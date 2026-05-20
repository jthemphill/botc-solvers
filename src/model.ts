import {
  Alignment,
  CharacterType,
  type RoleClaim,
  type RoleRef,
  roleAlignment,
  roleCharacterType,
  roleName,
} from "./core";
import { type Clause, type Literal, type SatBackend, combinations, negate } from "./sat";

export const DEFAULT_POISON_CONTEXT = "default";

function slug(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_+|_+$/g, "");
}

export class BoolVar {
  constructor(
    readonly id: number,
    readonly name: string,
  ) {}

  not(): Literal {
    return -this.id;
  }

  get lit(): Literal {
    return this.id;
  }
}

export type BoolLike = BoolVar | Literal;
export type RedHerrings = ReadonlyMap<string, BoolVar>;
export type DemonPredicate = (player: string, name: string) => BoolLike;

function lit(value: BoolLike): Literal {
  return typeof value === "number" ? value : value.lit;
}

function keyOf(items: readonly string[]): string {
  return items.join("\u0000");
}

export class World {
  constructor(
    readonly actual: ReadonlyMap<string, string>,
    readonly apparent: ReadonlyMap<string, string>,
    readonly poisoned: ReadonlySet<string>,
    readonly seating: readonly string[],
    readonly poisonedByContext: ReadonlyMap<string, ReadonlySet<string>> = new Map(),
  ) {}

  holder(role: RoleRef): string | undefined {
    const roleRef = roleName(role);
    const holders = [...this.actual.entries()]
      .filter(([, actualRole]) => actualRole === roleRef)
      .map(([player]) => player);
    return holders.length === 1 ? holders[0] : undefined;
  }

  actualRole(player: string): string {
    const actual = this.actual.get(player);
    if (actual === undefined) throw new KeyError(`Unknown player: ${player}`);
    return actual;
  }

  isPoisoned(player: string, context?: string): boolean {
    if (context === undefined) return this.poisoned.has(player);
    return this.poisonedByContext.get(context)?.has(player) ?? false;
  }
}

export class KeyError extends Error {}

export class BOTCModel {
  readonly players: string[];
  readonly seating: string[];
  readonly characters: ReadonlyMap<string, RoleRef>;
  readonly apparentRoles = new Map<string, string>();
  readonly poisonContexts = new Set<string>();

  private variableCount = 0;
  private counter = 0;
  private readonly clauses: Clause[] = [];
  private readonly actual = new Map<string, BoolVar>();
  private readonly poisonedVars = new Map<string, BoolVar>();
  private readonly poisonSourceContexts = new Set<string>();
  private readonly explicitPoisonedTrue = new Set<string>();
  private readonly defaultSoberConstraints = new Set<string>();
  private readonly predicateCache = new Map<string, BoolVar>();
  private readonly backend: SatBackend;

  constructor(
    players: readonly string[],
    options: {
      readonly characters: readonly RoleRef[];
      readonly seating?: readonly string[];
      readonly uniqueCharacters?: boolean;
      readonly backend: SatBackend;
    },
  ) {
    if (players.length === 0) throw new Error("At least one player is required.");
    this.players = [...players];
    if (new Set(this.players).size !== this.players.length) throw new Error("Player names must be unique.");
    this.seating = [...(options.seating ?? players)];
    if (this.seating.length !== this.players.length || this.seating.some((player) => !this.players.includes(player))) {
      throw new Error("Seating must contain exactly the model players.");
    }
    const chars = new Map<string, RoleRef>();
    for (const character of options.characters) chars.set(roleName(character), character);
    if (chars.size !== options.characters.length) throw new Error("Character names must be unique.");
    this.characters = chars;
    this.backend = options.backend;

    for (const player of this.players) {
      for (const role of this.characters.keys()) {
        this.actual.set(this.actualKey(player, role), this.newBool(`${slug(player)}__actual__${slug(role)}`));
      }
    }
    for (const player of this.players)
      this.addExactlyOne([...this.characters.keys()].map((role) => this.actualIs(player, role)));
    if (options.uniqueCharacters ?? true) {
      for (const role of this.characters.keys())
        this.addAtMostN(
          this.players.map((player) => this.actualIs(player, role)),
          1,
        );
    }
  }

  newBool(name: string): BoolVar {
    this.variableCount += 1;
    this.counter += 1;
    return new BoolVar(this.variableCount, `${slug(name)}__${this.counter}`);
  }

  constantBool(value: boolean, name: string): BoolVar {
    const result = this.newBool(name);
    this.addClause([value ? result.lit : result.not()]);
    return result;
  }

  actualIs(player: string, role: RoleRef): BoolVar {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    return this.actual.get(this.actualKey(player, roleRef)) as BoolVar;
  }

  poisoned(player: string, context?: string): BoolVar {
    this.checkPlayer(player);
    const poisonContext = this.poisonContext(context);
    const key = this.poisonKey(poisonContext, player);
    let result = this.poisonedVars.get(key);
    if (result === undefined) {
      result = this.newBool(`${slug(player)}__poisoned__${slug(poisonContext)}`);
      this.poisonedVars.set(key, result);
    }
    this.poisonContexts.add(poisonContext);
    return result;
  }

  poisonedLiterals(context: string): Array<[string, BoolVar]> {
    const poisonContext = this.poisonContext(context);
    return this.players.flatMap((player) => {
      const variable = this.poisonedVars.get(this.poisonKey(poisonContext, player));
      return variable === undefined ? [] : [[player, variable] as [string, BoolVar]];
    });
  }

  setApparentRole(player: string, role: RoleRef): void {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    this.apparentRoles.set(player, roleRef);
  }

  addRoleClaim(
    claim: RoleClaim,
    options: {
      readonly evilRoles?: readonly RoleRef[];
      readonly drunkRole?: RoleRef;
      readonly extraPossibleActualRoles?: readonly RoleRef[];
      readonly drunkThinksOutOfPlayRole?: boolean;
    } = {},
  ): void {
    const apparentRole = roleName(claim.apparentRole);
    this.setApparentRole(claim.player, apparentRole);
    const evilRoles =
      options.evilRoles ??
      [...this.characters.entries()]
        .filter(([, character]) => roleAlignment(character) === Alignment.Evil)
        .map(([role]) => role);
    const possibleRoles = [
      apparentRole,
      ...evilRoles.map(roleName),
      ...(options.extraPossibleActualRoles ?? []).map(roleName),
    ];
    const drunkRole = roleName(options.drunkRole ?? "Drunk");
    const claimedTownsfolk =
      roleCharacterType(this.characters.get(apparentRole) as RoleRef) === CharacterType.Townsfolk;
    if (claimedTownsfolk && this.characters.has(drunkRole)) possibleRoles.push(drunkRole);
    this.setPossibleActualRoles(claim.player, possibleRoles);
    if (claimedTownsfolk && this.characters.has(drunkRole) && (options.drunkThinksOutOfPlayRole ?? false))
      this.addDrunkThinksOutOfPlayRole(claim.player, apparentRole, drunkRole);
  }

  addClaim(
    player: string,
    apparentRole: RoleRef,
    possibleRoles: readonly RoleRef[],
    options: { readonly drunkRole?: RoleRef; readonly drunkThinksOutOfPlayRole?: boolean } = {},
  ): void {
    const apparentRoleRef = roleName(apparentRole);
    const drunkRole = options.drunkRole ?? "Drunk";
    this.setApparentRole(player, apparentRoleRef);
    this.setPossibleActualRoles(player, possibleRoles);
    if (options.drunkThinksOutOfPlayRole ?? possibleRoles.some((role) => roleName(role) === roleName(drunkRole)))
      this.addDrunkThinksOutOfPlayRole(player, apparentRoleRef, drunkRole);
  }

  setPossibleActualRoles(player: string, roles: readonly RoleRef[]): void {
    this.checkPlayer(player);
    const allowed = new Set(roles.map(roleName));
    for (const role of allowed) this.checkRole(role);
    for (const role of this.characters.keys()) if (!allowed.has(role)) this.addFalse(this.actualIs(player, role));
  }

  fixActual(player: string, role: RoleRef): void {
    this.addTruth(this.actualIs(player, role));
  }

  fixNotActual(player: string, role: RoleRef): void {
    this.addFalse(this.actualIs(player, role));
  }

  addDrunkThinksOutOfPlayRole(player: string, apparentRole: RoleRef, drunkRole: RoleRef): void {
    this.addImplication(this.actualIs(player, drunkRole), this.roleInPlay(apparentRole).not());
  }

  forceOutsiderCount(
    count: number,
    options: { readonly players?: readonly string[]; readonly name?: string } = {},
  ): void {
    this.addTruth(this.outsiderCountIs(count, options));
  }

  outsiderCountIs(
    count: number,
    options: { readonly players?: readonly string[]; readonly name?: string } = {},
  ): BoolVar {
    const players = options.players ?? this.players;
    return this.boolSumEquals(
      players.map((player) => this.hasCharacterType(player, CharacterType.Outsider)),
      count,
      options.name ?? `outsider_count_${count}`,
    );
  }

  addBaronOutsiderCounts(
    counts: { readonly withoutBaron: number; readonly withBaron: number },
    options: { readonly players?: readonly string[]; readonly baronRole?: RoleRef } = {},
  ): void {
    const baronRole = options.baronRole ?? "Baron";
    this.addImplication(this.roleInPlay(baronRole), this.outsiderCountIs(counts.withBaron, options));
    this.addImplication(this.roleInPlay(baronRole).not(), this.outsiderCountIs(counts.withoutBaron, options));
  }

  fixPoisoned(player: string, value: boolean, context?: string): void {
    const poisonContext = this.poisonContext(context);
    this.addClause([value ? this.poisoned(player, poisonContext).lit : this.poisoned(player, poisonContext).not()]);
    if (value) this.explicitPoisonedTrue.add(this.poisonKey(poisonContext, player));
  }

  addPoisonerEffect(
    context: string,
    options: { readonly poisonerRole?: RoleRef; readonly activeIf?: BoolLike | boolean } = {},
  ): void {
    const poisonContext = this.poisonContext(context);
    this.poisonSourceContexts.add(poisonContext);
    const poisoned = this.players.map((player) => this.poisoned(player, poisonContext));
    const poisonerRole = options.poisonerRole ?? "Poisoner";
    const poisonerInPlay = this.roleInPlay(poisonerRole);
    let poisonerActive: BoolVar;
    if (options.activeIf === undefined) {
      poisonerActive = poisonerInPlay;
    } else if (typeof options.activeIf === "boolean") {
      poisonerActive = this.allOf(
        [poisonerInPlay, this.constantBool(options.activeIf, `${poisonContext}_${roleName(poisonerRole)}_active_if`)],
        `${poisonContext}_${roleName(poisonerRole)}_active`,
      );
    } else {
      poisonerActive = this.allOf(
        [poisonerInPlay, options.activeIf],
        `${poisonContext}_${roleName(poisonerRole)}_active`,
      );
    }
    this.addEnforcedExactlyN(poisoned, 1, poisonerActive);
    this.addEnforcedExactlyN(poisoned, 0, poisonerActive.not());
  }

  allowPoisonInContext(context?: string): void {
    const poisonContext = this.poisonContext(context);
    this.poisonSourceContexts.add(poisonContext);
    this.poisonContexts.add(poisonContext);
  }

  setCharacterCount(role: RoleRef, count: number): void {
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    this.addExactlyN(
      this.players.map((player) => this.actualIs(player, roleRef)),
      count,
    );
  }

  addTruth(value: BoolLike): void {
    this.addClause([lit(value)]);
  }

  addFalse(value: BoolLike): void {
    this.addClause([negate(lit(value))]);
  }

  addImplication(condition: BoolLike, conclusion: BoolLike): void {
    this.addClause([negate(lit(condition)), lit(conclusion)]);
  }

  addExactlyOne(values: readonly BoolLike[]): void {
    this.addExactlyN(values, 1);
  }

  addExactlyN(values: readonly BoolLike[], count: number): void {
    this.addAtMostN(values, count);
    this.addAtLeastN(values, count);
  }

  addEnforcedExactlyN(values: readonly BoolLike[], count: number, condition: BoolLike): void {
    for (const clause of this.exactlyNClauses(values.map(lit), count))
      this.addClause([negate(lit(condition)), ...clause]);
  }

  addEnforcedAtLeastN(values: readonly BoolLike[], count: number, condition: BoolLike): void {
    for (const clause of this.atLeastNClauses(values.map(lit), count))
      this.addClause([negate(lit(condition)), ...clause]);
  }

  addEnforcedAtMostN(values: readonly BoolLike[], count: number, condition: BoolLike): void {
    for (const clause of this.atMostNClauses(values.map(lit), count))
      this.addClause([negate(lit(condition)), ...clause]);
  }

  boolSumEquals(values: readonly BoolLike[], count: number, name: string): BoolVar {
    const literals = values.map(lit);
    const result = this.newBool(name);
    this.reifyExactCount(literals, count, result);
    return result;
  }

  allOf(values: readonly BoolLike[], name: string): BoolVar {
    const literals = values.map(lit);
    if (literals.length === 0) return this.constantBool(true, name);
    const result = this.newBool(name);
    for (const literal of literals) this.addClause([result.not(), literal]);
    this.addClause([result.lit, ...literals.map(negate)]);
    return result;
  }

  anyOf(values: readonly BoolLike[], name: string): BoolVar {
    const literals = values.map(lit);
    if (literals.length === 0) return this.constantBool(false, name);
    const result = this.newBool(name);
    this.addClause([result.not(), ...literals]);
    for (const literal of literals) this.addClause([result.lit, negate(literal)]);
    return result;
  }

  not(value: BoolLike, name: string): BoolVar {
    const result = this.newBool(name);
    this.addClause([result.not(), negate(lit(value))]);
    this.addClause([result.lit, lit(value)]);
    return result;
  }

  xor(left: BoolLike, right: BoolLike, name: string): BoolVar {
    return this.boolSumEquals([left, right], 1, name);
  }

  isEvil(player: string): BoolVar {
    return this.cachedPlayerPredicate(
      "is_evil",
      player,
      [...this.characters.entries()]
        .filter(([, character]) => roleAlignment(character) === Alignment.Evil)
        .map(([role]) => this.actualIs(player, role)),
    );
  }

  isGood(player: string): BoolVar {
    return this.cachedPlayerPredicate(
      "is_good",
      player,
      [...this.characters.entries()]
        .filter(([, character]) => roleAlignment(character) === Alignment.Good)
        .map(([role]) => this.actualIs(player, role)),
    );
  }

  isTownsfolk(player: string): BoolVar {
    return this.hasCharacterType(player, CharacterType.Townsfolk);
  }

  hasCharacterType(player: string, characterType: CharacterType): BoolVar {
    return this.cachedPlayerPredicate(
      `is_${characterType}`,
      player,
      [...this.characters.entries()]
        .filter(([, character]) => roleCharacterType(character) === characterType)
        .map(([role]) => this.actualIs(player, role)),
    );
  }

  isDemon(player: string): BoolVar {
    return this.hasCharacterType(player, CharacterType.Demon);
  }

  isMinion(player: string): BoolVar {
    return this.hasCharacterType(player, CharacterType.Minion);
  }

  roleInPlay(role: RoleRef): BoolVar {
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const key = keyOf(["role_in_play", roleRef]);
    let cached = this.predicateCache.get(key);
    if (cached === undefined) {
      cached = this.anyOf(
        this.players.map((player) => this.actualIs(player, roleRef)),
        `${roleRef}_in_play`,
      );
      this.predicateCache.set(key, cached);
    }
    return cached;
  }

  registersAsEvil(player: string, name: string): BoolVar {
    return this.registersAsAlignment(player, Alignment.Evil, name);
  }

  registersAsGood(player: string, name: string): BoolVar {
    return this.registersAsAlignment(player, Alignment.Good, name);
  }

  registersAsCharacterType(player: string, characterType: CharacterType, name: string): BoolVar {
    this.checkPlayer(player);
    const result = this.newBool(`${name}_${player}_registers_as_${characterType}`);
    for (const [role, character] of this.characters.entries()) {
      const actual = this.actualIs(player, role);
      if (this.roleCanFlexiblyRegisterAsType(role, characterType)) continue;
      this.addImplication(actual, roleCharacterType(character) === characterType ? result : result.not());
    }
    return result;
  }

  registersAsRole(player: string, role: RoleRef, name: string): BoolVar {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const result = this.newBool(`${name}_${player}_registers_as_${roleRef}`);
    for (const actualRole of this.characters.keys()) {
      const actual = this.actualIs(player, actualRole);
      if (this.roleCanFlexiblyRegisterAsRole(actualRole, roleRef)) continue;
      this.addImplication(actual, actualRole === roleRef ? result : result.not());
    }
    return result;
  }

  registeredEvilCount(players: readonly string[], count: number, name: string): BoolVar {
    return this.boolSumEquals(
      players.map((player) => this.registersAsEvil(player, `${name}_${player}`)),
      count,
      name,
    );
  }

  addFortuneTellerRedHerring(
    fortuneTeller: string,
    options: { readonly players?: readonly string[]; readonly fortuneTellerRole?: RoleRef } = {},
  ): RedHerrings {
    const players = options.players ?? this.players;
    const fortuneTellerRole = options.fortuneTellerRole ?? "Fortune Teller";
    const entries = players.map((player) => [player, this.newBool(`${player}_fortune_teller_red_herring`)] as const);
    const redHerrings = new Map(entries);
    this.addEnforcedExactlyN(
      entries.map(([, variable]) => variable),
      1,
      this.actualIs(fortuneTeller, fortuneTellerRole),
    );
    for (const [player, redHerring] of entries) this.addImplication(redHerring, this.isGood(player));
    return redHerrings;
  }

  fortuneTellerYes(
    redHerrings: RedHerrings,
    players: readonly [string, string],
    name: string,
    isDemon: DemonPredicate = (player, predicateName) => this.registersAsRole(player, "Imp", predicateName),
  ): BoolVar {
    const checkedRedHerrings = players.map((player) => {
      const redHerring = redHerrings.get(player);
      if (redHerring === undefined) throw new KeyError(`No Fortune Teller red herring variable for ${player}.`);
      return redHerring;
    });
    return this.anyOf([...players.map((player) => isDemon(player, `${name}_${player}`)), ...checkedRedHerrings], name);
  }

  fortuneTellerNo(
    redHerrings: RedHerrings,
    players: readonly [string, string],
    name: string,
    isDemon?: DemonPredicate,
  ): BoolVar {
    return this.not(this.fortuneTellerYes(redHerrings, players, `${name}_yes`, isDemon), name);
  }

  addTruthfulInfoClaim(
    player: string,
    apparentRole: RoleRef,
    claimTruth: BoolLike,
    options: { readonly poisonContext?: string } = {},
  ): void {
    const apparentRoleRef = roleName(apparentRole);
    const activeClaimedRole = this.allOf(
      [this.actualIs(player, apparentRoleRef), this.poisoned(player, options.poisonContext).not()],
      `${player}_${apparentRoleRef}_sober_healthy_claim`,
    );
    this.addImplication(activeClaimedRole, claimTruth);
  }

  addNoDashiiInfoClaim(
    player: string,
    role: RoleRef,
    reportedInfo: BoolLike,
    name: string,
    options: { readonly seating?: readonly string[]; readonly noDashiiRole?: RoleRef } = {},
  ): BoolVar {
    const active = this.actualIs(player, role);
    const poisoned = this.noDashiiPoisoned(player, options);
    this.addImplication(this.allOf([active, poisoned.not()], `${player}_${name}_sober_info`), reportedInfo);
    return this.allOf(
      [active, poisoned, this.not(reportedInfo, `${player}_${name}_false_info`)],
      `${player}_${name}_malfunction`,
    );
  }

  noDashiiPoisoned(
    player: string,
    options: { readonly seating?: readonly string[]; readonly noDashiiRole?: RoleRef } = {},
  ): BoolVar {
    const seating = options.seating ?? this.seating;
    const noDashiiRole = options.noDashiiRole ?? "No Dashii";
    this.checkPlayer(player);
    if (!seating.includes(player)) throw new KeyError(`Player is not seated: ${player}`);
    for (const seated of seating) this.checkPlayer(seated);
    return this.anyOf(
      seating.flatMap((demon) => [
        this.closestTownfolkInDirectionIs(seating, demon, player, 1, noDashiiRole),
        this.closestTownfolkInDirectionIs(seating, demon, player, -1, noDashiiRole),
      ]),
      `${player}_poisoned_by_no_dashii`,
    );
  }

  neighbors(player: string): [string, string] {
    this.checkPlayer(player);
    const index = this.seating.indexOf(player);
    return [
      this.seating[(index - 1 + this.seating.length) % this.seating.length] as string,
      this.seating[(index + 1) % this.seating.length] as string,
    ];
  }

  adjacentPairs(): Array<[string, string]> {
    return this.seating.map((player, index) => [player, this.seating[(index + 1) % this.seating.length] as string]);
  }

  sitsNextToEvil(player: string): BoolVar {
    const [left, right] = this.neighbors(player);
    return this.anyOf([this.isEvil(left), this.isEvil(right)], `${player}_sits_next_to_evil`);
  }

  async solveAll(options: { readonly limit?: number } = {}): Promise<World[]> {
    this.applyDefaultSoberConstraints();
    const worlds: World[] = [];
    const seen = new Set<string>();
    const workingClauses = [...this.clauses];
    while (options.limit === undefined || worlds.length < options.limit) {
      const result = await this.backend.solve({ variableCount: this.variableCount, clauses: workingClauses });
      if (!result.sat || result.model === undefined) break;
      const model = result.model;
      const actual = new Map<string, string>();
      for (const player of this.players) {
        const matching = [...this.characters.keys()].filter((role) => model.has(this.actualIs(player, role).id));
        if (matching.length !== 1) throw new Error(`Expected exactly one actual character for ${player}.`);
        actual.set(player, matching[0] as string);
      }
      const poisonedByContext = new Map<string, ReadonlySet<string>>();
      for (const context of [...this.poisonContexts].sort()) {
        poisonedByContext.set(
          context,
          new Set(
            this.poisonedLiterals(context)
              .filter(([, variable]) => model.has(variable.id))
              .map(([player]) => player),
          ),
        );
      }
      const poisoned = poisonedByContext.get(DEFAULT_POISON_CONTEXT) ?? new Set<string>();
      const key = JSON.stringify({
        actual: [...actual.entries()].sort(),
        apparent: [...this.apparentRoles.entries()].sort(),
        poisoned: [...poisonedByContext.entries()].map(([context, players]) => [context, [...players].sort()]),
        seating: this.seating,
      });
      if (!seen.has(key)) {
        seen.add(key);
        worlds.push(new World(actual, new Map(this.apparentRoles), poisoned, [...this.seating], poisonedByContext));
      }
      const significant = [
        ...this.players.flatMap((player) => [...this.characters.keys()].map((role) => this.actualIs(player, role).id)),
        ...[...this.poisonedVars.values()].map((variable) => variable.id),
      ];
      workingClauses.push(significant.map((variable) => (model.has(variable) ? -variable : variable)));
    }
    return worlds;
  }

  private checkPlayer(player: string): void {
    if (!this.players.includes(player)) throw new KeyError(`Unknown player: ${player}`);
  }

  private checkRole(role: string): void {
    if (!this.characters.has(role)) throw new KeyError(`Unknown character: ${role}`);
  }

  private actualKey(player: string, role: string): string {
    return keyOf([player, role]);
  }

  private poisonKey(context: string, player: string): string {
    return keyOf([context, player]);
  }

  private poisonContext(context?: string): string {
    if (context === undefined) return DEFAULT_POISON_CONTEXT;
    if (context.length === 0) throw new Error("Poison context must not be empty.");
    return context;
  }

  private addClause(clause: readonly Literal[]): void {
    this.clauses.push([...clause]);
  }

  private addAtMostN(values: readonly BoolLike[], count: number): void {
    for (const clause of this.atMostNClauses(values.map(lit), count)) this.addClause(clause);
  }

  private addAtLeastN(values: readonly BoolLike[], count: number): void {
    for (const clause of this.atLeastNClauses(values.map(lit), count)) this.addClause(clause);
  }

  private atMostNClauses(literals: readonly Literal[], count: number): Clause[] {
    if (count < 0) return [[]];
    if (count >= literals.length) return [];
    return combinations(literals, count + 1).map((combo) => combo.map(negate));
  }

  private atLeastNClauses(literals: readonly Literal[], count: number): Clause[] {
    if (count <= 0) return [];
    if (count > literals.length) return [[]];
    return combinations(literals, literals.length - count + 1).map((combo) => [...combo]);
  }

  private exactlyNClauses(literals: readonly Literal[], count: number): Clause[] {
    return [...this.atMostNClauses(literals, count), ...this.atLeastNClauses(literals, count)];
  }

  private reifyExactCount(literals: readonly Literal[], count: number, result: BoolVar): void {
    const assignments = 1 << literals.length;
    for (let mask = 0; mask < assignments; mask += 1) {
      const clause: Literal[] = [];
      let trueCount = 0;
      for (let index = 0; index < literals.length; index += 1) {
        const literal = literals[index] as Literal;
        const isTrue = (mask & (1 << index)) !== 0;
        if (isTrue) trueCount += 1;
        clause.push(isTrue ? negate(literal) : literal);
      }
      clause.push(trueCount === count ? result.lit : result.not());
      this.addClause(clause);
    }
  }

  private cachedPlayerPredicate(predicate: string, player: string, values: readonly BoolLike[]): BoolVar {
    this.checkPlayer(player);
    const key = keyOf([predicate, player]);
    let cached = this.predicateCache.get(key);
    if (cached === undefined) {
      cached = this.boolSumEquals(values, 1, `${predicate}_${player}`);
      this.predicateCache.set(key, cached);
    }
    return cached;
  }

  private registersAsAlignment(player: string, alignment: Alignment, name: string): BoolVar {
    this.checkPlayer(player);
    const result = this.newBool(`${name}_${player}_registers_as_${alignment}`);
    for (const [role, character] of this.characters.entries()) {
      const actual = this.actualIs(player, role);
      if (this.roleCanFlexiblyRegisterAsAlignment(role)) continue;
      this.addImplication(actual, roleAlignment(character) === alignment ? result : result.not());
    }
    return result;
  }

  private roleCanFlexiblyRegisterAsAlignment(actualRole: string): boolean {
    return (actualRole === "Spy" || actualRole === "Recluse") && this.characters.has(actualRole);
  }

  private roleCanFlexiblyRegisterAsType(actualRole: string, characterType: CharacterType): boolean {
    if (actualRole === "Spy" && this.characters.has(actualRole))
      return [CharacterType.Minion, CharacterType.Outsider, CharacterType.Townsfolk].includes(characterType);
    if (actualRole === "Recluse" && this.characters.has(actualRole))
      return [CharacterType.Demon, CharacterType.Minion, CharacterType.Outsider].includes(characterType);
    return false;
  }

  private roleCanFlexiblyRegisterAsRole(actualRole: string, observedRole: string): boolean {
    const observedCharacter = this.characters.get(observedRole) as RoleRef;
    if (actualRole === "Spy" && this.characters.has(actualRole)) {
      return (
        observedRole === "Spy" ||
        (roleAlignment(observedCharacter) === Alignment.Good &&
          [CharacterType.Outsider, CharacterType.Townsfolk].includes(roleCharacterType(observedCharacter)))
      );
    }
    if (actualRole === "Recluse" && this.characters.has(actualRole)) {
      return (
        observedRole === "Recluse" ||
        (roleAlignment(observedCharacter) === Alignment.Evil &&
          [CharacterType.Demon, CharacterType.Minion].includes(roleCharacterType(observedCharacter)))
      );
    }
    return false;
  }

  private closestTownfolkInDirectionIs(
    seating: readonly string[],
    demon: string,
    target: string,
    direction: 1 | -1,
    noDashiiRole: RoleRef,
  ): BoolVar {
    const demonIndex = seating.indexOf(demon);
    const targetIndex = seating.indexOf(target);
    const distance =
      (direction === 1 ? targetIndex - demonIndex : demonIndex - targetIndex + seating.length) % seating.length;
    if (distance <= 0) return this.constantBool(false, `${demon}_${target}_not_in_direction_${direction}`);
    const between = Array.from({ length: distance - 1 }, (_ignored, offset) => {
      const index = (demonIndex + direction * (offset + 1) + seating.length) % seating.length;
      return seating[index] as string;
    });
    return this.allOf(
      [
        this.actualIs(demon, noDashiiRole),
        this.hasCharacterType(target, CharacterType.Townsfolk),
        ...between.map((betweenPlayer) => this.hasCharacterType(betweenPlayer, CharacterType.Townsfolk).not()),
      ],
      `${target}_closest_townsfolk_${direction}_of_${demon}`,
    );
  }

  private applyDefaultSoberConstraints(): void {
    for (const [key, poisoned] of this.poisonedVars.entries()) {
      const [context] = key.split("\u0000");
      if (
        context === undefined ||
        this.poisonSourceContexts.has(context) ||
        this.explicitPoisonedTrue.has(key) ||
        this.defaultSoberConstraints.has(key)
      )
        continue;
      this.addFalse(poisoned);
      this.defaultSoberConstraints.add(key);
    }
  }
}

export function forcedRoleHolders(
  worlds: readonly World[],
  roles: readonly RoleRef[],
): Record<string, string | undefined> {
  const summary: Record<string, string | undefined> = {};
  for (const role of roles) {
    const roleRef = roleName(role);
    const holders = new Set(worlds.map((world) => world.holder(roleRef)));
    summary[roleRef] = holders.size === 1 ? [...holders][0] : undefined;
  }
  return summary;
}
