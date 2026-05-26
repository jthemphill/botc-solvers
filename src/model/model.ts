import {
  Alignment,
  CharacterType,
  type RoleClaim,
  type RoleRef,
  roleAlignment,
  roleCharacterType,
  roleMaxCopies,
  roleName,
} from "./core";
import { type Clause, type Literal, type SatBackend, combinations, negate } from "./sat";

export type Timing = `night_${number}` | `day_${number}`;

const DEFAULT_TIMING_KEY = "default";

export function night(number: number): Timing {
  if (!Number.isInteger(number) || number <= 0) throw new Error(`Night must be a positive integer: ${number}.`);
  return `night_${number}`;
}

export function day(number: number): Timing {
  if (!Number.isInteger(number) || number <= 0) throw new Error(`Day must be a positive integer: ${number}.`);
  return `day_${number}`;
}

export interface TimingQuery {
  readonly timing?: Timing;
}

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

export interface InfoClaimConstraint {
  readonly player: string;
  readonly role: RoleRef;
  readonly learned: BoolLike;
  readonly timing: Timing;
  readonly vortoxAffected?: boolean;
}

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
    readonly players: readonly string[],
    readonly poisonedByTiming: ReadonlyMap<string, ReadonlySet<string>> = new Map(),
    readonly drunk: ReadonlySet<string> = new Set(),
    readonly drunkByTiming: ReadonlyMap<string, ReadonlySet<string>> = new Map(),
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

  isPoisoned(player: string, timing?: Timing): boolean {
    if (timing === undefined) return this.poisoned.has(player);
    return this.poisonedByTiming.get(timing)?.has(player) ?? false;
  }

  isDrunk(player: string, timing?: Timing): boolean {
    if (this.drunk.has(player)) return true;
    if (timing === undefined) return false;
    return this.drunkByTiming.get(timing)?.has(player) ?? false;
  }
}

export class KeyError extends Error {}

export class BOTCModel {
  readonly players: string[];
  readonly characters: ReadonlyMap<string, RoleRef>;
  readonly uniqueCharacters: boolean;
  readonly apparentRoles = new Map<string, string>();
  readonly poisonTimingKeys = new Set<string>();

  private variableCount = 0;
  private counter = 0;
  private readonly clauses: Clause[] = [];
  private readonly actual = new Map<string, BoolVar>();
  private readonly poisonedVars = new Map<string, BoolVar>();
  private readonly drunkVars = new Map<string, BoolVar>();
  private readonly globalDrunkVars = new Map<string, BoolVar>();
  private readonly roleAtVars = new Map<string, BoolVar>();
  private readonly roleAtSources = new Map<string, BoolLike[]>();
  private readonly roleAtRemovals = new Map<string, BoolLike[]>();
  private readonly defaultRoleAtConstraints = new Set<string>();
  private readonly poisonSourceTimingKeys = new Set<string>();
  private readonly drunkSourceTimingKeys = new Set<string>();
  private readonly explicitPoisonedTrue = new Set<string>();
  private readonly explicitDrunkTrue = new Set<string>();
  private hasGlobalDrunkSource = false;
  private readonly defaultSoberConstraints = new Set<string>();
  private readonly predicateCache = new Map<string, BoolVar>();
  private readonly infoMalfunctionsByTiming = new Map<string, BoolVar[]>();
  private readonly backend: SatBackend;

  constructor(
    players: readonly string[],
    options: {
      readonly characters: readonly RoleRef[];
      readonly uniqueCharacters?: boolean;
      readonly backend: SatBackend;
    },
  ) {
    if (players.length === 0) throw new Error("At least one player is required.");
    this.players = [...players];
    if (new Set(this.players).size !== this.players.length) throw new Error("Player names must be unique.");
    const chars = new Map<string, RoleRef>();
    for (const character of options.characters) chars.set(roleName(character), character);
    if (chars.size !== options.characters.length) throw new Error("Character names must be unique.");
    this.characters = chars;
    this.uniqueCharacters = options.uniqueCharacters ?? true;
    this.backend = options.backend;

    for (const player of this.players) {
      for (const role of this.characters.keys()) {
        this.actual.set(this.actualKey(player, role), this.newBool(`${slug(player)}__actual__${slug(role)}`));
      }
    }
    for (const player of this.players)
      this.addExactlyOne([...this.characters.keys()].map((role) => this.actualIs(player, role)));
    if (this.uniqueCharacters) {
      for (const role of this.characters.keys())
        this.addAtMostN(
          this.players.map((player) => this.actualIs(player, role)),
          roleMaxCopies(this.characters.get(role) as RoleRef),
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

  poisoned(player: string, timing?: Timing): BoolVar {
    this.checkPlayer(player);
    const poisonTiming = timing ?? DEFAULT_TIMING_KEY;
    const key = this.timingPlayerKey(poisonTiming, player);
    let result = this.poisonedVars.get(key);
    if (result === undefined) {
      result = this.newBool(`${slug(player)}__poisoned__${slug(poisonTiming)}`);
      this.poisonedVars.set(key, result);
    }
    this.poisonTimingKeys.add(poisonTiming);
    return result;
  }

  poisonedLiterals(timing: Timing): Array<[string, BoolVar]> {
    return this.poisonedLiteralsForKey(timing);
  }

  private poisonedLiteralsForKey(timing: string): Array<[string, BoolVar]> {
    return this.players.flatMap((player) => {
      const variable = this.poisonedVars.get(this.timingPlayerKey(timing, player));
      return variable === undefined ? [] : [[player, variable] as [string, BoolVar]];
    });
  }

  drunk(player: string, timing?: Timing): BoolVar {
    this.checkPlayer(player);
    const drunkTiming = timing ?? DEFAULT_TIMING_KEY;
    const key = this.timingPlayerKey(drunkTiming, player);
    let result = this.drunkVars.get(key);
    if (result === undefined) {
      result = this.newBool(`${slug(player)}__drunk__${slug(drunkTiming)}`);
      this.drunkVars.set(key, result);
    }
    return result;
  }

  globalDrunk(player: string): BoolVar {
    this.checkPlayer(player);
    let result = this.globalDrunkVars.get(player);
    if (result === undefined) {
      result = this.newBool(`${slug(player)}__globally_drunk`);
      this.globalDrunkVars.set(player, result);
    }
    return result;
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
    if (claimedTownsfolk && this.characters.has(drunkRole))
      this.addDrunkThinksOutOfPlayRole(claim.player, apparentRole, drunkRole);
  }

  addClaim(
    player: string,
    apparentRole: RoleRef,
    possibleRoles: readonly RoleRef[],
    options: { readonly drunkRole?: RoleRef } = {},
  ): void {
    const apparentRoleRef = roleName(apparentRole);
    const drunkRole = options.drunkRole ?? "Drunk";
    this.setApparentRole(player, apparentRoleRef);
    this.setPossibleActualRoles(player, possibleRoles);
    if (possibleRoles.some((role) => roleName(role) === roleName(drunkRole)))
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
    if (!this.uniqueCharacters) return;
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

  fixPoisoned(player: string, value: boolean, timing?: Timing): void {
    const poisonTiming = timing ?? DEFAULT_TIMING_KEY;
    this.addClause([value ? this.poisoned(player, timing).lit : this.poisoned(player, timing).not()]);
    if (value) this.explicitPoisonedTrue.add(this.timingPlayerKey(poisonTiming, player));
  }

  fixDrunk(player: string, value: boolean, timing?: Timing): void {
    const drunkTiming = timing ?? DEFAULT_TIMING_KEY;
    this.addClause([value ? this.drunk(player, timing).lit : this.drunk(player, timing).not()]);
    if (value) this.explicitDrunkTrue.add(this.timingPlayerKey(drunkTiming, player));
  }

  addPuzzlemasterDrunking(options: { readonly excludedPlayers?: readonly string[] } = {}): void {
    this.hasGlobalDrunkSource = true;
    const excluded = new Set(options.excludedPlayers ?? []);
    const candidates = this.players.filter((player) => !excluded.has(player));
    this.addExactlyN(
      candidates.map((player) => this.globalDrunk(player)),
      1,
    );
    for (const player of this.players) if (excluded.has(player)) this.addFalse(this.globalDrunk(player));
  }

  addPoisonerEffect(
    timing: Timing,
    options: { readonly poisonerRole?: RoleRef; readonly activeIf?: BoolLike | boolean } = {},
  ): void {
    const poisonTiming = timing;
    this.poisonSourceTimingKeys.add(poisonTiming);
    const poisoned = this.players.map((player) => this.poisoned(player, timing));
    const poisonerRole = options.poisonerRole ?? "Poisoner";
    const poisonerInPlay = this.roleInPlay(poisonerRole);
    let poisonerActive: BoolVar;
    if (options.activeIf === undefined) {
      poisonerActive = poisonerInPlay;
    } else if (typeof options.activeIf === "boolean") {
      poisonerActive = this.allOf(
        [poisonerInPlay, this.constantBool(options.activeIf, `${poisonTiming}_${roleName(poisonerRole)}_active_if`)],
        `${poisonTiming}_${roleName(poisonerRole)}_active`,
      );
    } else {
      poisonerActive = this.allOf(
        [poisonerInPlay, options.activeIf],
        `${poisonTiming}_${roleName(poisonerRole)}_active`,
      );
    }
    this.addEnforcedExactlyN(poisoned, 1, poisonerActive);
    this.addEnforcedExactlyN(poisoned, 0, poisonerActive.not());
  }

  allowPoisonAt(timing?: Timing): void {
    const poisonTiming = timing ?? DEFAULT_TIMING_KEY;
    this.poisonSourceTimingKeys.add(poisonTiming);
    this.poisonTimingKeys.add(poisonTiming);
  }

  allowDrunkAt(timing?: Timing): void {
    const drunkTiming = timing ?? DEFAULT_TIMING_KEY;
    this.drunkSourceTimingKeys.add(drunkTiming);
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

  hasRoleAt(player: string, role: RoleRef, timing?: Timing): BoolVar {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const roleTiming = timing ?? DEFAULT_TIMING_KEY;
    if (roleTiming === DEFAULT_TIMING_KEY) return this.actualIs(player, roleRef);
    const key = this.roleAtKey(roleTiming, player, roleRef);
    let result = this.roleAtVars.get(key);
    if (result === undefined) {
      result = this.newBool(`${player}_${roleRef}_${roleTiming}`);
      this.roleAtVars.set(key, result);
    }
    return result;
  }

  addRoleAt(player: string, role: RoleRef, timing: Timing, value: BoolLike | boolean = true): BoolVar {
    const roleRef = roleName(role);
    const roleAt = this.hasRoleAt(player, roleRef, timing);
    const key = this.roleAtKey(timing, player, roleRef);
    if (typeof value === "boolean") {
      if (!value) return this.removeRoleAt(player, roleRef, timing);
      this.addTruth(roleAt);
      const sources = this.roleAtSources.get(key) ?? [];
      sources.push(this.constantBool(true, `${player}_${roleRef}_${timing}_role_at_source`));
      this.roleAtSources.set(key, sources);
    } else {
      this.addImplication(value, roleAt);
      const sources = this.roleAtSources.get(key) ?? [];
      sources.push(value);
      this.roleAtSources.set(key, sources);
    }
    return roleAt;
  }

  removeRoleAt(player: string, role: RoleRef, timing: Timing, value: BoolLike | boolean = true): BoolVar {
    const roleRef = roleName(role);
    const roleAt = this.hasRoleAt(player, roleRef, timing);
    const key = this.roleAtKey(timing, player, roleRef);
    if (typeof value === "boolean") {
      if (!value) return roleAt;
      this.addFalse(roleAt);
      const removals = this.roleAtRemovals.get(key) ?? [];
      removals.push(this.constantBool(true, `${player}_${roleRef}_${timing}_role_at_removal`));
      this.roleAtRemovals.set(key, removals);
    } else {
      this.addImplication(value, roleAt.not());
      const removals = this.roleAtRemovals.get(key) ?? [];
      removals.push(value);
      this.roleAtRemovals.set(key, removals);
    }
    return roleAt;
  }

  isDemonAt(player: string, timing?: Timing): BoolVar {
    const demonRoles = [...this.characters.entries()]
      .filter(([, character]) => roleCharacterType(character) === CharacterType.Demon)
      .map(([role]) => role);
    return this.anyOf(
      demonRoles.map((role) => this.hasRoleAt(player, role, timing)),
      `${player}_demon_at_${timing ?? DEFAULT_TIMING_KEY}`,
    );
  }

  isPoisonedAt(player: string, timing: Timing): BoolVar {
    return this.poisoned(player, timing);
  }

  isDrunkAt(player: string, timing: Timing): BoolVar {
    return this.anyOf([this.drunk(player, timing), this.globalDrunk(player)], `${player}_drunk_at_${timing}`);
  }

  soberAndHealthy(player: string, timing: Timing): BoolVar {
    const timingName = timing;
    const unhealthy = this.anyOf(
      [this.isPoisonedAt(player, timing), this.isDrunkAt(player, timing), this.noDashiiPoisonedAt(player, timing)],
      `${player}_unhealthy_at_${timingName}`,
    );
    return this.not(unhealthy, `${player}_sober_healthy_at_${timingName}`);
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
    options: TimingQuery & { readonly vortoxAffected?: boolean } = {},
  ): void {
    this.addInfoClaim({
      player,
      role: apparentRole,
      learned: claimTruth,
      timing:
        options.timing ??
        (() => {
          throw new Error(`${player}'s ${roleName(apparentRole)} info claim needs explicit timing.`);
        })(),
      vortoxAffected: options.vortoxAffected,
    });
  }

  addInfoClaim(claim: InfoClaimConstraint): void {
    const roleRef = roleName(claim.role);
    const claimTiming = claim.timing;
    const claimTimingName = claimTiming;
    const activeRole = this.hasRoleAt(claim.player, roleRef, claimTiming);
    const healthy = this.soberAndHealthy(claim.player, claimTiming);
    const activeHealthy = this.allOf(
      [activeRole, healthy],
      `${claim.player}_${roleRef}_${claimTimingName}_sober_healthy_claim`,
    );
    this.recordInfoMalfunctions(claim.player, roleRef, claimTiming, activeRole, claim.vortoxAffected ?? false);

    if (!(claim.vortoxAffected ?? false) || !this.characters.has(roleName("Vortox"))) {
      this.addImplication(activeHealthy, claim.learned);
      return;
    }

    this.addImplication(
      this.allOf(
        [activeHealthy, this.roleInPlay("Vortox").not()],
        `${claim.player}_${roleRef}_${claimTimingName}_normal`,
      ),
      claim.learned,
    );
    this.addImplication(
      this.allOf([activeHealthy, this.roleInPlay("Vortox")], `${claim.player}_${roleRef}_${claimTimingName}_vortox`),
      this.not(claim.learned, `${claim.player}_${roleRef}_${claimTimingName}_vortox_false`),
    );
  }

  addNoDashiiInfoClaim(
    player: string,
    role: RoleRef,
    reportedInfo: BoolLike,
    name: string,
    options: {
      readonly noDashiiRole?: RoleRef;
      readonly timing?: Timing;
    } = {},
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
    options: {
      readonly noDashiiRole?: RoleRef;
      readonly timing?: Timing;
    } = {},
  ): BoolVar {
    const timing = options.timing ?? night(1);
    return this.noDashiiPoisonedAt(player, timing, options);
  }

  noDashiiPoisonedAt(player: string, timing: Timing, options: { readonly noDashiiRole?: RoleRef } = {}): BoolVar {
    const timingName = timing;
    const players = this.players;
    const noDashiiRole = options.noDashiiRole ?? "No Dashii";
    this.checkPlayer(player);
    if (!this.characters.has(roleName(noDashiiRole)))
      return this.constantBool(false, `${player}_no_no_dashii_${timingName}`);
    return this.anyOf(
      players.flatMap((demon) => [
        this.closestTownfolkInDirectionIs(players, demon, player, 1, noDashiiRole, timing),
        this.closestTownfolkInDirectionIs(players, demon, player, -1, noDashiiRole, timing),
      ]),
      `${player}_poisoned_by_no_dashii_${timingName}`,
    );
  }

  infoMalfunctions(timing: Timing): readonly BoolVar[] {
    return this.infoMalfunctionsByTiming.get(timing) ?? [];
  }

  malfunctionCountAt(timing: Timing, count: number, name: string): BoolVar {
    return this.boolSumEquals(this.infoMalfunctions(timing), count, name);
  }

  neighbors(player: string): [string, string] {
    this.checkPlayer(player);
    const index = this.players.indexOf(player);
    return [
      this.players[(index + 1) % this.players.length] as string,
      this.players[(index - 1 + this.players.length) % this.players.length] as string,
    ];
  }

  adjacentPairs(): Array<[string, string]> {
    return this.players.map((player, index) => [player, this.players[(index + 1) % this.players.length] as string]);
  }

  sitsNextToEvil(player: string): BoolVar {
    const [left, right] = this.neighbors(player);
    return this.anyOf([this.isEvil(left), this.isEvil(right)], `${player}_sits_next_to_evil`);
  }

  async solveAll(options: { readonly limit?: number } = {}): Promise<World[]> {
    this.applyDefaultTimingRoleConstraints();
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
      const poisonedByTiming = new Map<string, ReadonlySet<string>>();
      for (const timing of [...this.poisonTimingKeys].sort()) {
        poisonedByTiming.set(
          timing,
          new Set(
            this.poisonedLiteralsForKey(timing)
              .filter(([, variable]) => model.has(variable.id))
              .map(([player]) => player),
          ),
        );
      }
      const poisoned = poisonedByTiming.get(DEFAULT_TIMING_KEY) ?? new Set<string>();
      const drunkByTiming = new Map<string, ReadonlySet<string>>();
      const drunkTimings = new Set([...this.drunkVars.keys()].map((key) => key.split("\u0000")[0] as string));
      for (const timing of [...drunkTimings].sort()) {
        drunkByTiming.set(
          timing,
          new Set(
            this.players.filter((player) => {
              const variable = this.drunkVars.get(this.timingPlayerKey(timing, player));
              return variable !== undefined && model.has(variable.id);
            }),
          ),
        );
      }
      const globallyDrunk = new Set(
        [...this.globalDrunkVars.entries()].filter(([, variable]) => model.has(variable.id)).map(([player]) => player),
      );
      const key = JSON.stringify({
        actual: [...actual.entries()].sort(),
        apparent: [...this.apparentRoles.entries()].sort(),
        poisoned: [...poisonedByTiming.entries()].map(([timing, players]) => [timing, [...players].sort()]),
        drunk: [...globallyDrunk].sort(),
        drunkByTiming: [...drunkByTiming.entries()].map(([timing, players]) => [timing, [...players].sort()]),
        players: this.players,
      });
      if (!seen.has(key)) {
        seen.add(key);
        worlds.push(
          new World(
            actual,
            new Map(this.apparentRoles),
            poisoned,
            [...this.players],
            poisonedByTiming,
            globallyDrunk,
            drunkByTiming,
          ),
        );
      }
      const significant = [
        ...this.players.flatMap((player) => [...this.characters.keys()].map((role) => this.actualIs(player, role).id)),
        ...[...this.poisonedVars.values()].map((variable) => variable.id),
        ...[...this.drunkVars.values()].map((variable) => variable.id),
        ...[...this.globalDrunkVars.values()].map((variable) => variable.id),
        ...[...this.roleAtVars.values()].map((variable) => variable.id),
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

  private timingPlayerKey(timing: string, player: string): string {
    return keyOf([timing, player]);
  }

  private roleAtKey(timing: string, player: string, role: string): string {
    return keyOf(["role_at", timing, player, role]);
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
    players: readonly string[],
    demon: string,
    target: string,
    direction: 1 | -1,
    noDashiiRole: RoleRef,
    timing: Timing,
  ): BoolVar {
    const timingName = timing;
    const demonIndex = players.indexOf(demon);
    const targetIndex = players.indexOf(target);
    const distance =
      (direction === 1 ? targetIndex - demonIndex : demonIndex - targetIndex + players.length) % players.length;
    if (distance <= 0) return this.constantBool(false, `${demon}_${target}_not_in_direction_${direction}`);
    const between = Array.from({ length: distance - 1 }, (_ignored, offset) => {
      const index = (demonIndex + direction * (offset + 1) + players.length) % players.length;
      return players[index] as string;
    });
    return this.allOf(
      [
        this.hasRoleAt(demon, noDashiiRole, timing),
        this.hasCharacterType(target, CharacterType.Townsfolk),
        ...between.map((betweenPlayer) => this.hasCharacterType(betweenPlayer, CharacterType.Townsfolk).not()),
      ],
      `${target}_closest_townsfolk_${direction}_of_${demon}_${timingName}`,
    );
  }

  private recordInfoMalfunctions(
    player: string,
    role: string,
    timing: Timing,
    activeRole: BoolVar,
    vortoxAffected: boolean,
  ): void {
    const timingName = timing;
    const causes: BoolVar[] = [
      this.allOf([activeRole, this.isPoisonedAt(player, timing)], `${player}_${role}_${timingName}_poison_malfunction`),
      this.allOf([activeRole, this.isDrunkAt(player, timing)], `${player}_${role}_${timingName}_drunk_malfunction`),
      this.allOf(
        [activeRole, this.noDashiiPoisonedAt(player, timing)],
        `${player}_${role}_${timingName}_nodashii_malfunction`,
      ),
    ];
    if (vortoxAffected && this.characters.has(roleName("Vortox"))) {
      causes.push(
        this.allOf([activeRole, this.roleInPlay("Vortox")], `${player}_${role}_${timingName}_vortox_malfunction`),
      );
    }
    const malfunction = this.anyOf(causes, `${player}_${role}_${timingName}_info_malfunction`);
    const malfunctions = this.infoMalfunctionsByTiming.get(timingName) ?? [];
    malfunctions.push(malfunction);
    this.infoMalfunctionsByTiming.set(timingName, malfunctions);
  }

  private applyDefaultTimingRoleConstraints(): void {
    for (const [key, roleAt] of this.roleAtVars.entries()) {
      if (this.defaultRoleAtConstraints.has(key)) continue;
      const [, timing, player, role] = key.split("\u0000") as [
        string | undefined,
        string | undefined,
        string | undefined,
        string | undefined,
      ];
      if (timing === undefined || player === undefined || role === undefined) continue;
      const sources = this.roleAtSources.get(key) ?? [];
      const removals = this.roleAtRemovals.get(key) ?? [];
      this.addClause([roleAt.not(), this.actualIs(player, role).lit, ...sources.map(lit)]);
      this.addClause([this.actualIs(player, role).not(), ...removals.map(lit), roleAt.lit]);
      this.defaultRoleAtConstraints.add(key);
    }
  }

  private applyDefaultSoberConstraints(): void {
    for (const [key, poisoned] of this.poisonedVars.entries()) {
      const [timing] = key.split("\u0000") as [string | undefined, string | undefined];
      const defaultKey = `poison:${key}`;
      if (
        timing === undefined ||
        this.poisonSourceTimingKeys.has(timing) ||
        this.explicitPoisonedTrue.has(key) ||
        this.defaultSoberConstraints.has(defaultKey)
      )
        continue;
      this.addFalse(poisoned);
      this.defaultSoberConstraints.add(defaultKey);
    }
    for (const [key, drunk] of this.drunkVars.entries()) {
      const [timing] = key.split("\u0000") as [string | undefined, string | undefined];
      const defaultKey = `drunk:${key}`;
      if (
        timing === undefined ||
        this.drunkSourceTimingKeys.has(timing) ||
        this.explicitDrunkTrue.has(key) ||
        this.defaultSoberConstraints.has(defaultKey)
      )
        continue;
      this.addFalse(drunk);
      this.defaultSoberConstraints.add(defaultKey);
    }
    if (this.hasGlobalDrunkSource) return;
    for (const [player, drunk] of this.globalDrunkVars.entries()) {
      const key = keyOf(["global_drunk", player]);
      if (this.defaultSoberConstraints.has(key)) continue;
      this.addFalse(drunk);
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
