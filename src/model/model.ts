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

function addMapValue<K, V>(map: Map<K, V[]>, key: K, value: V): void {
  const values = map.get(key);
  if (values === undefined) map.set(key, [value]);
  else values.push(value);
}

export class World {
  constructor(
    readonly actual: ReadonlyMap<string, string>,
    readonly apparent: ReadonlyMap<string, string>,
    readonly poisoned: ReadonlySet<string>,
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
  private readonly activePoisonSourcesByTiming = new Map<string, BoolLike[]>();
  private readonly poisonSourceTargetsByTimingPlayer = new Map<string, BoolLike[]>();
  private readonly poisonOverridesByTimingPlayer = new Map<string, BoolLike[]>();
  private readonly drunkVars = new Map<string, BoolVar>();
  private readonly globalDrunkVars = new Map<string, BoolVar>();
  private readonly globalDrunkSourceTargetsByPlayer = new Map<string, BoolLike[]>();
  private readonly puzzlemasterDrunkSourceTargetsByPlayer = new Map<string, BoolLike[]>();
  private readonly roleAtVars = new Map<string, BoolVar>();
  private readonly roleAtSources = new Map<string, BoolLike[]>();
  private readonly roleAtRemovals = new Map<string, BoolLike[]>();
  private readonly roleActiveByTimingRole = new Map<string, BoolLike>();
  private readonly defaultRoleAtConstraints = new Set<string>();
  private readonly drunkSourceTimingKeys = new Set<string>();
  private readonly explicitDroisonTrue = new Set<number>();
  private globalDrunkSourceConstraintsApplied = false;
  private readonly defaultSoberConstraints = new Set<string>();
  private readonly predicateCache = new Map<string, BoolVar>();
  private readonly fortuneTellerRedHerringVars = new Map<string, RedHerrings>();
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
      readonly possibleActualRoles?: readonly RoleRef[];
    } = {},
  ): void {
    const apparentRole = roleName(claim.apparentRole);
    this.setApparentRole(claim.player, apparentRole);
    const evilRoles =
      options.evilRoles ??
      [...this.characters.entries()]
        .filter(([, character]) => roleAlignment(character) === Alignment.Evil)
        .map(([role]) => role);
    const claimedRole = this.characters.get(apparentRole) as RoleRef;
    const claimedEvil = roleAlignment(claimedRole) === Alignment.Evil;
    const possibleRoles = options.possibleActualRoles?.map(roleName) ?? [
      ...(claimedEvil ? [] : [apparentRole]),
      ...evilRoles.map(roleName).filter((role) => !claimedEvil || role !== apparentRole),
    ];
    const drunkRole = roleName(options.drunkRole ?? "Drunk");
    const drunkLikeRoles = [
      ...(this.characters.has(drunkRole) ? [drunkRole] : []),
      ...(drunkRole !== "Hermit" && this.characters.has("Hermit") ? ["Hermit"] : []),
    ];
    const claimedTownsfolk = roleCharacterType(claimedRole) === CharacterType.Townsfolk;
    if (claimedTownsfolk && options.possibleActualRoles === undefined) possibleRoles.push(...drunkLikeRoles);
    this.setPossibleActualRoles(claim.player, possibleRoles);
    if (claimedTownsfolk)
      for (const drunkLikeRole of drunkLikeRoles)
        this.addDrunkThinksOutOfPlayRole(claim.player, apparentRole, drunkLikeRole);
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
    const poisoned = this.poisoned(player, timing);
    this.addClause([value ? poisoned.lit : poisoned.not()]);
    if (value) this.explicitDroisonTrue.add(poisoned.id);
  }

  fixDrunk(player: string, value: boolean, timing?: Timing): void {
    const drunk = this.drunk(player, timing);
    this.addClause([value ? drunk.lit : drunk.not()]);
    if (value) this.explicitDroisonTrue.add(drunk.id);
  }

  addPersistentDrunking(
    timings: readonly Timing[],
    options: {
      readonly activeIf?: BoolLike | boolean;
      readonly activeByTiming?: readonly { readonly timing: Timing; readonly activeIf: BoolLike | boolean }[];
      readonly excludedPlayers?: readonly string[];
      readonly sourceName?: string;
    } = {},
  ): void {
    if (timings.length === 0) return;

    const sourceName = options.sourceName ?? "persistent";
    const excludedPlayers = new Set(options.excludedPlayers ?? []);
    const candidates = this.players.filter((player) => !excludedPlayers.has(player));
    const sourceTargets = new Map(
      candidates.map((player) => [player, this.newBool(`${sourceName}_${player}_drunk_target`)] as const),
    );
    const targetVars = [...sourceTargets.values()];
    const activeByTiming = new Map(
      (options.activeByTiming ?? []).map((entry) => [
        entry.timing,
        typeof entry.activeIf === "boolean"
          ? this.constantBool(entry.activeIf, `${sourceName}_${entry.timing}_drunking_active`)
          : entry.activeIf,
      ]),
    );
    const active =
      options.activeIf === undefined
        ? activeByTiming.size === 0
          ? this.constantBool(true, `${sourceName}_drunking_active`)
          : this.anyOf([...activeByTiming.values()], `${sourceName}_drunking_active`)
        : typeof options.activeIf === "boolean"
          ? this.constantBool(options.activeIf, `${sourceName}_drunking_active`)
          : options.activeIf;

    this.addEnforcedExactlyN(targetVars, 1, active);
    this.addEnforcedExactlyN(targetVars, 0, negate(lit(active)));

    for (const timing of timings) {
      this.drunkSourceTimingKeys.add(timing);
      const activeAtTiming = activeByTiming.get(timing) ?? active;
      for (const player of this.players) {
        const drunk = this.drunk(player, timing);
        const sourceTarget = sourceTargets.get(player);
        if (sourceTarget === undefined) {
          this.addFalse(drunk);
          continue;
        }
        const activeTarget = this.allOf(
          [activeAtTiming, sourceTarget],
          `${sourceName}_${timing}_${player}_drunk_active_target`,
        );
        this.addImplication(activeTarget, drunk);
        this.addImplication(drunk, activeTarget);
      }
    }
  }

  addPuzzlemasterDrunking(
    options: {
      readonly excludedPlayers?: readonly string[];
      readonly activeIf?: BoolLike;
      readonly sourceName?: string;
    } = {},
  ): void {
    const excluded = new Set(options.excludedPlayers ?? []);
    const sourceName = options.sourceName ?? "puzzlemaster";
    this.addOnePlayerDroisonSource(
      options.activeIf,
      (player) => `${sourceName}_${slug(player)}_global_drunk`,
      (player, target) => {
        this.registerGlobalDrunkSourceTarget(player, target);
        addMapValue(this.puzzlemasterDrunkSourceTargetsByPlayer, player, target);
      },
      excluded,
    );
  }

  addVillageIdiotDrunking(options: { readonly villageIdiotRole?: RoleRef } = {}): void {
    const villageIdiotRole = roleName(options.villageIdiotRole ?? "Village Idiot");
    this.checkRole(villageIdiotRole);

    const villageIdiotPlayers = this.players.map((player) => this.actualIs(player, villageIdiotRole));
    const atLeastTwoVillageIdiots = this.anyOf(
      combinations(villageIdiotPlayers, 2).map((pair, index) =>
        this.allOf(pair, `village_idiot_pair_${index + 1}_in_play`),
      ),
      "at_least_two_village_idiots_in_play",
    );
    const drunkPlayers = this.players.map((player) => {
      const drunk = this.newBool(`village_idiot_${slug(player)}_global_drunk`);
      this.registerGlobalDrunkSourceTarget(player, drunk);
      this.addImplication(drunk, this.actualIs(player, villageIdiotRole));
      return drunk;
    });
    this.addEnforcedExactlyN(drunkPlayers, 1, atLeastTwoVillageIdiots);
    this.addEnforcedExactlyN(drunkPlayers, 0, atLeastTwoVillageIdiots.not());
  }

  private registerGlobalDrunkSourceTarget(player: string, target: BoolLike): void {
    this.checkPlayer(player);
    this.addImplication(target, this.globalDrunk(player));
    addMapValue(this.globalDrunkSourceTargetsByPlayer, player, target);
  }

  puzzlemasterDrunk(player: string, name: string): BoolVar {
    this.checkPlayer(player);
    const sources = this.puzzlemasterDrunkSourceTargetsByPlayer.get(player) ?? [];
    return this.anyOf(sources, name);
  }

  addRoleDrunking(
    role: RoleRef,
    timings: readonly Timing[],
    options: { readonly activeIf?: BoolLike | boolean; readonly excludedPlayers?: readonly string[] } = {},
  ): void {
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const excludedPlayers = new Set(options.excludedPlayers ?? []);
    for (const timing of timings) {
      this.drunkSourceTimingKeys.add(timing);
      const active = this.activeRole(roleRef, `${timing}_${roleRef}_drunking`, options.activeIf);

      for (const player of this.players) {
        const drunk = this.drunk(player, timing);
        if (excludedPlayers.has(player)) {
          this.addFalse(drunk);
          continue;
        }
        const hasRole = this.hasRoleAt(player, roleRef, timing);
        this.addImplication(this.allOf([active, hasRole], `${timing}_${player}_${roleRef}_is_drunked_role`), drunk);
        this.addImplication(
          this.allOf([active, hasRole.not()], `${timing}_${player}_${roleRef}_is_not_drunked_role`),
          drunk.not(),
        );
        this.addImplication(active.not(), drunk.not());
      }
    }
  }

  private activeRole(role: RoleRef, name: string, activeIf?: BoolLike | boolean): BoolVar {
    const roleInPlay = this.roleInPlay(role);
    if (activeIf === undefined) return roleInPlay;
    const condition = typeof activeIf === "boolean" ? this.constantBool(activeIf, `${name}_active_if`) : activeIf;
    return this.allOf([roleInPlay, condition], `${name}_active`);
  }

  addPoisonerEffect(
    timing: Timing,
    options: { readonly poisonerRole?: RoleRef; readonly activeIf?: BoolLike | boolean } = {},
  ): void {
    const poisonTiming = timing;
    const poisonerRole = options.poisonerRole ?? "Poisoner";
    const poisonerActive = this.activeRole(poisonerRole, `${poisonTiming}_${roleName(poisonerRole)}`, options.activeIf);
    this.addOnePlayerPoisonSource(timing, poisonerActive, slug(roleName(poisonerRole)));
  }

  addWidowEffect(
    options: {
      readonly widowRole?: RoleRef;
      readonly activeIf?: BoolLike | boolean;
      readonly timings?: readonly Timing[];
    } = {},
  ): void {
    const widowRole = options.widowRole ?? "Widow";
    const widowActive = this.activeRole(widowRole, roleName(widowRole), options.activeIf);
    if ((options.timings ?? []).length === 0) return;
    this.addOnePlayerDroisonSource(
      widowActive,
      (player) => `${slug(roleName(widowRole))}_poisons_${slug(player)}`,
      (player, target) => {
        for (const timing of options.timings ?? []) this.registerPoisonSourceTarget(player, timing, target);
      },
    );
    for (const timing of options.timings ?? []) {
      this.poisonTimingKeys.add(timing);
      this.registerActivePoisonSource(timing, widowActive);
    }
  }

  private registerActivePoisonSource(timing: string, sourceActive: BoolLike): void {
    addMapValue(this.activePoisonSourcesByTiming, timing, sourceActive);
  }

  private addOnePlayerPoisonSource(timing: Timing, sourceActive: BoolLike, sourceName: string): void {
    const poisonTiming = timing;
    this.registerActivePoisonSource(poisonTiming, sourceActive);
    this.addOnePlayerDroisonSource(
      sourceActive,
      (player) => `${poisonTiming}_${sourceName}_poisons_${slug(player)}`,
      (player, target) => this.registerPoisonSourceTarget(player, timing, target),
    );
  }

  private addOnePlayerDroisonSource(
    activeIf: BoolLike | undefined,
    targetName: (player: string) => string,
    registerTarget: (player: string, target: BoolVar) => void,
    excludedPlayers: ReadonlySet<string> = new Set(),
  ): void {
    const candidates = this.players.filter((player) => !excludedPlayers.has(player));
    const targets = candidates.map((player) => {
      const target = this.newBool(targetName(player));
      registerTarget(player, target);
      return target;
    });
    if (activeIf === undefined) {
      this.addExactlyN(targets, 1);
    } else {
      this.addEnforcedExactlyN(targets, 1, activeIf);
      this.addEnforcedExactlyN(targets, 0, negate(lit(activeIf)));
    }
  }

  private registerPoisonSourceTarget(player: string, timing: string, target: BoolLike): void {
    const timingArg = timing === DEFAULT_TIMING_KEY ? undefined : (timing as Timing);
    this.addImplication(target, this.poisoned(player, timingArg));
    addMapValue(this.poisonSourceTargetsByTimingPlayer, this.timingPlayerKey(timing, player), target);
  }

  private registerPoisonOverride(player: string, timing: string, override: BoolLike): void {
    const timingArg = timing === DEFAULT_TIMING_KEY ? undefined : (timing as Timing);
    this.addImplication(override, this.poisoned(player, timingArg));
    addMapValue(this.poisonOverridesByTimingPlayer, this.timingPlayerKey(timing, player), override);
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

  setRoleActiveAt(role: RoleRef, timing: Timing, activeIf: BoolLike): void {
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    this.roleActiveByTimingRole.set(this.timingRoleKey(timing, roleRef), activeIf);
  }

  private roleActiveAt(role: RoleRef, timing: Timing): BoolLike {
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    return this.roleActiveByTimingRole.get(this.timingRoleKey(timing, roleRef)) ?? this.roleInPlay(roleRef);
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
      addMapValue(this.roleAtSources, key, this.constantBool(true, `${player}_${roleRef}_${timing}_role_at_source`));
    } else {
      this.addImplication(value, roleAt);
      addMapValue(this.roleAtSources, key, value);
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
      addMapValue(this.roleAtRemovals, key, this.constantBool(true, `${player}_${roleRef}_${timing}_role_at_removal`));
    } else {
      this.addImplication(value, roleAt.not());
      addMapValue(this.roleAtRemovals, key, value);
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
    const sources: BoolLike[] = [this.drunk(player, timing), this.globalDrunk(player)];
    if (this.characters.has("Drunk")) sources.push(this.actualIs(player, "Drunk"));
    if (this.characters.has("Hermit")) sources.push(this.actualIs(player, "Hermit"));
    return this.anyOf(sources, `${player}_drunk_at_${timing}`);
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

  registersAsCharacterTypeAt(player: string, characterType: CharacterType, timing: Timing, name: string): BoolVar {
    this.checkPlayer(player);
    const result = this.newBool(`${name}_${player}_registers_as_${characterType}_at_${timing}`);
    for (const [role, character] of this.characters.entries()) {
      const roleAt = this.hasRoleAt(player, role, timing);
      if (this.roleCanFlexiblyRegisterAsType(role, characterType)) continue;
      this.addImplication(roleAt, roleCharacterType(character) === characterType ? result : result.not());
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

  registersAsRoleAt(player: string, role: RoleRef, timing: Timing, name: string): BoolVar {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const result = this.newBool(`${name}_${player}_registers_as_${roleRef}_at_${timing}`);
    for (const actualRole of this.characters.keys()) {
      const roleAt = this.hasRoleAt(player, actualRole, timing);
      if (this.roleCanFlexiblyRegisterAsRole(actualRole, roleRef)) continue;
      this.addImplication(roleAt, actualRole === roleRef ? result : result.not());
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
    const key = keyOf([fortuneTeller, roleName(fortuneTellerRole), ...players]);
    const cached = this.fortuneTellerRedHerringVars.get(key);
    if (cached !== undefined) return cached;
    const entries = players.map((player) => [player, this.newBool(`${player}_fortune_teller_red_herring`)] as const);
    const redHerrings = new Map(entries);
    this.addEnforcedExactlyN(
      entries.map(([, variable]) => variable),
      1,
      this.actualIs(fortuneTeller, fortuneTellerRole),
    );
    for (const [player, redHerring] of entries) this.addImplication(redHerring, this.isGood(player));
    this.fortuneTellerRedHerringVars.set(key, redHerrings);
    return redHerrings;
  }

  fortuneTellerRedHerring(fortuneTeller: string, player: string): BoolVar {
    this.checkPlayer(player);
    const redHerrings = this.addFortuneTellerRedHerring(fortuneTeller);
    const redHerring = redHerrings.get(player);
    if (redHerring === undefined) throw new KeyError(`No Fortune Teller red herring variable for ${player}.`);
    return redHerring;
  }

  fortuneTellerYes(
    redHerrings: RedHerrings,
    players: readonly [string, string],
    name: string,
    isDemon: DemonPredicate = (player, predicateName) => this.registersAsCharacterType(player, CharacterType.Demon, predicateName),
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
    const vortoxAffected = this.infoClaimAffectedByVortox(roleRef) || (claim.vortoxAffected ?? false);
    this.recordInfoMalfunctions(claim.player, roleRef, claimTiming, activeRole, claim.learned, vortoxAffected);

    if (!vortoxAffected || !this.characters.has(roleName("Vortox"))) {
      this.addImplication(activeHealthy, claim.learned);
      return;
    }

    const activeVortox = this.roleSoberAndHealthyAt("Vortox", claimTiming, `${claim.player}_${roleRef}_vortox`);
    this.addImplication(
      this.allOf([activeHealthy, activeVortox.not()], `${claim.player}_${roleRef}_${claimTimingName}_normal`),
      claim.learned,
    );
    this.addImplication(
      this.allOf([activeRole, activeVortox], `${claim.player}_${roleRef}_${claimTimingName}_vortox`),
      this.not(claim.learned, `${claim.player}_${roleRef}_${claimTimingName}_vortox_false`),
    );
  }

  private infoClaimAffectedByVortox(roleRef: string): boolean {
    if (roleRef === "Snake Charmer") return false;
    const role = this.characters.get(roleRef);
    if (role === undefined) return false;
    try {
      return roleCharacterType(role) === CharacterType.Townsfolk;
    } catch {
      return false;
    }
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
          new World(actual, new Map(this.apparentRoles), poisoned, poisonedByTiming, globallyDrunk, drunkByTiming),
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

  private timingRoleKey(timing: string, role: string): string {
    return keyOf([timing, role]);
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
    return (
      (actualRole === "Spy" || actualRole === "Recluse" || actualRole === "Hermit") && this.characters.has(actualRole)
    );
  }

  private roleCanFlexiblyRegisterAsType(actualRole: string, characterType: CharacterType): boolean {
    if (actualRole === "Legion" && this.characters.has(actualRole)) return characterType === CharacterType.Minion;
    if (actualRole === "Spy" && this.characters.has(actualRole))
      return [CharacterType.Minion, CharacterType.Outsider, CharacterType.Townsfolk].includes(characterType);
    if ((actualRole === "Recluse" || actualRole === "Hermit") && this.characters.has(actualRole))
      return [CharacterType.Demon, CharacterType.Minion, CharacterType.Outsider].includes(characterType);
    return false;
  }

  private roleCanFlexiblyRegisterAsRole(actualRole: string, observedRole: string): boolean {
    const observedCharacter = this.characters.get(observedRole) as RoleRef;
    if (actualRole === "Legion" && this.characters.has(actualRole)) {
      return observedRole === "Legion" || roleCharacterType(observedCharacter) === CharacterType.Minion;
    }
    if (actualRole === "Spy" && this.characters.has(actualRole)) {
      return (
        observedRole === "Spy" ||
        (roleAlignment(observedCharacter) === Alignment.Good &&
          [CharacterType.Outsider, CharacterType.Townsfolk].includes(roleCharacterType(observedCharacter)))
      );
    }
    if ((actualRole === "Recluse" || actualRole === "Hermit") && this.characters.has(actualRole)) {
      return (
        observedRole === actualRole ||
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
      (direction === 1 ? targetIndex - demonIndex + players.length : demonIndex - targetIndex + players.length) %
      players.length;
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
    reportedInfo: BoolLike,
    vortoxAffected: boolean,
  ): void {
    const timingName = timing;
    const falseInfo = this.not(reportedInfo, `${player}_${role}_${timingName}_reported_info_false`);
    const causes: BoolVar[] = [
      this.allOf(
        [activeRole, this.isPoisonedAt(player, timing), falseInfo],
        `${player}_${role}_${timingName}_poison_malfunction`,
      ),
      this.allOf(
        [activeRole, this.isDrunkAt(player, timing), falseInfo],
        `${player}_${role}_${timingName}_drunk_malfunction`,
      ),
      this.allOf(
        [activeRole, this.noDashiiPoisonedAt(player, timing), falseInfo],
        `${player}_${role}_${timingName}_nodashii_malfunction`,
      ),
    ];
    if (vortoxAffected && this.characters.has(roleName("Vortox"))) {
      causes.push(
        this.allOf(
          [activeRole, this.roleSoberAndHealthyAt("Vortox", timing, `${player}_${role}_vortox`), falseInfo],
          `${player}_${role}_${timingName}_vortox_malfunction`,
        ),
      );
    }
    const malfunction = this.anyOf(causes, `${player}_${role}_${timingName}_info_malfunction`);
    addMapValue(this.infoMalfunctionsByTiming, timingName, malfunction);
  }

  private roleSoberAndHealthyAt(role: RoleRef, timing: Timing, name: string): BoolVar {
    const roleRef = roleName(role);
    return this.anyOf(
      this.players.map((player) =>
        this.allOf(
          [this.hasRoleAt(player, roleRef, timing), this.soberAndHealthy(player, timing)],
          `${name}_${player}_${timing}_sober_healthy`,
        ),
      ),
      `${name}_${timing}_sober_healthy_in_play`,
    );
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
    this.applyDefaultXaanPoisoningConstraints();
    this.applyDefaultPoisonCapacityConstraints();
    const poisonCapableTimingKeys = new Set([
      ...this.activePoisonSourcesByTiming.keys(),
      ...[...this.poisonOverridesByTimingPlayer.keys()].map((key) => key.split("\u0000")[0] as string),
    ]);
    for (const [key, poisoned] of this.poisonedVars.entries()) {
      const [timing] = key.split("\u0000") as [string | undefined, string | undefined];
      const defaultKey = `poison:${key}`;
      if (timing === undefined || this.defaultSoberConstraints.has(defaultKey)) continue;
      if (poisonCapableTimingKeys.has(timing)) continue;
      if (this.explicitDroisonTrue.has(poisoned.id)) continue;
      this.addFalse(poisoned);
      this.defaultSoberConstraints.add(defaultKey);
    }
    for (const [key, drunk] of this.drunkVars.entries()) {
      const [timing] = key.split("\u0000") as [string | undefined, string | undefined];
      const defaultKey = `drunk:${key}`;
      if (
        timing === undefined ||
        this.drunkSourceTimingKeys.has(timing) ||
        this.explicitDroisonTrue.has(drunk.id) ||
        this.defaultSoberConstraints.has(defaultKey)
      )
        continue;
      this.addFalse(drunk);
      this.defaultSoberConstraints.add(defaultKey);
    }
    if (this.globalDrunkSourceTargetsByPlayer.size > 0) {
      this.applyGlobalDrunkSourceConstraints();
      return;
    }
    for (const [player, drunk] of this.globalDrunkVars.entries()) {
      const key = keyOf(["global_drunk", player]);
      if (this.defaultSoberConstraints.has(key)) continue;
      this.addFalse(drunk);
      this.defaultSoberConstraints.add(key);
    }
  }

  private applyDefaultXaanPoisoningConstraints(): void {
    const key = "xaan_poisoning";
    if (this.defaultSoberConstraints.has(key)) return;
    this.defaultSoberConstraints.add(key);
    if (!this.characters.has("Xaan")) return;
    const maxOutsiders = [...this.characters.values()]
      .filter((role) => roleCharacterType(role) === CharacterType.Outsider)
      .reduce((total, role) => total + roleMaxCopies(role), 0);
    for (let count = 0; count <= maxOutsiders; count += 1) {
      const timing = `night_${count}` as Timing;
      this.poisonTimingKeys.add(timing);
      const xaanPoisoning = this.allOf(
        [this.roleActiveAt("Xaan", timing), this.outsiderCountIs(count, { name: `xaan_${count}_outsiders` })],
        `xaan_${count}_outsiders_poisoning`,
      );
      for (const player of this.players) {
        const poisoned = this.allOf([xaanPoisoning, this.isTownsfolk(player)], `${timing}_${player}_xaan_poisoned`);
        this.registerPoisonOverride(player, timing, poisoned);
      }
    }
  }

  private applyGlobalDrunkSourceConstraints(): void {
    if (this.globalDrunkSourceConstraintsApplied) return;
    for (const [player, drunk] of this.globalDrunkVars.entries()) {
      const sources = this.globalDrunkSourceTargetsByPlayer.get(player) ?? [];
      if (sources.length === 0) {
        this.addFalse(drunk);
        continue;
      }
      const sourceActive =
        sources.length === 1 ? sources[0] : this.anyOf(sources, `${player}_global_drunk_source_active`);
      this.addImplication(drunk, sourceActive as BoolLike);
    }
    this.globalDrunkSourceConstraintsApplied = true;
  }

  private applyDefaultPoisonCapacityConstraints(): void {
    const overrideTimings = [...this.poisonOverridesByTimingPlayer.keys()].map(
      (key) => key.split("\u0000")[0] as string,
    );
    const targetTimings = [...this.poisonSourceTargetsByTimingPlayer.keys()].map(
      (key) => key.split("\u0000")[0] as string,
    );
    const timings = new Set([...this.activePoisonSourcesByTiming.keys(), ...overrideTimings, ...targetTimings]);
    for (const timing of timings) {
      const key = `poison_capacity:${timing}`;
      if (this.defaultSoberConstraints.has(key)) continue;
      const activeSources = this.activePoisonSourcesByTiming.get(timing) ?? [];
      const timingArg = timing === DEFAULT_TIMING_KEY ? undefined : (timing as Timing);
      const cappedPoisonedPlayers = this.players.map((player) => {
        const poisoned = this.poisoned(player, timingArg);
        const overrides = this.poisonOverridesByTimingPlayer.get(this.timingPlayerKey(timing, player)) ?? [];
        if (overrides.length === 0) return poisoned;
        const overridden = this.anyOf(overrides, `${timing}_${player}_poison_capacity_override`);
        return this.allOf([poisoned, overridden.not()], `${timing}_${player}_capacity_counted_poison`);
      });
      for (const player of this.players) {
        const poisoned = this.poisoned(player, timingArg);
        const sourceTargets = this.poisonSourceTargetsByTimingPlayer.get(this.timingPlayerKey(timing, player)) ?? [];
        const overrides = this.poisonOverridesByTimingPlayer.get(this.timingPlayerKey(timing, player)) ?? [];
        if (sourceTargets.length === 0 && overrides.length === 0) continue;
        this.addImplication(
          poisoned,
          this.anyOf([...sourceTargets, ...overrides], `${timing}_${player}_poison_source_or_override`),
        );
      }
      this.addCountAtMostCount(cappedPoisonedPlayers, activeSources);
      this.defaultSoberConstraints.add(key);
    }
  }

  private addCountAtMostCount(leftValues: readonly BoolLike[], rightValues: readonly BoolLike[]): void {
    const leftLiterals = leftValues.map(lit);
    const rightLiterals = rightValues.map(lit);
    const maxLeftSubsetSize = Math.min(leftLiterals.length, rightLiterals.length + 1);
    for (let leftSubsetSize = 1; leftSubsetSize <= maxLeftSubsetSize; leftSubsetSize += 1) {
      const falseRightSubsetSize = rightLiterals.length - leftSubsetSize + 1;
      for (const leftSubset of combinations(leftLiterals, leftSubsetSize)) {
        for (const falseRightSubset of combinations(rightLiterals, falseRightSubsetSize)) {
          this.addClause([...leftSubset.map(negate), ...falseRightSubset]);
        }
      }
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
