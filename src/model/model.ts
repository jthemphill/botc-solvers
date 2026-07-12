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

function timingOrder(timing: Timing): number {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) throw new Error(`Invalid timing: ${timing}.`);
  const round = Number(match[2]);
  return round * 2 + (match[1] === "day" ? 1 : 0);
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
  // Timings at which droisoned, poisoned, or drunk state was queried, so script effects that
  // poison (Poisoner, Widow) or drunk (e.g. Sailor, Courtier) players need their sources
  // modeled there.
  readonly droisonTimingKeys = new Set<string>();

  private variableCount = 0;
  private counter = 0;
  private readonly clauses: Clause[] = [];
  private readonly actual = new Map<string, BoolVar>();
  private readonly droisonedVars = new Map<string, BoolVar>();
  private readonly activePoisonSourcesByTiming = new Map<string, BoolLike[]>();
  private readonly poisonSourceTargetsByTimingPlayer = new Map<string, BoolLike[]>();
  private readonly poisonOverridesByTimingPlayer = new Map<string, BoolLike[]>();
  private readonly drunkSourceTargetsByTimingPlayer = new Map<string, BoolLike[]>();
  private readonly poisonQueryVars = new Map<string, BoolVar>();
  private readonly drunkQueryVars = new Map<string, BoolVar>();
  private readonly globalDrunkVars = new Map<string, BoolVar>();
  private readonly globalDrunkSourceTargetsByPlayer = new Map<string, BoolLike[]>();
  private readonly puzzlemasterDrunkSourceTargetsByPlayer = new Map<string, BoolLike[]>();
  private readonly roleAtVars = new Map<string, BoolVar>();
  private readonly roleAtSources = new Map<string, BoolLike[]>();
  private readonly roleAtRemovals = new Map<string, BoolLike[]>();
  private readonly roleActiveByTimingRole = new Map<string, BoolLike>();
  private readonly abilityUses: Array<{
    readonly player: string;
    readonly role: string;
    readonly timing: Timing;
    readonly activeIf: BoolLike;
  }> = [];
  private readonly abilityUsedBeforeQueries = new Map<
    string,
    { readonly player: string; readonly role: string; readonly timing: Timing; readonly variable: BoolVar }
  >();
  private readonly wakePreventionSources = new Map<string, BoolLike[]>();
  private readonly wakePreventionQueries = new Map<string, BoolVar>();
  private readonly defaultWakeConstraints = new Set<string>();
  private readonly defaultRoleAtConstraints = new Set<string>();
  private readonly explicitDroisonTrue = new Set<number>();
  private globalDrunkSourceConstraintsApplied = false;
  private readonly defaultSoberConstraints = new Set<string>();
  private readonly gateCache = new Map<string, BoolVar>();
  private trueConstant: BoolVar | undefined;
  private falseConstant: BoolVar | undefined;
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
    const existing = value ? this.trueConstant : this.falseConstant;
    if (existing !== undefined) return existing;
    const result = this.newBool(name);
    this.addClause([value ? result.lit : result.not()]);
    if (value) this.trueConstant = result;
    else this.falseConstant = result;
    return result;
  }

  private constantValueOf(literal: Literal): boolean | undefined {
    if (this.trueConstant !== undefined && Math.abs(literal) === this.trueConstant.id) return literal > 0;
    if (this.falseConstant !== undefined && Math.abs(literal) === this.falseConstant.id) return literal < 0;
    return undefined;
  }

  private literalBool(literal: Literal, name: string): BoolVar {
    if (literal > 0) return new BoolVar(literal, name);
    const key = keyOf(["not", String(-literal)]);
    let cached = this.gateCache.get(key);
    if (cached === undefined) {
      cached = this.newBool(name);
      this.addClause([cached.not(), literal]);
      this.addClause([cached.lit, negate(literal)]);
      this.gateCache.set(key, cached);
    }
    return cached;
  }

  // Returns a variable defined as the and/or of `values`, reusing the existing variable when an
  // equivalent gate was already built. `identity` is the gate's identity element (true for and,
  // false for or): identity operands are dropped, and an absorbing operand or a complementary
  // operand pair collapses the gate to a constant.
  private gate(
    kind: string,
    values: readonly BoolLike[],
    name: string,
    identity: boolean,
    build: (literals: readonly Literal[], result: BoolVar) => void,
  ): BoolVar {
    const unique = new Set(values.map(lit));
    const literals: Literal[] = [];
    for (const literal of unique) {
      const constant = this.constantValueOf(literal);
      if (constant === identity) continue;
      if (constant === !identity || unique.has(-literal)) return this.constantBool(!identity, name);
      literals.push(literal);
    }
    literals.sort((left, right) => left - right);
    if (literals.length === 0) return this.constantBool(identity, name);
    if (literals.length === 1) return this.literalBool(literals[0] as Literal, name);
    const key = keyOf([kind, ...literals.map(String)]);
    let cached = this.gateCache.get(key);
    if (cached === undefined) {
      cached = this.newBool(name);
      build(literals, cached);
      this.gateCache.set(key, cached);
    }
    return cached;
  }

  actualIs(player: string, role: RoleRef): BoolVar {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    return this.actual.get(this.actualKey(player, roleRef)) as BoolVar;
  }

  droisoned(player: string, timing?: Timing): BoolVar {
    this.checkPlayer(player);
    const droisonTiming = timing ?? DEFAULT_TIMING_KEY;
    this.droisonTimingKeys.add(droisonTiming);
    const key = this.timingPlayerKey(droisonTiming, player);
    let result = this.droisonedVars.get(key);
    if (result === undefined) {
      result = this.newBool(`${slug(player)}__droisoned__${slug(droisonTiming)}`);
      this.droisonedVars.set(key, result);
    }
    return result;
  }

  poisoned(player: string, timing?: Timing): BoolVar {
    this.droisonTimingKeys.add(timing ?? DEFAULT_TIMING_KEY);
    return this.flavorQueryVar(this.poisonQueryVars, player, timing, "poisoned");
  }

  drunk(player: string, timing?: Timing): BoolVar {
    this.droisonTimingKeys.add(timing ?? DEFAULT_TIMING_KEY);
    return this.flavorQueryVar(this.drunkQueryVars, player, timing, "drunk");
  }

  private flavorQueryVar(
    vars: Map<string, BoolVar>,
    player: string,
    timing: Timing | undefined,
    flavor: string,
  ): BoolVar {
    this.checkPlayer(player);
    const flavorTiming = timing ?? DEFAULT_TIMING_KEY;
    const key = this.timingPlayerKey(flavorTiming, player);
    let result = vars.get(key);
    if (result === undefined) {
      result = this.newBool(`${slug(player)}__${flavor}__${slug(flavorTiming)}`);
      vars.set(key, result);
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
      ...(drunkRole !== "Hermit" && this.characters.has(drunkRole) && this.characters.has("Hermit") ? ["Hermit"] : []),
    ];
    const thinksRoleIsOutOfPlayRoles = [
      ...drunkLikeRoles,
      ...(this.characters.has("Marionette") ? ["Marionette"] : []),
    ];
    const claimedTownsfolk = roleCharacterType(claimedRole) === CharacterType.Townsfolk;
    if (claimedTownsfolk && options.possibleActualRoles === undefined) possibleRoles.push(...drunkLikeRoles);
    this.setPossibleActualRoles(claim.player, possibleRoles);
    if (claimedTownsfolk)
      for (const hiddenRole of thinksRoleIsOutOfPlayRoles)
        this.addThinksOutOfPlayRole(claim.player, apparentRole, hiddenRole);
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
      this.addThinksOutOfPlayRole(player, apparentRoleRef, drunkRole);
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

  addThinksOutOfPlayRole(player: string, apparentRole: RoleRef, hiddenRole: RoleRef): void {
    if (!this.uniqueCharacters) return;
    this.addImplication(this.actualIs(player, hiddenRole), this.roleInPlay(apparentRole).not());
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
    this.fixFlavor(this.poisoned(player, timing), player, value, timing);
  }

  fixDrunk(player: string, value: boolean, timing?: Timing): void {
    this.fixFlavor(this.drunk(player, timing), player, value, timing);
  }

  private fixFlavor(flavor: BoolVar, player: string, value: boolean, timing?: Timing): void {
    this.addClause([value ? flavor.lit : flavor.not()]);
    if (value) {
      const droisoned = this.droisoned(player, timing);
      this.addTruth(droisoned);
      this.explicitDroisonTrue.add(droisoned.id);
      this.explicitDroisonTrue.add(flavor.id);
    }
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
      const activeAtTiming = activeByTiming.get(timing) ?? active;
      for (const player of this.players) {
        const sourceTarget = sourceTargets.get(player);
        if (sourceTarget === undefined) continue;
        const activeTarget = this.allOf(
          [activeAtTiming, sourceTarget],
          `${sourceName}_${timing}_${player}_drunk_active_target`,
        );
        this.registerDrunkSourceTarget(player, timing, activeTarget);
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
      const active = this.activeRole(roleRef, `${timing}_${roleRef}_drunking`, options.activeIf);

      for (const player of this.players) {
        if (excludedPlayers.has(player)) continue;
        const hasRole = this.hasRoleAt(player, roleRef, timing);
        this.registerDrunkSourceTarget(
          player,
          timing,
          this.allOf([active, hasRole], `${timing}_${player}_${roleRef}_is_drunked_role`),
        );
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

  addPersistentPoisonSource(
    timings: readonly Timing[],
    candidates: readonly string[],
    activeIf: BoolLike,
    sourceName: string,
  ): void {
    const targets = candidates.map((player) => {
      this.checkPlayer(player);
      const target = this.newBool(`${sourceName}_poisons_${slug(player)}`);
      this.addImplication(target, this.hasCharacterType(player, CharacterType.Townsfolk));
      for (const timing of timings) this.registerPoisonSourceTarget(player, timing, target);
      return target;
    });
    this.addEnforcedExactlyN(targets, 1, activeIf);
    this.addEnforcedExactlyN(targets, 0, negate(lit(activeIf)));
    for (const timing of timings) {
      this.droisonTimingKeys.add(timing);
      this.registerActivePoisonSource(timing, activeIf);
    }
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
      this.droisonTimingKeys.add(timing);
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
    this.checkPlayer(player);
    addMapValue(this.poisonSourceTargetsByTimingPlayer, this.timingPlayerKey(timing, player), target);
  }

  private registerPoisonOverride(player: string, timing: string, override: BoolLike): void {
    this.checkPlayer(player);
    addMapValue(this.poisonOverridesByTimingPlayer, this.timingPlayerKey(timing, player), override);
  }

  private registerDrunkSourceTarget(player: string, timing: string, target: BoolLike): void {
    this.checkPlayer(player);
    addMapValue(this.drunkSourceTargetsByTimingPlayer, this.timingPlayerKey(timing, player), target);
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
    const literals = values.map(lit).sort((left, right) => left - right);
    if (count < 0 || count > literals.length) return this.constantBool(false, name);
    if (literals.length === 0) return this.constantBool(true, name);
    if (literals.length === 1)
      return this.literalBool(count === 1 ? (literals[0] as Literal) : negate(literals[0] as Literal), name);
    const key = keyOf(["sum", String(count), ...literals.map(String)]);
    let cached = this.gateCache.get(key);
    if (cached === undefined) {
      cached = this.reifyExactCount(literals, count, name);
      this.gateCache.set(key, cached);
    }
    return cached;
  }

  allOf(values: readonly BoolLike[], name: string): BoolVar {
    return this.gate("all_of", values, name, true, (literals, result) => {
      for (const literal of literals) this.addClause([result.not(), literal]);
      this.addClause([result.lit, ...literals.map(negate)]);
    });
  }

  anyOf(values: readonly BoolLike[], name: string): BoolVar {
    return this.gate("any_of", values, name, false, (literals, result) => {
      this.addClause([result.not(), ...literals]);
      for (const literal of literals) this.addClause([result.lit, negate(literal)]);
    });
  }

  not(value: BoolLike, name: string): BoolVar {
    const literal = lit(value);
    const constant = this.constantValueOf(literal);
    if (constant !== undefined) return this.constantBool(!constant, name);
    return this.literalBool(negate(literal), name);
  }

  xor(left: BoolLike, right: BoolLike, name: string): BoolVar {
    return this.boolSumEquals([left, right], 1, name);
  }

  isEvil(player: string): BoolVar {
    this.checkPlayer(player);
    return this.anyOf(
      [...this.characters.entries()]
        .filter(([, character]) => roleAlignment(character) === Alignment.Evil)
        .map(([role]) => this.actualIs(player, role)),
      `is_evil_${player}`,
    );
  }

  isGood(player: string): BoolVar {
    this.checkPlayer(player);
    return this.anyOf(
      [...this.characters.entries()]
        .filter(([, character]) => roleAlignment(character) === Alignment.Good)
        .map(([role]) => this.actualIs(player, role)),
      `is_good_${player}`,
    );
  }

  isTownsfolk(player: string): BoolVar {
    return this.hasCharacterType(player, CharacterType.Townsfolk);
  }

  hasCharacterType(player: string, characterType: CharacterType): BoolVar {
    this.checkPlayer(player);
    return this.anyOf(
      [...this.characters.entries()]
        .filter(([, character]) => roleCharacterType(character) === characterType)
        .map(([role]) => this.actualIs(player, role)),
      `is_${characterType}_${player}`,
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
    return this.anyOf(
      this.players.map((player) => this.actualIs(player, roleRef)),
      `${roleRef}_in_play`,
    );
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

  registerAbilityUse(player: string, role: RoleRef, timing: Timing, activeIf: BoolLike): void {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    this.abilityUses.push({ player, role: roleRef, timing, activeIf });
  }

  abilityUsedBefore(player: string, role: RoleRef, timing: Timing, name: string): BoolVar {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const key = keyOf(["ability_used_before", player, roleRef, timing]);
    let query = this.abilityUsedBeforeQueries.get(key);
    if (query === undefined) {
      query = { player, role: roleRef, timing, variable: this.newBool(name) };
      this.abilityUsedBeforeQueries.set(key, query);
    }
    return query.variable;
  }

  preventWakeAt(player: string, timing: Timing, activeIf: BoolLike): void {
    this.checkPlayer(player);
    addMapValue(this.wakePreventionSources, keyOf(["wake_prevented", player, timing]), activeIf);
  }

  wakePreventedAt(player: string, timing: Timing, name: string): BoolVar {
    this.checkPlayer(player);
    const key = keyOf(["wake_prevented", player, timing]);
    let result = this.wakePreventionQueries.get(key);
    if (result === undefined) {
      result = this.newBool(name);
      this.wakePreventionQueries.set(key, result);
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

  isDroisonedAt(player: string, timing: Timing): BoolVar {
    const sources: BoolLike[] = [this.droisoned(player, timing), this.globalDrunk(player)];
    if (this.characters.has("Drunk")) {
      sources.push(this.actualIs(player, "Drunk"));
      if (this.characters.has("Hermit")) sources.push(this.actualIs(player, "Hermit"));
    }
    return this.anyOf(sources, `${player}_droisoned_at_${timing}`);
  }

  soberAndHealthy(player: string, timing: Timing): BoolVar {
    const timingName = timing;
    const unhealthy = this.anyOf(
      [this.isDroisonedAt(player, timing), this.noDashiiPoisonedAt(player, timing)],
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
    isDemon: DemonPredicate = (player, predicateName) =>
      this.registersAsCharacterType(player, CharacterType.Demon, predicateName),
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
    this.applyDefaultWakeConstraints();
    this.applyDefaultSoberConstraints();
    const worlds: World[] = [];
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
      const poisonedByTiming = this.flavorByTiming(
        model,
        [this.poisonSourceTargetsByTimingPlayer, this.poisonOverridesByTimingPlayer],
        this.poisonQueryVars,
      );
      const poisoned = poisonedByTiming.get(DEFAULT_TIMING_KEY) ?? new Set<string>();
      const drunkByTiming = this.flavorByTiming(model, [this.drunkSourceTargetsByTimingPlayer], this.drunkQueryVars);
      const globallyDrunk = new Set(
        [...this.globalDrunkVars.entries()].filter(([, variable]) => model.has(variable.id)).map(([player]) => player),
      );
      worlds.push(
        new World(actual, new Map(this.apparentRoles), poisoned, poisonedByTiming, globallyDrunk, drunkByTiming),
      );
      const actualRoleVariables = this.players.flatMap((player) =>
        [...this.characters.keys()].map((role) => this.actualIs(player, role).id),
      );
      workingClauses.push(actualRoleVariables.map((variable) => (model.has(variable) ? -variable : variable)));
    }
    return worlds;
  }

  private flavorByTiming(
    model: ReadonlySet<number>,
    sourceMaps: readonly ReadonlyMap<string, readonly BoolLike[]>[],
    queryVars: ReadonlyMap<string, BoolVar>,
  ): Map<string, ReadonlySet<string>> {
    const satisfied = (value: BoolLike): boolean => {
      const literal = lit(value);
      return literal > 0 ? model.has(literal) : !model.has(-literal);
    };
    const keys = new Set([...sourceMaps.flatMap((sources) => [...sources.keys()]), ...queryVars.keys()]);
    const result = new Map<string, Set<string>>();
    for (const key of [...keys].sort()) {
      const [timing, player] = key.split("\u0000") as [string, string];
      let players = result.get(timing);
      if (players === undefined) result.set(timing, (players = new Set()));
      const queryVar = queryVars.get(key);
      const affected =
        (queryVar !== undefined && model.has(queryVar.id)) ||
        sourceMaps.some((sources) => (sources.get(key) ?? []).some(satisfied));
      if (affected) players.add(player);
    }
    return result;
  }

  private poisonSourceFlavor(key: string): readonly BoolLike[] {
    return [
      ...(this.poisonSourceTargetsByTimingPlayer.get(key) ?? []),
      ...(this.poisonOverridesByTimingPlayer.get(key) ?? []),
    ];
  }

  private drunkSourceFlavor(key: string): readonly BoolLike[] {
    return this.drunkSourceTargetsByTimingPlayer.get(key) ?? [];
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

  // Returns a variable equivalent to "exactly `count` of `literals` are true", via a sequential
  // counter: row[level - 1] is "at least `level` of the literals seen so far are true", tracked up
  // to count + 1 levels, so the encoding stays polynomial in the input size. Duplicate literals are
  // separate counter inputs and count as many times as they appear.
  private reifyExactCount(literals: readonly Literal[], count: number, name: string): BoolVar {
    const maxLevel = Math.min(count + 1, literals.length);
    let row: BoolLike[] = [];
    for (let index = 0; index < literals.length; index += 1) {
      const literal = literals[index] as Literal;
      const levels = Math.min(index + 1, maxLevel);
      const next: BoolLike[] = [];
      for (let level = 1; level <= levels; level += 1) {
        const levelName = `${name}__ge_${level}_of_${index + 1}`;
        const carry: BoolLike = level === 1 ? literal : this.allOf([literal, row[level - 2] as BoolLike], levelName);
        next.push(level <= row.length ? this.anyOf([row[level - 1] as BoolLike, carry], levelName) : carry);
      }
      row = next;
    }
    const bounds: BoolLike[] = [];
    if (count > 0) bounds.push(row[count - 1] as BoolLike);
    if (count < literals.length) bounds.push(negate(lit(row[count] as BoolLike)));
    return this.allOf(bounds, name);
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
    return (actualRole === "Spy" && this.characters.has("Spy")) || this.roleHasOutsiderAbility(actualRole, "Recluse");
  }

  private roleCanFlexiblyRegisterAsType(actualRole: string, characterType: CharacterType): boolean {
    if (actualRole === "Legion" && this.characters.has(actualRole)) return characterType === CharacterType.Minion;
    if (actualRole === "Spy" && this.characters.has(actualRole))
      return [CharacterType.Minion, CharacterType.Outsider, CharacterType.Townsfolk].includes(characterType);
    if (this.roleHasOutsiderAbility(actualRole, "Recluse"))
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
    if (this.roleHasOutsiderAbility(actualRole, "Recluse")) {
      return (
        observedRole === actualRole ||
        (roleAlignment(observedCharacter) === Alignment.Evil &&
          [CharacterType.Demon, CharacterType.Minion].includes(roleCharacterType(observedCharacter)))
      );
    }
    return false;
  }

  private roleHasOutsiderAbility(actualRole: string, sourceRole: string): boolean {
    return (actualRole === sourceRole || actualRole === "Hermit") && this.characters.has(sourceRole);
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
    const actualDrunkUsingClaimedAbility =
      this.characters.has("Drunk") && this.characters.has("Mathematician")
        ? this.actualIs(player, "Drunk")
        : this.constantBool(false, `${player}_${role}_${timingName}_no_mathematician_drunk_jinx`);
    const causes: BoolVar[] = [
      this.allOf(
        [activeRole, this.isDroisonedAt(player, timing), falseInfo],
        `${player}_${role}_${timingName}_droison_malfunction`,
      ),
      this.allOf(
        [activeRole, this.noDashiiPoisonedAt(player, timing), falseInfo],
        `${player}_${role}_${timingName}_nodashii_malfunction`,
      ),
      this.allOf([actualDrunkUsingClaimedAbility, falseInfo], `${player}_${role}_${timingName}_drunk_role_malfunction`),
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

  roleSoberAndHealthyAt(role: RoleRef, timing: Timing, name: string): BoolVar {
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

  private constrainToAnySource(key: string, variable: BoolVar, sources: readonly BoolLike[]): void {
    if (this.defaultWakeConstraints.has(key)) return;
    for (const source of sources) this.addImplication(source, variable);
    this.addClause([variable.not(), ...sources.map(lit)]);
    this.defaultWakeConstraints.add(key);
  }

  private applyDefaultWakeConstraints(): void {
    for (const [key, query] of this.abilityUsedBeforeQueries) {
      const queryOrder = timingOrder(query.timing);
      const sources = this.abilityUses
        .filter((use) => use.player === query.player && use.role === query.role && timingOrder(use.timing) < queryOrder)
        .map((use) => use.activeIf);
      this.constrainToAnySource(key, query.variable, sources);
    }
    for (const [key, query] of this.wakePreventionQueries) {
      this.constrainToAnySource(key, query, this.wakePreventionSources.get(key) ?? []);
    }
  }

  private applyDefaultSoberConstraints(): void {
    this.applyDefaultXaanPoisoningConstraints();
    this.applyDefaultPoisonCapacityConstraints();
    this.applyFlavorPredicateConstraints();
    for (const [key, droisoned] of this.droisonedVars.entries()) {
      const defaultKey = `droison:${key}`;
      if (this.defaultSoberConstraints.has(defaultKey)) continue;
      const sources = [...this.poisonSourceFlavor(key), ...this.drunkSourceFlavor(key)];
      if (sources.length > 0) {
        for (const source of sources) this.addImplication(source, droisoned);
        this.addClause([droisoned.not(), ...sources.map(lit)]);
      } else if (!this.explicitDroisonTrue.has(droisoned.id)) {
        this.addFalse(droisoned);
      }
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

  private applyFlavorPredicateConstraints(): void {
    const flavors: Array<[string, ReadonlyMap<string, BoolVar>, (key: string) => readonly BoolLike[]]> = [
      ["poison", this.poisonQueryVars, (key) => this.poisonSourceFlavor(key)],
      ["drunk", this.drunkQueryVars, (key) => this.drunkSourceFlavor(key)],
    ];
    for (const [flavor, vars, sourcesForKey] of flavors) {
      for (const [key, flavorVar] of vars.entries()) {
        const defaultKey = `${flavor}_flavor:${key}`;
        if (this.defaultSoberConstraints.has(defaultKey)) continue;
        const sources = sourcesForKey(key);
        if (sources.length > 0) {
          for (const source of sources) this.addImplication(source, flavorVar);
          this.addClause([flavorVar.not(), ...sources.map(lit)]);
        } else if (!this.explicitDroisonTrue.has(flavorVar.id)) {
          this.addFalse(flavorVar);
        }
        this.defaultSoberConstraints.add(defaultKey);
      }
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
      this.addClause([drunk.not(), ...sources.map(lit)]);
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
      const cappedPoisonedPlayers = this.players.map((player) => {
        const sourceTargets = this.poisonSourceTargetsByTimingPlayer.get(this.timingPlayerKey(timing, player)) ?? [];
        return this.anyOf(sourceTargets, `${timing}_${player}_capacity_counted_poison`);
      });
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
