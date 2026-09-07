import { World, KeyError, flavorByTiming } from "./world";
import { enumerateWorlds, type SolveReport } from "./solve";
export { World, KeyError, forcedRoleHolders } from "./world";
export type { SolveReport } from "./solve";
import { BooleanConstraints, BoolVar, lit, type BoolLike } from "./boolean";
export { BoolVar, type BoolLike } from "./boolean";
import { slug, keyOf, addMapValue } from "./keys";
import type { SatProblem } from "./sat";
import { select, constrainSelection, type ChoiceAction, type ChoiceWitness } from "./actions";
import { CharacterTrace } from "./trace";
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
import { type SatBackend, combinations, negate } from "./sat";

export { day, night, type Timing } from "./timing";
import { night, timingOrder, type Timing } from "./timing";

const DEFAULT_TIMING_KEY = "default";

export interface TimingQuery {
  readonly timing?: Timing;
}

export type RedHerrings = ReadonlyMap<string, BoolVar>;
export type DemonPredicate = (player: string, name: string) => BoolLike;

export interface InfoClaimConstraint {
  readonly player: string;
  readonly role: RoleRef;
  readonly learned: BoolLike;
  readonly malfunctionLearned?: BoolLike;
  readonly timing: Timing;
  readonly vortoxAffected?: boolean;
}

export class BOTCModel extends BooleanConstraints {
  private finalizeMs = 0;
  private readonly choiceActions: ChoiceAction[] = [];
  private readonly pitHagDemonCreations = new Map<Timing, BoolLike[]>();
  readonly trace = new CharacterTrace(this);
  private observationTiming: Timing | undefined;
  private readonly acquiredAbilities: Array<{
    player: string;
    role: string;
    timing: Timing;
    active: BoolLike;
    sourceRole?: string;
  }> = [];
  readonly players: string[];
  readonly characters: ReadonlyMap<string, RoleRef>;
  readonly uniqueCharacters: boolean;
  readonly apparentRoles = new Map<string, string>();
  // This set contains the times of queries for poison or drunkenness.
  // Add the applicable effect sources at each of these times.
  readonly droisonTimingKeys = new Set<string>();

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
  private readonly lleechHostTargetsByPlayer = new Map<string, BoolLike[]>();
  private readonly abilityAtVars = new Map<string, BoolVar>();
  private readonly abilityRemovals = new Map<string, BoolLike[]>();
  private readonly roleActiveByTimingRole = new Map<string, BoolLike>();
  private readonly goodAtVars = new Map<string, BoolVar>();
  private readonly goodAtSources = new Map<string, BoolLike>();
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
  private readonly abilityTargets: Array<{
    readonly actor: string;
    readonly role: string;
    readonly target: string;
    readonly timing: Timing;
    readonly order: number;
    readonly activeIf: BoolLike;
  }> = [];
  private readonly abilityTargetQueries = new Map<
    string,
    {
      readonly actor: string;
      readonly role: string;
      readonly target: string;
      readonly timing: Timing;
      readonly variable: BoolVar;
    }
  >();
  private readonly wakePreventionSources = new Map<string, BoolLike[]>();
  private readonly wakePreventionQueries = new Map<string, BoolVar>();
  private readonly conditionalWakeSources = new Map<string, BoolLike[]>();
  private readonly conditionalWakeQueries = new Map<string, BoolVar>();
  private readonly preDroisonHealthQueries: Array<{
    readonly player: string;
    readonly timing: Timing;
    readonly excludedPoisonSourceIds: ReadonlySet<number>;
    readonly excludedSourceIds: ReadonlySet<number>;
    readonly variable: BoolVar;
  }> = [];
  private readonly explicitDroisonTrue = new Set<number>();
  private readonly fortuneTellerRedHerringVars = new Map<string, RedHerrings>();
  private readonly malfunctions = new Map<string, Map<string, BoolLike[]>>();
  private readonly malfunctionQueries: Array<{ timing: Timing; count: number; observer?: string; variable: BoolVar }> =
    [];
  private readonly backend: SatBackend;

  constructor(
    players: readonly string[],
    options: {
      readonly characters: readonly RoleRef[];
      readonly uniqueCharacters?: boolean;
      readonly backend: SatBackend;
    },
  ) {
    super();
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

  registerChoiceAction(action: ChoiceAction): void {
    this.assertBuilding();
    this.choiceActions.push(action);
  }

  registerPitHagDemonCreation(timing: Timing, active: BoolLike): void {
    this.assertBuilding();
    this.pitHagDemonCreations.set(timing, [...(this.pitHagDemonCreations.get(timing) ?? []), active]);
  }

  pitHagCreatedDemon(timing: Timing): BoolVar {
    return this.anyOf(this.pitHagDemonCreations.get(timing) ?? [], `${timing}_pit_hag_created_demon`);
  }

  private decodeActions(model: ReadonlySet<number>): readonly ChoiceWitness[] {
    return this.choiceActions.map((action) => ({
      rule: action.rule,
      actor: action.actor,
      timing: action.timing,
      count: action.count,
      active: model.has(Math.abs(lit(action.active))) === lit(action.active) > 0,
      candidates: [...action.choices.keys()],
      selected: [...action.choices]
        .filter(([, variable]) => model.has(Math.abs(lit(variable))) === lit(variable) > 0)
        .map(([candidate]) => candidate),
    }));
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
    this.assertBuilding();
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
      readonly timing?: Timing;
    } = {},
  ): void {
    this.assertBuilding();
    const apparentRole = roleName(claim.apparentRole);
    this.setApparentRole(claim.player, apparentRole);
    if (options.timing !== undefined && timingOrder(options.timing) > timingOrder(night(1))) {
      if (options.possibleActualRoles) this.setPossibleActualRoles(claim.player, options.possibleActualRoles);
      return; // The document builder compares these claims with the character trace.
    }
    const evilRoles =
      options.evilRoles ??
      [...this.characters.entries()]
        .filter(([, character]) => roleAlignment(character) === Alignment.Evil)
        .map(([role]) => role);
    const claimedRole = this.characters.get(apparentRole) as RoleRef;
    const roleClaimAlignment = claim.alignment ?? roleAlignment(claimedRole);
    const claimedEvil = roleClaimAlignment === Alignment.Evil;
    const truthfulRoles =
      claim.alignment !== undefined && claim.alignment !== roleAlignment(claimedRole)
        ? [...this.characters.entries()]
            .filter(([, character]) => roleAlignment(character) === claim.alignment)
            .map(([role]) => role)
        : [apparentRole];
    const possibleRoles = options.possibleActualRoles?.map(roleName) ?? [
      ...(claimedEvil ? [] : truthfulRoles),
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
    if (claimedTownsfolk && options.possibleActualRoles === undefined) {
      possibleRoles.push(...drunkLikeRoles);
      if (this.characters.has("Goon")) possibleRoles.push("Goon");
    }
    this.setPossibleActualRoles(claim.player, possibleRoles);
    if (claimedTownsfolk)
      for (const hiddenRole of thinksRoleIsOutOfPlayRoles)
        this.addThinksOutOfPlayRole(claim.player, apparentRole, hiddenRole);
  }

  setPossibleActualRoles(player: string, roles: readonly RoleRef[]): void {
    this.assertBuilding();
    this.checkPlayer(player);
    const allowed = new Set(roles.map(roleName));
    for (const role of allowed) this.checkRole(role);
    for (const role of this.characters.keys()) if (!allowed.has(role)) this.addFalse(this.actualIs(player, role));
  }

  fixActual(player: string, role: RoleRef): void {
    this.assertBuilding();
    this.addTruth(this.actualIs(player, role));
  }

  fixNotActual(player: string, role: RoleRef): void {
    this.assertBuilding();
    this.addFalse(this.actualIs(player, role));
  }

  addThinksOutOfPlayRole(player: string, apparentRole: RoleRef, hiddenRole: RoleRef): void {
    this.assertBuilding();
    if (!this.uniqueCharacters) return;
    this.addImplication(this.actualIs(player, hiddenRole), this.roleInPlay(apparentRole).not());
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

  fixPoisoned(player: string, value: boolean, timing?: Timing): void {
    this.assertBuilding();
    this.fixFlavor(this.poisoned(player, timing), player, value, timing);
  }

  private fixFlavor(flavor: BoolVar, player: string, value: boolean, timing?: Timing): void {
    this.assertBuilding();
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
    this.assertBuilding();
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

    constrainSelection(this, targetVars, 1, active);

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

  addNightlyChoiceDrunking(
    actor: string,
    role: RoleRef,
    timing: Timing,
    candidates: readonly string[],
    affectedTimings: readonly Timing[],
    sourceName: string,
  ): BoolLike {
    const uniqueCandidates = [...new Set(candidates)];
    for (const player of uniqueCandidates) this.checkPlayer(player);
    const active = this.newBool(`${sourceName}_active`);
    const targets = uniqueCandidates.map(
      (player) => [player, this.newBool(`${sourceName}_${slug(player)}_target`)] as const,
    );
    const ownSourcesAtAbilityTiming: BoolLike[] = [];
    for (const affectedTiming of affectedTimings) {
      for (const [player, target] of targets) {
        const activeTarget = this.allOf(
          [active, target],
          `${sourceName}_${affectedTiming}_${slug(player)}_active_target`,
        );
        this.registerDrunkSourceTarget(player, affectedTiming, activeTarget);
        if (affectedTiming === timing) ownSourcesAtAbilityTiming.push(activeTarget);
      }
    }
    const preAbilityHealthy = this.soberAndHealthyBeforeOwnDrunking(
      actor,
      timing,
      ownSourcesAtAbilityTiming,
      `${sourceName}_actor_healthy_before_choice`,
    );
    const shouldBeActive = this.allOf(
      [this.hasAbilityAt(actor, role, timing), preAbilityHealthy],
      `${sourceName}_should_be_active`,
    );
    this.equate(active, shouldBeActive);
    constrainSelection(
      this,
      targets.map(([, target]) => target),
      1,
      active,
    );
    return active;
  }

  addPuzzlemasterDrunking(
    options: {
      readonly excludedPlayers?: readonly string[];
      readonly activeIf?: BoolLike;
      readonly sourceName?: string;
    } = {},
  ): void {
    this.assertBuilding();
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
    this.assertBuilding();
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
    constrainSelection(this, drunkPlayers, 1, atLeastTwoVillageIdiots);
  }

  private registerGlobalDrunkSourceTarget(player: string, target: BoolLike): void {
    this.assertBuilding();
    this.checkPlayer(player);
    this.addImplication(target, this.globalDrunk(player));
    addMapValue(this.globalDrunkSourceTargetsByPlayer, player, target);
  }

  puzzlemasterDrunk(player: string, name: string): BoolVar {
    this.checkPlayer(player);
    const sources = this.puzzlemasterDrunkSourceTargetsByPlayer.get(player) ?? [];
    return this.anyOf(sources, name);
  }

  addLleechHostChoice(options: { readonly role?: RoleRef; readonly sourceName?: string } = {}): void {
    this.assertBuilding();
    const role = roleName(options.role ?? "Lleech");
    const sourceName = options.sourceName ?? "lleech_host";
    this.checkRole(role);
    const active = this.roleInPlay(role);
    const targets = this.players.map((player) => {
      const target = this.newBool(`${sourceName}_${slug(player)}`);
      this.addImplication(target, active);
      this.addImplication(target, this.actualIs(player, role).not());
      addMapValue(this.lleechHostTargetsByPlayer, player, target);
      return target;
    });
    constrainSelection(this, targets, 1, active);
  }

  lleechHost(player: string, name: string): BoolVar {
    this.checkPlayer(player);
    return this.anyOf(this.lleechHostTargetsByPlayer.get(player) ?? [], name);
  }

  addLleechHostPoisoning(timings: readonly Timing[], options: { readonly role?: RoleRef } = {}): void {
    this.assertBuilding();
    const role = roleName(options.role ?? "Lleech");
    this.checkRole(role);
    const active = this.roleInPlay(role);
    for (const timing of timings) {
      this.registerActivePoisonSource(timing, active);
      for (const player of this.players) {
        for (const target of this.lleechHostTargetsByPlayer.get(player) ?? []) {
          this.registerPoisonSourceTarget(player, timing, target);
        }
      }
    }
  }

  addRoleDrunking(
    role: RoleRef,
    timings: readonly Timing[],
    options: { readonly activeIf?: BoolLike | boolean; readonly excludedPlayers?: readonly string[] } = {},
  ): void {
    this.assertBuilding();
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const excludedPlayers = new Set(options.excludedPlayers ?? []);
    for (const timing of timings) {
      const active = this.activeRole(roleRef, `${timing}_${roleRef}_drunking`, options.activeIf);

      for (const player of this.players) {
        if (excludedPlayers.has(player)) continue;
        const hasRole = this.hasAbilityAt(player, roleRef, timing);
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
    this.assertBuilding();
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
    this.assertBuilding();
    const targets = candidates.map((player) => {
      this.checkPlayer(player);
      const target = this.newBool(`${sourceName}_poisons_${slug(player)}`);
      this.addImplication(target, this.hasCharacterType(player, CharacterType.Townsfolk));
      for (const timing of timings) this.registerPoisonSourceTarget(player, timing, target);
      return target;
    });
    constrainSelection(this, targets, 1, activeIf);
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
    this.assertBuilding();
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
    this.assertBuilding();
    addMapValue(this.activePoisonSourcesByTiming, timing, sourceActive);
  }

  private addOnePlayerPoisonSource(timing: Timing, sourceActive: BoolLike, sourceName: string): void {
    this.assertBuilding();
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
    this.assertBuilding();
    const candidates = this.players.filter((player) => !excludedPlayers.has(player));
    const targets = candidates.map((player) => {
      const target = this.newBool(targetName(player));
      registerTarget(player, target);
      return target;
    });
    if (activeIf === undefined) {
      this.addExactlyN(targets, 1);
    } else {
      constrainSelection(this, targets, 1, activeIf);
    }
  }

  private registerPoisonSourceTarget(player: string, timing: string, target: BoolLike): void {
    this.assertBuilding();
    this.checkPlayer(player);
    addMapValue(this.poisonSourceTargetsByTimingPlayer, this.timingPlayerKey(timing, player), target);
  }

  private registerPoisonOverride(player: string, timing: string, override: BoolLike): void {
    this.assertBuilding();
    this.checkPlayer(player);
    addMapValue(this.poisonOverridesByTimingPlayer, this.timingPlayerKey(timing, player), override);
  }

  private registerDrunkSourceTarget(player: string, timing: string, target: BoolLike): void {
    this.assertBuilding();
    this.checkPlayer(player);
    addMapValue(this.drunkSourceTargetsByTimingPlayer, this.timingPlayerKey(timing, player), target);
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

  isGoodAt(player: string, timing: Timing): BoolVar {
    this.checkPlayer(player);
    const key = this.timingPlayerKey(timing, player);
    let result = this.goodAtVars.get(key);
    if (result === undefined) {
      result = this.newBool(`${slug(player)}_good_at_${timing}`);
      this.goodAtVars.set(key, result);
    }
    return result;
  }

  isEvilAt(player: string, timing: Timing): BoolVar {
    return this.not(this.isGoodAt(player, timing), `${slug(player)}_evil_at_${timing}`);
  }

  setGoodAt(player: string, timing: Timing, goodIf: BoolLike): void {
    this.assertBuilding();
    this.checkPlayer(player);
    const key = this.timingPlayerKey(timing, player);
    this.goodAtSources.set(key, goodIf);
    this.isGoodAt(player, timing);
  }

  hasAlignmentOverrideAt(player: string, timing: Timing): boolean {
    this.checkPlayer(player);
    return this.goodAtSources.has(this.timingPlayerKey(timing, player));
  }

  addTimedDrunkSource(player: string, timings: readonly Timing[], activeIf: BoolLike): void {
    this.assertBuilding();
    this.checkPlayer(player);
    for (const timing of timings) this.registerDrunkSourceTarget(player, timing, activeIf);
  }

  addPoisonState(timing: Timing, targets: ReadonlyMap<string, BoolLike>, sourceName: string): void {
    this.assertBuilding();
    for (const player of targets.keys()) this.checkPlayer(player);
    const active = this.anyOf([...targets.values()], `${sourceName}_active`);
    this.droisonTimingKeys.add(timing);
    this.registerActivePoisonSource(timing, active);
    for (const [player, targeted] of targets) this.registerPoisonSourceTarget(player, timing, targeted);
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
    this.assertBuilding();
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    this.roleActiveByTimingRole.set(this.timingRoleKey(timing, roleRef), activeIf);
  }

  private roleActiveAt(role: RoleRef, timing: Timing): BoolLike {
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    return this.roleActiveByTimingRole.get(this.timingRoleKey(timing, roleRef)) ?? this.roleInPlay(roleRef);
  }

  hasAbilityAt(player: string, role: RoleRef, timing?: Timing): BoolVar {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const roleTiming = timing ?? DEFAULT_TIMING_KEY;
    if (roleTiming === DEFAULT_TIMING_KEY) return this.actualIs(player, roleRef);
    const key = this.abilityAtKey(roleTiming, player, roleRef);
    let result = this.abilityAtVars.get(key);
    if (result === undefined) {
      result = this.newBool(`${player}_${roleRef}_${roleTiming}`);
      this.abilityAtVars.set(key, result);
    }
    return result;
  }

  registerAbilityUse(player: string, role: RoleRef, timing: Timing, activeIf: BoolLike): void {
    this.assertBuilding();
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    this.abilityUses.push({ player, role: roleRef, timing, activeIf });
  }

  enforceAbilityUseLimit(role: RoleRef, count: number): void {
    this.assertBuilding();
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const always = this.constantBool(true, `${slug(roleRef)}_ability_use_limit_active`);
    for (const player of this.players) {
      this.addEnforcedAtMostN(
        this.abilityUses.filter((use) => use.player === player && use.role === roleRef).map((use) => use.activeIf),
        count,
        always,
      );
    }
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

  registerAbilityTarget(
    actor: string,
    role: RoleRef,
    target: string,
    timing: Timing,
    activeIf: BoolLike,
    order: number,
  ): void {
    this.assertBuilding();
    this.checkPlayer(actor);
    this.checkPlayer(target);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    this.abilityTargets.push({ actor, role: roleRef, target, timing, order, activeIf });
  }

  abilityTargetedAt(actor: string, role: RoleRef, target: string, timing: Timing, name: string): BoolVar {
    this.checkPlayer(actor);
    this.checkPlayer(target);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const key = keyOf(["ability_target", actor, roleRef, target, timing]);
    let query = this.abilityTargetQueries.get(key);
    if (query === undefined) {
      query = { actor, role: roleRef, target, timing, variable: this.newBool(name) };
      this.abilityTargetQueries.set(key, query);
    }
    return query.variable;
  }

  registeredAbilityTargets(): readonly {
    readonly actor: string;
    readonly role: string;
    readonly target: string;
    readonly timing: Timing;
    readonly order: number;
    readonly activeIf: BoolLike;
  }[] {
    return this.abilityTargets;
  }

  preventWakeAt(player: string, timing: Timing, activeIf: BoolLike): void {
    this.assertBuilding();
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

  registerConditionalWake(player: string, role: RoleRef, timing: Timing, activeIf: BoolLike): void {
    this.assertBuilding();
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    addMapValue(this.conditionalWakeSources, keyOf(["conditional_wake", player, roleRef, timing]), activeIf);
  }

  conditionalWakeAt(player: string, role: RoleRef, timing: Timing, name: string): BoolVar {
    this.checkPlayer(player);
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const key = keyOf(["conditional_wake", player, roleRef, timing]);
    let result = this.conditionalWakeQueries.get(key);
    if (result === undefined) {
      result = this.newBool(name);
      this.conditionalWakeQueries.set(key, result);
    }
    return result;
  }

  characterAt(player: string, role: RoleRef, timing?: Timing): BoolVar {
    return this.trace.at(player, roleName(role), timing);
  }

  characterBefore(player: string, role: RoleRef, timing: Timing): BoolVar {
    return this.trace.at(player, roleName(role), timing, true);
  }

  hasCharacterTypeAt(player: string, type: CharacterType, timing?: Timing): BoolVar {
    return this.anyOf(
      [...this.characters]
        .filter(([, role]) => roleCharacterType(role) === type)
        .map(([role]) => this.characterAt(player, role, timing)),
      `${player}_${type}_${timing}`,
    );
  }

  withTiming<T>(timing: Timing | undefined, evaluate: () => T): T {
    const previous = this.observationTiming;
    this.observationTiming = timing;
    try {
      return evaluate();
    } finally {
      this.observationTiming = previous;
    }
  }

  gainAbility(player: string, role: RoleRef, timing: Timing, active: BoolLike, sourceRole?: string): void {
    this.assertBuilding();
    this.acquiredAbilities.push({ player, role: roleName(role), timing, active, sourceRole });
  }

  replaceCharacter(
    player: string,
    role: RoleRef,
    timing: Timing,
    active: BoolLike = this.constantBool(true, "character_transition"),
  ): BoolVar {
    this.assertBuilding();
    this.trace.replace({ player, character: roleName(role), timing, active, rule: "character-change" });
    return this.hasAbilityAt(player, role, timing);
  }

  removeAbility(
    player: string,
    role: RoleRef,
    timing: Timing,
    active: BoolLike = this.constantBool(true, "ability_removal"),
  ): BoolVar {
    this.assertBuilding();
    const roleRef = roleName(role);
    const ability = this.hasAbilityAt(player, roleRef, timing);
    this.addImplication(active, ability.not());
    addMapValue(this.abilityRemovals, this.abilityAtKey(timing, player, roleRef), active);
    return ability;
  }

  isDemonAt(player: string, timing?: Timing): BoolVar {
    const demonRoles = [...this.characters.entries()]
      .filter(([, character]) => roleCharacterType(character) === CharacterType.Demon)
      .map(([role]) => role);
    return this.anyOf(
      demonRoles.map((role) => this.hasAbilityAt(player, role, timing)),
      `${player}_demon_at_${timing ?? DEFAULT_TIMING_KEY}`,
    );
  }

  isDroisonedAt(player: string, timing: Timing): BoolVar {
    const sources: BoolLike[] = [this.droisoned(player, timing), this.globalDrunk(player)];
    if (this.characters.has("Drunk")) {
      sources.push(this.characterAt(player, "Drunk", timing));
      if (this.characters.has("Hermit")) sources.push(this.characterAt(player, "Hermit", timing));
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

  soberAndHealthyBeforeCharacterChange(player: string, timing: Timing): BoolVar {
    const intrinsic = ["Drunk", ...(this.characters.has("Drunk") ? ["Hermit"] : [])]
      .filter((role) => this.characters.has(role))
      .map((role) => this.characterBefore(player, role, timing));
    return this.not(
      this.anyOf(
        [
          this.droisoned(player, timing),
          this.globalDrunk(player),
          this.noDashiiPoisonedAt(player, timing),
          ...intrinsic,
        ],
        "unhealthy_before_character_change",
      ),
      "healthy_before_character_change",
    );
  }

  soberAndHealthyBeforeOwnDrunking(
    player: string,
    timing: Timing,
    ownDrunkSources: readonly BoolLike[],
    name: string,
  ): BoolVar {
    this.checkPlayer(player);
    const variable = this.newBool(name);
    this.preDroisonHealthQueries.push({
      player,
      timing,
      excludedPoisonSourceIds: new Set(),
      excludedSourceIds: new Set(ownDrunkSources.map((source) => Math.abs(lit(source)))),
      variable,
    });
    return variable;
  }

  soberAndHealthyBeforeOwnPoisoning(
    player: string,
    timing: Timing,
    ownPoisonSources: readonly BoolLike[],
    name: string,
  ): BoolVar {
    this.checkPlayer(player);
    const variable = this.newBool(name);
    this.preDroisonHealthQueries.push({
      player,
      timing,
      excludedPoisonSourceIds: new Set(ownPoisonSources.map((source) => Math.abs(lit(source)))),
      excludedSourceIds: new Set(),
      variable,
    });
    return variable;
  }

  addRolePoisonChoice(
    role: RoleRef,
    timing: Timing,
    affectedTimings: readonly Timing[],
    activeIf: BoolLike,
    sourceName: string,
  ): {
    readonly active: BoolLike;
    readonly choiceActive: BoolLike;
    readonly healthyRoleInPlay: BoolLike;
    readonly activeTargetsAtChoiceTiming: ReadonlyMap<string, BoolLike>;
    readonly targets: ReadonlyMap<string, BoolLike>;
  } {
    const roleRef = roleName(role);
    this.checkRole(roleRef);
    const active = this.newBool(`${sourceName}_active`);
    const choiceActive = this.newBool(`${sourceName}_choice_active`);
    const targets = select(this, this.players, choiceActive, sourceName, 1);
    const activeTargetsByTimingPlayer = new Map<string, BoolLike>();
    for (const affectedTiming of affectedTimings) {
      this.registerActivePoisonSource(affectedTiming, active);
      for (const [player, target] of targets) {
        const activeTarget = this.allOf(
          [active, target],
          `${sourceName}_${affectedTiming}_${slug(player)}_active_target`,
        );
        activeTargetsByTimingPlayer.set(this.timingPlayerKey(affectedTiming, player), activeTarget);
        this.registerPoisonSourceTarget(player, affectedTiming, activeTarget);
      }
    }
    const healthyRoleHolders = this.players.map((player) =>
      this.allOf(
        [
          this.hasAbilityAt(player, roleRef, timing),
          this.soberAndHealthyBeforeOwnPoisoning(
            player,
            timing,
            [activeTargetsByTimingPlayer.get(this.timingPlayerKey(timing, player))].filter(
              (source): source is BoolLike => source !== undefined,
            ),
            `${sourceName}_${slug(player)}_healthy_before_own_poisoning`,
          ),
        ],
        `${sourceName}_${slug(player)}_healthy_role_holder`,
      ),
    );
    const healthyRoleInPlay = this.anyOf(healthyRoleHolders, `${sourceName}_healthy_role_in_play`);
    const shouldBeActive = this.allOf([healthyRoleInPlay, choiceActive], `${sourceName}_should_be_active`);
    const shouldChoose = this.allOf(
      [
        this.anyOf(
          this.players.map((player) => this.hasAbilityAt(player, roleRef, timing)),
          `${sourceName}_role_in_play`,
        ),
        activeIf,
      ],
      `${sourceName}_should_choose`,
    );
    this.equate(choiceActive, shouldChoose);
    this.equate(active, shouldBeActive);
    return {
      active,
      choiceActive,
      healthyRoleInPlay,
      activeTargetsAtChoiceTiming: new Map(
        this.players.flatMap((player) => {
          const target = activeTargetsByTimingPlayer.get(this.timingPlayerKey(timing, player));
          return target === undefined ? [] : [[player, target] as const];
        }),
      ),
      targets,
    };
  }

  registersAsEvil(player: string, name: string, timing = this.observationTiming ?? night(1)): BoolVar {
    this.assertBuilding();
    return this.registersAsAlignment(player, Alignment.Evil, name, timing);
  }

  registersAsGood(player: string, name: string, timing = this.observationTiming ?? night(1)): BoolVar {
    this.assertBuilding();
    return this.registersAsAlignment(player, Alignment.Good, name, timing);
  }

  registersAsCharacterType(
    player: string,
    type: CharacterType,
    name: string,
    timing = this.observationTiming ?? night(1),
  ): BoolVar {
    this.assertBuilding();
    return this.registersAsCharacterTypeAt(player, type, timing, name);
  }

  private registration(
    player: string,
    timing: Timing,
    name: string,
    actual: BoolLike,
    flexibleRoles: readonly string[],
  ): BoolVar {
    const result = this.newBool(name);
    const flexibility = this.allOf(
      [
        this.anyOf(
          flexibleRoles.map((role) => this.characterAt(player, role, timing)),
          `${name}_flexible_character`,
        ),
        // The Hermit keeps its other Outsider abilities while it has the Drunk ability.
        // External drunkenness or poison disables these abilities (Hermit oldid=2805).
        this.anyOf(
          [
            this.soberAndHealthy(player, timing),
            this.characters.has("Hermit") && this.characters.has("Drunk")
              ? this.allOf(
                  [
                    this.characterAt(player, "Hermit", timing),
                    this.droisoned(player, timing).not(),
                    this.globalDrunk(player).not(),
                    this.noDashiiPoisonedAt(player, timing).not(),
                  ],
                  `${name}_hermit_outsider_ability`,
                )
              : this.constantBool(false, "no_hermit_exception"),
          ],
          `${name}_registration_health`,
        ),
      ],
      `${name}_registration_ability_active`,
    );
    this.addImplication(this.allOf([flexibility.not(), actual], `${name}_normal_positive`), result);
    this.addImplication(
      this.allOf([flexibility.not(), this.not(actual, `${name}_actual_false`)], `${name}_normal_negative`),
      result.not(),
    );
    return result;
  }

  registersAsCharacterTypeAt(player: string, type: CharacterType, timing: Timing, name: string): BoolVar {
    this.assertBuilding();
    return this.registration(
      player,
      timing,
      name,
      this.hasCharacterTypeAt(player, type, timing),
      [...this.characters.keys()].filter((role) => this.roleCanFlexiblyRegisterAsType(role, type)),
    );
  }

  registersAsRole(player: string, role: RoleRef, name: string, timing = this.observationTiming ?? night(1)): BoolVar {
    this.assertBuilding();
    return this.registersAsRoleAt(player, role, timing, name);
  }

  registersAsRoleAt(player: string, role: RoleRef, timing: Timing, name: string): BoolVar {
    this.assertBuilding();
    const observed = roleName(role);
    this.checkRole(observed);
    return this.registration(
      player,
      timing,
      name,
      this.characterAt(player, observed, timing),
      [...this.characters.keys()].filter((actual) => this.roleCanFlexiblyRegisterAsRole(actual, observed)),
    );
  }

  registeredEvilCount(players: readonly string[], count: number, name: string): BoolVar {
    this.assertBuilding();
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
    this.assertBuilding();
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
    this.assertBuilding();
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
    this.assertBuilding();
    const roleRef = roleName(claim.role);
    const claimTiming = claim.timing;
    const claimTimingName = claimTiming;
    const activeRole = this.hasAbilityAt(claim.player, roleRef, claimTiming);
    this.addImplication(
      this.allOf(
        [this.actualIs(claim.player, roleRef), this.isGoodAt(claim.player, claimTiming)],
        "truthful_starting_character_report",
      ),
      this.anyOf(
        [
          activeRole,
          ...["Drunk", "Marionette"]
            .filter((role) => this.characters.has(role))
            .map((role) => this.characterAt(claim.player, role, claimTiming)),
        ],
        "possesses_or_believes_reported_ability",
      ),
    );
    const healthy = this.soberAndHealthy(claim.player, claimTiming);
    const honest = this.hasAlignmentOverrideAt(claim.player, claimTiming)
      ? this.isGoodAt(claim.player, claimTiming)
      : undefined;
    const activeHealthy = this.allOf(
      honest === undefined ? [activeRole, healthy] : [activeRole, healthy, honest],
      honest === undefined
        ? `${claim.player}_${roleRef}_${claimTimingName}_sober_healthy_claim`
        : `${claim.player}_${roleRef}_${claimTimingName}_sober_healthy_honest_claim`,
    );
    const vortoxAffected = this.infoClaimAffectedByVortox(roleRef) || (claim.vortoxAffected ?? false);
    this.recordInfoMalfunctions(
      claim.player,
      roleRef,
      claimTiming,
      activeRole,
      honest,
      claim.learned,
      vortoxAffected,
      claim.malfunctionLearned,
    );

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
      this.allOf(
        honest === undefined ? [activeRole, activeVortox] : [activeRole, honest, activeVortox],
        `${claim.player}_${roleRef}_${claimTimingName}_vortox`,
      ),
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

  recordAbilityMalfunction(player: string, timing: Timing, malfunction: BoolLike): void {
    this.assertBuilding();
    this.checkPlayer(player);
    const players = this.malfunctions.get(timing) ?? new Map<string, BoolLike[]>();
    players.set(player, [...(players.get(player) ?? []), malfunction]);
    this.malfunctions.set(timing, players);
  }

  infoMalfunctions(timing: Timing, observer?: string): readonly BoolVar[] {
    const round = Number(timing.split("_")[1]);
    const interval = timing.startsWith("night_") && round > 1 ? [`day_${round - 1}`, timing] : [timing];
    return this.players
      .filter((player) => player !== observer)
      .map((player) =>
        this.anyOf(
          interval.flatMap((when) => this.malfunctions.get(when)?.get(player) ?? []),
          `${timing}_${player}_abnormal`,
        ),
      );
  }

  malfunctionCountAt(timing: Timing, count: number, name: string, observer?: string): BoolVar {
    const variable = this.newBool(name);
    this.malfunctionQueries.push({ timing, count, observer, variable });
    return variable;
  }

  private applyMalfunctionConstraints(): void {
    for (const query of this.malfunctionQueries) {
      const count = this.boolSumEquals(
        this.infoMalfunctions(query.timing, query.observer),
        query.count,
        "abnormal_player_count",
      );
      this.equate(query.variable, count);
    }
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

  /** Complete the source sets once. Each solver call uses the same fixed set of constraints. */
  finalize(): SatProblem {
    if (this.prepared !== undefined) return this.prepared;
    const started = performance.now();
    this.applyDefaultXaanPoisoningConstraints();
    const healthConstraints = this.collectHealthConstraints();
    this.resolveEffects();
    for (const [variable, healthy] of healthConstraints) this.equate(variable, healthy);
    this.resolveActions();
    this.resolveAbilities();
    this.resolveAlignment();
    this.applyMalfunctionConstraints();
    this.trace.finalize();
    const problem = super.finalize();
    this.finalizeMs = performance.now() - started;
    return problem;
  }

  async solveAll(options: { readonly limit?: number } = {}): Promise<World[]> {
    const result = await this.solve(options);
    if (result.status === "unknown") throw new Error(result.reason);
    return [...result.worlds];
  }

  async solve(options: { readonly limit?: number } = {}): Promise<SolveReport> {
    if (options.limit !== undefined && (!Number.isSafeInteger(options.limit) || options.limit < 1))
      throw new Error("Solution limit must be a positive integer.");
    const problem = this.finalize();
    return enumerateWorlds(
      problem,
      this.backend,
      [...this.actual.values()].map((variable) => variable.id),
      (model) => this.decodeWorld(model),
      this.finalizeMs,
      options.limit,
    );
  }

  private decodeWorld(model: ReadonlySet<number>): World {
    const actual = new Map<string, string>();
    for (const player of this.players) {
      const matching = [...this.characters.keys()].filter((role) => model.has(this.actualIs(player, role).id));
      if (matching.length !== 1) throw new Error(`Expected exactly one actual character for ${player}.`);
      actual.set(player, matching[0] as string);
    }
    const poisonedByTiming = flavorByTiming(
      model,
      [this.poisonSourceTargetsByTimingPlayer, this.poisonOverridesByTimingPlayer],
      this.poisonQueryVars,
    );
    for (const timing of new Set(
      [...this.poisonQueryVars.entries()]
        .filter(([, variable]) => this.explicitDroisonTrue.has(variable.id))
        .map(([key]) => key.split("\u0000")[0] as string),
    )) {
      poisonedByTiming.set(
        timing,
        new Set(
          [...this.poisonQueryVars.entries()]
            .filter(
              ([key, variable]) =>
                key.startsWith(`${timing}\u0000`) &&
                this.explicitDroisonTrue.has(variable.id) &&
                model.has(variable.id),
            )
            .map(([key]) => key.split("\u0000")[1] as string),
        ),
      );
    }
    const poisoned = poisonedByTiming.get(DEFAULT_TIMING_KEY) ?? new Set<string>();
    const drunkByTiming = flavorByTiming(model, [this.drunkSourceTargetsByTimingPlayer], this.drunkQueryVars);
    const globallyDrunk = new Set(
      [...this.globalDrunkVars.entries()].filter(([, variable]) => model.has(variable.id)).map(([player]) => player),
    );
    return new World(
      actual,
      new Map(this.apparentRoles),
      poisoned,
      poisonedByTiming,
      globallyDrunk,
      drunkByTiming,
      this.trace.decode(model, actual),
      this.decodeActions(model),
    );
  }

  private resolveAlignment(): void {
    for (const [key, variable] of this.goodAtVars) {
      const [, player] = key.split("\u0000") as [string, string];
      const source = this.goodAtSources.get(key) ?? this.isGood(player);
      this.equate(variable, source);
    }
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

  private abilityAtKey(timing: string, player: string, role: string): string {
    return keyOf(["role_at", timing, player, role]);
  }

  private registersAsAlignment(player: string, alignment: Alignment, name: string, timing: Timing): BoolVar {
    this.assertBuilding();
    return this.registration(
      player,
      timing,
      name,
      alignment === Alignment.Good ? this.isGoodAt(player, timing) : this.isEvilAt(player, timing),
      [...this.characters.keys()].filter((role) => this.roleCanFlexiblyRegisterAsAlignment(role)),
    );
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
        this.hasAbilityAt(demon, noDashiiRole, timing),
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
    honest: BoolVar | undefined,
    reportedInfo: BoolLike,
    vortoxAffected: boolean,
    registrationIndependentInfo?: BoolLike,
  ): void {
    this.assertBuilding();
    const timingName = timing;
    const honesty = honest === undefined ? [] : [honest];
    const falseInfo = this.not(
      registrationIndependentInfo ?? reportedInfo,
      `${player}_${role}_${timingName}_reported_info_false`,
    );
    const actualDrunkUsingClaimedAbility =
      this.characters.has("Drunk") && this.characters.has("Mathematician")
        ? this.actualIs(player, "Drunk")
        : this.constantBool(false, `${player}_${role}_${timingName}_no_mathematician_drunk_jinx`);
    const causes: BoolVar[] = [
      this.allOf(
        [activeRole, ...honesty, this.isDroisonedAt(player, timing), falseInfo],
        `${player}_${role}_${timingName}_droison_malfunction`,
      ),
      this.allOf(
        [activeRole, ...honesty, this.noDashiiPoisonedAt(player, timing), falseInfo],
        `${player}_${role}_${timingName}_nodashii_malfunction`,
      ),
      this.allOf(
        [...honesty, actualDrunkUsingClaimedAbility, falseInfo],
        `${player}_${role}_${timingName}_drunk_role_malfunction`,
      ),
    ];
    if (registrationIndependentInfo !== undefined) {
      causes.push(
        this.allOf(
          [
            activeRole,
            ...honesty,
            reportedInfo,
            this.not(
              registrationIndependentInfo,
              `${player}_${role}_${timingName}_registration_independent_info_false`,
            ),
          ],
          `${player}_${role}_${timingName}_registration_malfunction`,
        ),
      );
    }
    if (vortoxAffected && this.characters.has(roleName("Vortox"))) {
      causes.push(
        this.allOf(
          [activeRole, ...honesty, this.roleSoberAndHealthyAt("Vortox", timing, `${player}_${role}_vortox`), falseInfo],
          `${player}_${role}_${timingName}_vortox_malfunction`,
        ),
      );
    }
    const malfunction = this.anyOf(causes, `${player}_${role}_${timingName}_info_malfunction`);
    this.recordAbilityMalfunction(player, timing, malfunction);
  }

  roleSoberAndHealthyAt(role: RoleRef, timing: Timing, name: string): BoolVar {
    const roleRef = roleName(role);
    return this.anyOf(
      this.players.map((player) =>
        this.allOf(
          [this.hasAbilityAt(player, roleRef, timing), this.soberAndHealthy(player, timing)],
          `${name}_${player}_${timing}_sober_healthy`,
        ),
      ),
      `${name}_${timing}_sober_healthy_in_play`,
    );
  }

  private resolveAbilities(): void {
    for (const [key, roleAt] of this.abilityAtVars.entries()) {
      const [, timing, player, role] = key.split("\u0000") as [string, Timing, string, string];
      const acquired = this.acquiredAbilities
        .filter(
          (ability) =>
            ability.player === player && ability.role === role && timingOrder(ability.timing) <= timingOrder(timing),
        )
        .map((ability) =>
          ability.sourceRole === undefined
            ? ability.active
            : this.allOf(
                [
                  ability.active,
                  this.characterAt(player, ability.sourceRole, timing),
                  this.trace.retainedThrough(player, ability.sourceRole, ability.timing, timing),
                ],
                "retains_acquired_ability",
              ),
        );
      const removals = [...this.abilityRemovals.entries()].flatMap(([removalKey, sources]) => {
        const [, when, who, what] = removalKey.split("\u0000") as [string, Timing, string, string];
        return who === player && what === role && timingOrder(when) <= timingOrder(timing) ? sources : [];
      });
      const state = this.allOf(
        [
          this.anyOf([this.characterAt(player, role, timing), ...acquired], "possesses_ability"),
          this.anyOf(removals, "ability_removed").not(),
        ],
        "ability_at",
      );
      this.equate(roleAt, state);
    }
  }

  private constrainToAnySource(variable: BoolVar, sources: readonly BoolLike[]): void {
    for (const source of sources) this.addImplication(source, variable);
    if (!this.explicitDroisonTrue.has(variable.id)) this.addClause([variable.not(), ...sources.map(lit)]);
  }

  private resolveActions(): void {
    for (const query of this.abilityUsedBeforeQueries.values()) {
      const queryOrder = timingOrder(query.timing);
      const sources = this.abilityUses
        .filter((use) => use.player === query.player && use.role === query.role && timingOrder(use.timing) < queryOrder)
        .map((use) => use.activeIf);
      this.constrainToAnySource(query.variable, sources);
    }
    for (const [key, query] of this.wakePreventionQueries) {
      this.constrainToAnySource(query, this.wakePreventionSources.get(key) ?? []);
    }
    for (const [key, query] of this.conditionalWakeQueries) {
      this.constrainToAnySource(query, this.conditionalWakeSources.get(key) ?? []);
    }
    for (const query of this.abilityTargetQueries.values()) {
      const sources = this.abilityTargets
        .filter(
          (target) =>
            target.actor === query.actor &&
            target.role === query.role &&
            target.target === query.target &&
            target.timing === query.timing,
        )
        .map((target) => target.activeIf);
      this.constrainToAnySource(query.variable, sources);
    }
  }

  private resolveEffects(): void {
    this.applyDefaultPoisonCapacityConstraints();
    const predicates: Array<[ReadonlyMap<string, BoolVar>, (key: string) => readonly BoolLike[]]> = [
      [this.poisonQueryVars, (key) => this.poisonSourceFlavor(key)],
      [this.drunkQueryVars, (key) => this.drunkSourceFlavor(key)],
      [this.droisonedVars, (key) => [...this.poisonSourceFlavor(key), ...this.drunkSourceFlavor(key)]],
    ];
    for (const [variables, sources] of predicates)
      for (const [key, variable] of variables) this.constrainToAnySource(variable, sources(key));
    for (const [player, drunk] of this.globalDrunkVars) {
      this.addClause([drunk.not(), ...(this.globalDrunkSourceTargetsByPlayer.get(player) ?? []).map(lit)]);
    }
  }

  private collectHealthConstraints(): readonly (readonly [BoolVar, BoolVar])[] {
    return this.preDroisonHealthQueries.map((query) => {
      const key = this.timingPlayerKey(query.timing, query.player);
      const poisonSources = this.poisonSourceFlavor(key).filter(
        (source) => !query.excludedPoisonSourceIds.has(Math.abs(lit(source))),
      );
      const otherDrunkSources = this.drunkSourceFlavor(key).filter(
        (source) => !query.excludedSourceIds.has(Math.abs(lit(source))),
      );
      const unhealthySources: BoolLike[] = [
        ...poisonSources,
        ...otherDrunkSources,
        this.globalDrunk(query.player),
        this.noDashiiPoisonedAt(query.player, query.timing),
      ];
      if (this.characters.has("Drunk")) {
        unhealthySources.push(this.actualIs(query.player, "Drunk"));
        if (this.characters.has("Hermit")) unhealthySources.push(this.actualIs(query.player, "Hermit"));
      }
      const unhealthy = this.anyOf(
        unhealthySources,
        `${query.player}_unhealthy_before_own_drunking_at_${query.timing}`,
      );
      const healthy = this.not(unhealthy, `${query.player}_healthy_before_own_drunking_at_${query.timing}`);
      return [query.variable, healthy] as const;
    });
  }

  private applyDefaultXaanPoisoningConstraints(): void {
    if (!this.characters.has("Xaan")) return;
    const maxOutsiders = [...this.characters.values()]
      .filter((role) => roleCharacterType(role) === CharacterType.Outsider)
      .reduce((total, role) => total + roleMaxCopies(role), 0);
    for (let count = 1; count <= maxOutsiders; count += 1) {
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

  private applyDefaultPoisonCapacityConstraints(): void {
    const overrideTimings = [...this.poisonOverridesByTimingPlayer.keys()].map(
      (key) => key.split("\u0000")[0] as string,
    );
    const targetTimings = [...this.poisonSourceTargetsByTimingPlayer.keys()].map(
      (key) => key.split("\u0000")[0] as string,
    );
    const timings = new Set([...this.activePoisonSourcesByTiming.keys(), ...overrideTimings, ...targetTimings]);
    for (const timing of timings) {
      const activeSources = this.activePoisonSourcesByTiming.get(timing) ?? [];
      const cappedPoisonedPlayers = this.players.map((player) => {
        const sourceTargets = this.poisonSourceTargetsByTimingPlayer.get(this.timingPlayerKey(timing, player)) ?? [];
        return this.anyOf(sourceTargets, `${timing}_${player}_capacity_counted_poison`);
      });
      this.addCountAtMostCount(cappedPoisonedPlayers, activeSources);
    }
  }
}
