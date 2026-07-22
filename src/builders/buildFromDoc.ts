import { applyClaims, type EmpathNeighborOption, type OracleDeadPlayerOption } from "../model/characters";
import { Alignment, CharacterType, roleAlignment, roleCharacterType, roleName, type RoleRef } from "../model/core";
import type { BoolLike, BOTCModel, Timing } from "../model/model";
import type { SatBackend } from "../model/sat";
import { buildPuzzleModel, type PuzzleSpec } from "../model/setup";
import { isTimelineDeathEvent, type PuzzleDoc } from "../schema/puzzleDoc";
import { compile, type CompileCtx } from "../dsl/compile";
import { buildClaim, type ClaimWithTimelineContext } from "./claim";
import { resolveRoleRef } from "./roleRef";

export function buildFromDoc(doc: PuzzleDoc, backend: SatBackend): BOTCModel {
  const spec: PuzzleSpec = {
    players: doc.players,
    characters: doc.script.map(resolveRoleRef),
    uniqueCharacters: doc.uniqueCharacters,
    setup: doc.setup === "none" || doc.setup === "atheist" ? false : "standard",
  };
  const game = buildPuzzleModel(spec, backend);
  const ctx = { players: doc.players, script: doc.script };
  applyGlobalConstraints(game, doc, ctx);
  if (doc.setup === "atheist") applyAtheistSetup(game, doc);
  applyTimelineConstraints(game, doc);
  if (doc.setup !== "atheist") applyMinstrelSources(game, doc);
  if (doc.setup !== "atheist") applySailorChoiceLegality(game, doc);
  applyConditionalWakeSources(game, doc);
  applyRiotTransformations(game, doc);
  const pukkaContext = doc.setup === "atheist" ? emptyPukkaContext() : applyPukkaPoisonChoices(game, doc);
  let nightDeathTiming = emptyNightDeathTimingContext();
  if (doc.setup !== "atheist") {
    registerDevilsAdvocateTargets(game, doc);
    const godfatherContext = applyGodfatherChoices(game, doc);
    const shabalothContext = registerShabalothChoices(game, doc);
    let goonContext = emptyGoonContext();
    if (doc.script.includes("Goon")) {
      registerDeclaredAbilityTargets(game, doc);
      goonContext = applyGoonInteractions(game, doc);
    }
    applyShabalothChoiceConstraints(game, doc, shabalothContext, goonContext);
    nightDeathTiming = applyNightDeathSourceConstraints(
      game,
      doc,
      ctx,
      pukkaContext,
      godfatherContext,
      goonContext,
      shabalothContext,
    );
    applyResurrectionConstraints(game, doc, nightDeathTiming);
  }
  applyOngoingGameConstraint(game, doc);
  const preNightDeathSnakeCharmerChecks = applyPreNightDeathSnakeCharmerChecks(game, doc);
  const timelineClaims = doc.claims.map((claim, index) =>
    removePreNightDeathSnakeCharmerChecks(claim, index, preNightDeathSnakeCharmerChecks),
  );
  const claims = timelineClaims.map((claim) => applyTimelineClaimContext(claim, doc, game, nightDeathTiming));
  const ordinaryClaims = claims.filter((claim) => !usesMalfunctionCount(claim)).map((claim) => buildClaim(claim, ctx));
  const malfunctionCountClaims = claims
    .filter((claim) => usesMalfunctionCount(claim))
    .map((claim) => buildClaim(claim, ctx));
  const claimOptions = doc.setup === "atheist" ? { info: () => undefined } : {};
  if (doc.setup !== "atheist") {
    applyPuzzlemasterSources(game, doc);
    applySweetheartSources(game, doc);
  }
  applyClaims(game, ordinaryClaims, claimOptions);
  applyClaims(game, malfunctionCountClaims, claimOptions);
  if (doc.script.includes("Assassin")) game.enforceAbilityUseLimit("Assassin", 1);
  if (doc.setup !== "atheist") {
    applyPhilosopherDrunking(game, doc);
    applyChangedRoleClaimExplanations(game, doc);
    applyXaanActivity(game, doc);
    applyVigormortisPoisonSources(game, doc, nightDeathTiming);
    applyPoisonerSources(game, doc, nightDeathTiming);
    applyWidowSources(game, doc);
    applyWidowCallClaims(game, doc);
    applyEvilTwinKnowledgeClaims(game, doc);
    applyVillageIdiotSources(game, doc);
  }
  return game;
}

function applyMinstrelSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Minstrel")) return;
  for (const event of doc.timeline ?? []) {
    if (event.type !== "execution") continue;
    const timing = event.timing as Timing;
    const match = /^day_(\d+)$/.exec(timing);
    if (match === null) continue;
    const round = Number(match[1]);
    const executedMinion = game.anyOf(
      event.players.map((player) => characterTypeBeforeEvent(game, doc, player, CharacterType.Minion, event)),
      `${timing}_executed_player_is_minion_for_minstrel`,
    );
    for (const minstrel of livingPlayersBeforeDeathEvent(doc, event)) {
      const active = game.allOf(
        [
          executedMinion,
          roleAtBeforeEvent(game, doc, minstrel, "Minstrel", event),
          game.soberAndHealthy(minstrel, healthTimingForDayAbility(timing)),
        ],
        `${timing}_${slug(minstrel)}_minstrel_drunking_active`,
      );
      const affectedTimings: Timing[] = [timing, `night_${round + 1}` as Timing, `day_${round + 1}` as Timing];
      for (const player of doc.players) {
        if (player !== minstrel) game.addTimedDrunkSource(player, affectedTimings, active);
      }
    }
  }
}

function applySailorChoiceLegality(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Sailor")) return;
  for (const claim of doc.claims) {
    if (claim.type !== "Sailor") continue;
    for (const [index, choice] of (claim.choices ?? []).entries()) {
      const timing = choice.timing as Timing | undefined;
      const legal =
        timing !== undefined &&
        /^night_\d+$/.test(timing) &&
        livingPlayersAt(doc, timing).includes(claim.name) &&
        livingPlayersAt(doc, timing).includes(choice.player);
      if (timing === undefined) continue;
      game.addImplication(
        game.hasRoleAt(claim.name, "Sailor", timing),
        game.constantBool(legal, `${timing}_${slug(claim.name)}_sailor_choice_${index + 1}_legal`),
      );
    }
  }
}

interface PukkaContext {
  readonly poisonedBeforeResolutionByTiming: ReadonlyMap<Timing, ReadonlyMap<string, BoolLike>>;
  readonly resolvesByTiming: ReadonlyMap<Timing, BoolLike>;
}

function emptyPukkaContext(): PukkaContext {
  return { poisonedBeforeResolutionByTiming: new Map(), resolvesByTiming: new Map() };
}

interface GodfatherChoice {
  readonly actor: string;
  readonly timing: Timing;
  readonly active: BoolLike;
  readonly targets: ReadonlyMap<string, BoolLike>;
}

interface GodfatherContext {
  readonly choices: readonly GodfatherChoice[];
}

function applyGodfatherChoices(game: BOTCModel, doc: PuzzleDoc): GodfatherContext {
  if (!doc.script.includes("Godfather")) return { choices: [] };
  const choices: GodfatherChoice[] = [];
  for (const timing of allNightTimings(doc)) {
    const previousDay = previousDayForNight(timing);
    if (previousDay === undefined) continue;
    const outsiderDied = outsiderDiedDuring(game, doc, previousDay, `${timing}_godfather_revenge`);
    const publicDeaths = nightDeathPlayersAt(doc, timing);
    const living = livingPlayersAt(doc, timing);
    for (const actor of living) {
      const choiceActive = game.allOf(
        [game.hasRoleAt(actor, "Godfather", timing), outsiderDied],
        `${timing}_${slug(actor)}_godfather_revenge_choice_active`,
      );
      const active = game.allOf(
        [choiceActive, game.soberAndHealthy(actor, timing)],
        `${timing}_${slug(actor)}_healthy_godfather_revenge_effect_active`,
      );
      const declaredTarget = doc.claims
        .flatMap((claim) => (claim.type === "Godfather" && claim.name === actor ? (claim.choices ?? []) : []))
        .find((choice) => choice.timing === timing)?.player;
      const targets = new Map<string, BoolLike>();
      const selections: BoolLike[] = [];
      for (const target of living) {
        const selected = game.newBool(`${timing}_${slug(actor)}_godfather_targets_${slug(target)}`);
        const effectiveTarget = game.allOf(
          [active, selected],
          `${timing}_${slug(actor)}_healthy_godfather_kills_${slug(target)}`,
        );
        targets.set(target, effectiveTarget);
        selections.push(selected);
        game.addImplication(selected, choiceActive);
        if (declaredTarget !== undefined) {
          if (target === declaredTarget) game.addImplication(choiceActive, selected);
          else game.addFalse(selected);
        }
        game.registerAbilityTarget(actor, "Godfather", target, timing, selected, nightActionOrder("Godfather"));
        if (!publicDeaths.has(target)) {
          game.addImplication(
            effectiveTarget,
            game.anyOf(
              [deathProtectionAt(game, doc, target, timing), innkeeperProtectionAt(game, doc, target, timing)],
              `${timing}_${slug(target)}_protected_from_unrecorded_godfather_death`,
            ),
          );
        }
      }
      if (declaredTarget !== undefined && !living.includes(declaredTarget)) game.addFalse(choiceActive);
      game.addEnforcedExactlyN(selections, 1, choiceActive);
      game.addEnforcedExactlyN(selections, 0, choiceActive.not());
      choices.push({ actor, timing, active, targets });
    }
  }
  return { choices };
}

function outsiderDiedDuring(game: BOTCModel, doc: PuzzleDoc, timing: Timing, name: string): BoolLike {
  return game.anyOf(
    (doc.timeline ?? []).flatMap((event) =>
      event.timing === timing && isTimelineDeathEvent(event)
        ? event.players.map((player) => game.hasCharacterType(player, CharacterType.Outsider))
        : [],
    ),
    `${name}_outsider_died`,
  );
}

function applyPukkaPoisonChoices(game: BOTCModel, doc: PuzzleDoc): PukkaContext {
  if (!doc.script.includes("Pukka")) return emptyPukkaContext();
  const choicesByTiming = new Map<
    Timing,
    {
      readonly active: BoolLike;
      readonly choiceActive: BoolLike;
      readonly healthyRoleInPlay: BoolLike;
      readonly activeTargetsAtChoiceTiming: ReadonlyMap<string, BoolLike>;
      readonly targets: ReadonlyMap<string, BoolLike>;
    }
  >();
  const resolvesByTiming = new Map<Timing, BoolLike>();
  for (const timing of allNightTimings(doc)) {
    const match = /^night_(\d+)$/.exec(timing);
    if (match === null) continue;
    const unblocked = game.newBool(`${timing}_pukka_not_blocked`);
    const livingPukka = game.anyOf(
      livingPlayersAt(doc, timing).map((player) => game.hasRoleAt(player, "Pukka", timing)),
      `${timing}_living_pukka`,
    );
    const choice = game.addRolePoisonChoice(
      "Pukka",
      timing,
      [timing],
      game.allOf([livingPukka, unblocked], `${timing}_living_unblocked_pukka_choice`),
      `${timing}_pukka_choice`,
    );
    const blocked = demonKillBlockedAt(game, doc, timing, (player, healthTiming, name) => {
      if (healthTiming !== timing) return game.soberAndHealthy(player, healthTiming);
      const currentPukkaPoison = choice.activeTargetsAtChoiceTiming.get(player);
      return game.soberAndHealthyBeforeOwnPoisoning(
        player,
        timing,
        currentPukkaPoison === undefined ? [] : [currentPukkaPoison],
        name,
      );
    });
    const notBlocked = game.not(blocked, `${timing}_pukka_wake_not_blocked`);
    game.addImplication(unblocked, notBlocked);
    game.addImplication(notBlocked, unblocked);
    for (const actor of doc.players)
      for (const [target, targeted] of choice.targets) {
        game.registerAbilityTarget(
          actor,
          "Pukka",
          target,
          timing,
          game.allOf(
            [choice.choiceActive, targeted, game.hasRoleAt(actor, "Pukka", timing)],
            `${timing}_${slug(actor)}_pukka_targets_${slug(target)}`,
          ),
          nightActionOrder("Pukka"),
        );
      }
    choicesByTiming.set(timing, choice);
    resolvesByTiming.set(
      timing,
      game.allOf([livingPukka, choice.healthyRoleInPlay], `${timing}_pukka_resolves_existing_poison`),
    );
  }

  const poisonedBeforeResolutionByTiming = new Map<Timing, Map<string, BoolLike>>();
  const poisonSeeds: Array<{ readonly originIndex: number; readonly targets: ReadonlyMap<string, BoolLike> }> = [];
  const nightTimings = [...choicesByTiming.keys()];
  for (const [timingIndex, timing] of nightTimings.entries()) {
    const choice = choicesByTiming.get(timing);
    const resolves = resolvesByTiming.get(timing);
    if (choice === undefined || resolves === undefined) continue;
    const match = /^night_(\d+)$/.exec(timing);
    if (match === null) continue;
    const dayTiming = `day_${match[1]}` as Timing;
    const livingAtNight = new Set(livingPlayersAt(doc, timing));
    const livingAfterNight = new Set(livingPlayersAt(doc, dayTiming));
    const oldPoison = new Map<string, BoolLike>();

    for (const player of livingAtNight) {
      const carriedTargets = poisonSeeds.flatMap((seed): BoolLike[] => {
        const seededTarget = seed.targets.get(player);
        if (seededTarget === undefined) return [];
        const survivedResolutions = nightTimings
          .slice(seed.originIndex + 1, timingIndex)
          .map((interveningTiming) =>
            game.not(
              resolvesByTiming.get(interveningTiming) as BoolLike,
              `${timing}_${interveningTiming}_pukka_poison_not_resolved`,
            ),
          );
        return [game.allOf([seededTarget, ...survivedResolutions], `${timing}_${slug(player)}_pukka_poison_carries`)];
      });
      if (carriedTargets.length > 0) {
        oldPoison.set(
          player,
          carriedTargets.length === 1
            ? (carriedTargets[0] as BoolLike)
            : game.anyOf(carriedTargets, `${timing}_pukka_previously_poisoned_${slug(player)}`),
        );
      }
    }

    if (oldPoison.size > 0) {
      game.addPoisonState(timing, oldPoison, `${timing}_carried_pukka_poison`);
      poisonedBeforeResolutionByTiming.set(timing, oldPoison);
    }

    const newPoison = new Map<string, BoolLike>();
    const poisonAfterResolution = new Map<string, BoolLike>();
    for (const player of livingAfterNight) {
      const selected = choice.targets.get(player);
      if (selected === undefined) continue;
      const oldTargetResolves = game.allOf(
        [resolves, oldPoison.get(player) ?? game.constantBool(false, `${timing}_${slug(player)}_not_old_pukka_target`)],
        `${timing}_${slug(player)}_old_pukka_target_resolves`,
      );
      const newlyPoisoned = game.allOf(
        [
          choice.active,
          selected,
          game.not(oldTargetResolves, `${timing}_${slug(player)}_not_cleared_after_pukka_death`),
        ],
        `${timing}_${slug(player)}_new_pukka_poison_persists`,
      );
      newPoison.set(player, newlyPoisoned);
      const oldPoisonPersists = game.allOf(
        [
          oldPoison.get(player) ?? game.constantBool(false, `${timing}_${slug(player)}_no_old_pukka_poison`),
          game.not(resolves, `${timing}_pukka_does_not_resolve_old_poison`),
        ],
        `${dayTiming}_${slug(player)}_old_pukka_poison_persists`,
      );
      poisonAfterResolution.set(
        player,
        game.anyOf([newlyPoisoned, oldPoisonPersists], `${dayTiming}_pukka_poisons_${slug(player)}`),
      );
    }
    game.addPoisonState(dayTiming, poisonAfterResolution, `${dayTiming}_pukka_poison`);
    poisonSeeds.push({ originIndex: timingIndex, targets: newPoison });
  }

  for (const [timing, poisonedPlayers] of poisonedBeforeResolutionByTiming) {
    const resolves = resolvesByTiming.get(timing);
    if (resolves === undefined) continue;
    const publicDeaths = nightDeathPlayersAt(doc, timing);
    const livingPlayers = new Set(livingPlayersAt(doc, timing));
    for (const [player, poisoned] of poisonedPlayers) {
      if (!livingPlayers.has(player) || publicDeaths.has(player)) continue;
      const shouldDie = game.allOf([resolves, poisoned], `${timing}_pukka_unrecorded_death_of_${slug(player)}`);
      const soldierProtected = doc.script.includes("Soldier")
        ? game.allOf(
            [game.hasRoleAt(player, "Soldier", timing), game.soberAndHealthy(player, timing)],
            `${timing}_${slug(player)}_soldier_protected_from_pukka`,
          )
        : game.constantBool(false, `${timing}_${slug(player)}_no_soldier_protection_from_pukka`);
      game.addImplication(
        shouldDie,
        game.anyOf(
          [
            deathProtectionAt(game, doc, player, timing),
            innkeeperProtectionAt(game, doc, player, timing),
            soldierProtected,
          ],
          `${timing}_${slug(player)}_protected_from_pukka_death`,
        ),
      );
    }
  }
  return { poisonedBeforeResolutionByTiming, resolvesByTiming };
}

function registerDevilsAdvocateTargets(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Devil's Advocate")) return;
  const choicesByActorTiming = new Map<string, Map<string, BoolLike>>();
  for (const timing of allNightTimings(doc)) {
    const living = livingPlayersAt(doc, timing);
    for (const actor of living) {
      const active = game.hasRoleAt(actor, "Devil's Advocate", timing);
      const declaredTarget = doc.claims
        .flatMap((claim) => (claim.type === "Devil's Advocate" && claim.name === actor ? (claim.choices ?? []) : []))
        .find((choice) => choice.timing === timing)?.player;
      const targets = new Map<string, BoolLike>();
      for (const target of living) {
        const selected = game.newBool(`${timing}_${slug(actor)}_devils_advocate_targets_${slug(target)}`);
        targets.set(target, selected);
        game.addImplication(selected, active);
        if (declaredTarget !== undefined) {
          if (target === declaredTarget) game.addImplication(active, selected);
          else game.addFalse(selected);
        }
        game.registerAbilityTarget(
          actor,
          "Devil's Advocate",
          target,
          timing,
          selected,
          nightActionOrder("Devil's Advocate"),
        );
      }
      game.addEnforcedExactlyN([...targets.values()], 1, active);
      game.addEnforcedExactlyN([...targets.values()], 0, active.not());
      choicesByActorTiming.set(`${actor}\u0000${timing}`, targets);
    }
  }
  for (const timing of allNightTimings(doc)) {
    const priorTiming = previousNight(timing);
    if (priorTiming === undefined) continue;
    for (const actor of doc.players) {
      const current = choicesByActorTiming.get(`${actor}\u0000${timing}`);
      const prior = choicesByActorTiming.get(`${actor}\u0000${priorTiming}`);
      if (current === undefined || prior === undefined) continue;
      for (const target of doc.players) {
        const currentTarget = current.get(target);
        const priorTarget = prior.get(target);
        if (currentTarget !== undefined && priorTarget !== undefined)
          game.addImplication(
            currentTarget,
            game.not(priorTarget, `${timing}_${slug(actor)}_da_changes_target_${slug(target)}`),
          );
      }
    }
  }
}

function registerDeclaredAbilityTargets(game: BOTCModel, doc: PuzzleDoc): void {
  const register = (actor: string, role: string, target: string, timing: string | undefined): void => {
    if (!/^(night)_\d+$/.test(timing ?? "") || !doc.players.includes(target)) return;
    const resolvedTiming = timing as Timing;
    if (!livingPlayersAt(doc, resolvedTiming).includes(actor)) return;
    game.registerAbilityTarget(
      actor,
      role,
      target,
      resolvedTiming,
      game.hasRoleAt(actor, role, resolvedTiming),
      nightActionOrder(role),
    );
  };
  for (const claim of doc.claims) {
    switch (claim.type) {
      case "Assassin":
        if (claim.target !== undefined) register(claim.name, "Assassin", claim.target, claim.timing);
        break;
      case "Chambermaid":
        for (const check of claim.checks ?? []) {
          register(claim.name, "Chambermaid", check.left, check.timing);
          register(claim.name, "Chambermaid", check.right, check.timing);
        }
        break;
      case "Devil's Advocate":
        break;
      case "Exorcist":
        for (const choice of claim.choices ?? []) register(claim.name, "Exorcist", choice.player, choice.timing);
        break;
      case "Gambler":
        for (const guess of claim.guesses ?? []) register(claim.name, "Gambler", guess.player, guess.timing);
        break;
      case "Godfather":
        break;
      case "Innkeeper":
        for (const choice of claim.choices ?? [])
          for (const target of choice.players) register(claim.name, "Innkeeper", target, choice.timing);
        break;
      case "Professor":
        if (claim.target !== undefined) register(claim.name, "Professor", claim.target, claim.timing);
        break;
      case "Sailor":
        for (const choice of claim.choices ?? []) register(claim.name, "Sailor", choice.player, choice.timing);
        break;
    }
  }
}

interface GoonContext {
  readonly drunkSourcesByActorTiming: ReadonlyMap<string, readonly BoolLike[]>;
  readonly targetings: readonly { readonly timing: Timing; readonly order: number; readonly active: BoolLike }[];
}

interface ShabalothChoice {
  readonly actor: string;
  readonly timing: Timing;
  readonly targets: ReadonlyMap<string, BoolLike>;
}

interface ShabalothContext {
  readonly choices: readonly ShabalothChoice[];
}

function registerShabalothChoices(game: BOTCModel, doc: PuzzleDoc): ShabalothContext {
  const modelsNoDeathNight = (doc.timeline ?? []).some(
    (event) => event.type === "nightDeath" && event.players.length === 0,
  );
  if (!doc.script.includes("Shabaloth") || !modelsNoDeathNight) return { choices: [] };
  const choices: ShabalothChoice[] = [];
  for (const timing of allNightTimings(doc)) {
    for (const actor of livingPlayersAt(doc, timing)) {
      const targets = new Map<string, BoolLike>();
      for (const target of livingPlayersAt(doc, timing)) {
        const selected = game.newBool(`${timing}_${slug(actor)}_shabaloth_targets_${slug(target)}`);
        targets.set(target, selected);
        game.addImplication(selected, game.hasRoleAt(actor, "Shabaloth", timing));
        game.registerAbilityTarget(actor, "Shabaloth", target, timing, selected, nightActionOrder("Shabaloth"));
      }
      choices.push({ actor, timing, targets });
    }
  }
  return { choices };
}

function applyShabalothChoiceConstraints(
  game: BOTCModel,
  doc: PuzzleDoc,
  context: ShabalothContext,
  goonContext: GoonContext,
): void {
  for (const choice of context.choices) {
    const preGoonHealthy = game.soberAndHealthyBeforeOwnDrunking(
      choice.actor,
      choice.timing,
      goonContext.drunkSourcesByActorTiming.get(`${choice.actor}\u0000${choice.timing}`) ?? [],
      `${choice.timing}_${slug(choice.actor)}_shabaloth_healthy_before_targeting_goon`,
    );
    const wakes = game.constantBool(choice.timing !== "night_1", `${choice.timing}_shabaloth_can_wake`);
    const shouldChoose = game.allOf(
      [
        game.hasRoleAt(choice.actor, "Shabaloth", choice.timing),
        preGoonHealthy,
        wakes,
        game.not(
          demonKillBlockedAt(game, doc, choice.timing),
          `${choice.timing}_${slug(choice.actor)}_shabaloth_not_blocked`,
        ),
      ],
      `${choice.timing}_${slug(choice.actor)}_shabaloth_choice_active`,
    );
    game.addEnforcedExactlyN([...choice.targets.values()], 2, shouldChoose);
    game.addEnforcedExactlyN(
      [...choice.targets.values()],
      0,
      game.not(shouldChoose, `${choice.timing}_shabaloth_inactive`),
    );

    const effective = game.allOf(
      [shouldChoose, game.soberAndHealthy(choice.actor, choice.timing)],
      `${choice.timing}_${slug(choice.actor)}_shabaloth_effective`,
    );
    const publicDeaths = nightDeathPlayersAt(doc, choice.timing);
    for (const [target, selected] of choice.targets) {
      if (publicDeaths.has(target)) continue;
      game.addImplication(
        game.allOf([effective, selected], `${choice.timing}_${slug(choice.actor)}_shabaloth_kills_${slug(target)}`),
        game.anyOf(
          [
            deathProtectionAt(game, doc, target, choice.timing),
            innkeeperProtectionAt(game, doc, target, choice.timing),
          ],
          `${choice.timing}_${slug(target)}_protected_from_shabaloth`,
        ),
      );
    }
  }
}

function shabalothTargetedAt(game: BOTCModel, context: ShabalothContext, player: string, timing: Timing): BoolLike {
  return game.anyOf(
    context.choices.flatMap((choice) =>
      choice.timing === timing && choice.targets.has(player) ? [choice.targets.get(player) as BoolLike] : [],
    ),
    `${timing}_shabaloth_targeted_${slug(player)}`,
  );
}

function emptyGoonContext(): GoonContext {
  return { drunkSourcesByActorTiming: new Map(), targetings: [] };
}

function applyGoonInteractions(game: BOTCModel, doc: PuzzleDoc): GoonContext {
  if (!doc.script.includes("Goon")) return emptyGoonContext();
  const actions = [...game.registeredAbilityTargets()].sort(
    (left, right) => phaseStartOrder(left.timing) - phaseStartOrder(right.timing) || left.order - right.order,
  );
  const firstGoonTargets: Array<(typeof actions)[number] & { readonly triggers: BoolLike }> = [];
  const targetings: Array<{ readonly timing: Timing; readonly order: number; readonly active: BoolLike }> = [];
  const drunkSourcesByActorTiming = new Map<string, BoolLike[]>();
  for (const timing of allNightTimings(doc)) {
    const earlier: BoolLike[] = [];
    for (const action of actions.filter((candidate) => candidate.timing === timing)) {
      if (!livingPlayersAt(doc, timing).includes(action.target)) continue;
      const targetsGoon = game.allOf(
        [action.activeIf, game.hasRoleAt(action.target, "Goon", timing)],
        `${timing}_${slug(action.actor)}_${slug(action.role)}_targets_goon_${slug(action.target)}`,
      );
      const triggers = game.allOf(
        [targetsGoon, ...earlier.map((prior) => game.not(prior, `${timing}_prior_goon_target_missed`))],
        `${timing}_${slug(action.actor)}_${slug(action.role)}_first_targets_goon`,
      );
      firstGoonTargets.push({ ...action, triggers });
      targetings.push({ timing, order: action.order, active: targetsGoon });
      earlier.push(targetsGoon);
      const match = /^night_(\d+)$/.exec(timing);
      game.addTimedDrunkSource(
        action.actor,
        match === null ? [timing] : [timing, `day_${match[1]}` as Timing],
        triggers,
      );
      const key = `${action.actor}\u0000${timing}`;
      drunkSourcesByActorTiming.set(key, [...(drunkSourcesByActorTiming.get(key) ?? []), triggers]);
    }
  }

  for (const timing of allNightTimings(doc)) {
    const priorTiming = previousNight(timing);
    for (const player of doc.players) {
      const priorGood = priorTiming === undefined ? game.isGood(player) : game.isGoodAt(player, priorTiming);
      const playerTriggers = firstGoonTargets.filter((target) => target.timing === timing && target.target === player);
      const turnsGood = game.anyOf(
        playerTriggers.map((target) => {
          const actorWasGood =
            priorTiming === undefined ? game.isGood(target.actor) : game.isGoodAt(target.actor, priorTiming);
          return game.allOf([target.triggers, actorWasGood], `${timing}_${slug(player)}_goon_turns_good`);
        }),
        `${timing}_${slug(player)}_goon_good_trigger`,
      );
      const turnsEvil = game.anyOf(
        playerTriggers.map((target) => {
          const actorWasEvil = game.not(
            priorTiming === undefined ? game.isGood(target.actor) : game.isGoodAt(target.actor, priorTiming),
            `${timing}_${slug(target.actor)}_evil_before_goon_choice`,
          );
          return game.allOf([target.triggers, actorWasEvil], `${timing}_${slug(player)}_goon_turns_evil`);
        }),
        `${timing}_${slug(player)}_goon_evil_trigger`,
      );
      const goodAtTiming = game.anyOf(
        [
          turnsGood,
          game.allOf(
            [priorGood, game.not(turnsEvil, `${timing}_${slug(player)}_goon_not_turned_evil`)],
            `${timing}_${slug(player)}_goon_stays_good`,
          ),
        ],
        `${timing}_${slug(player)}_good_after_goon`,
      );
      game.setGoodAt(player, timing, goodAtTiming);
      const match = /^night_(\d+)$/.exec(timing);
      if (match !== null) game.setGoodAt(player, `day_${match[1]}` as Timing, goodAtTiming);
    }
  }
  return { drunkSourcesByActorTiming, targetings };
}

function goonWasTargetedBefore(
  game: BOTCModel,
  context: GoonContext,
  timing: Timing,
  order: number,
  name: string,
): BoolLike {
  return game.anyOf(
    context.targetings
      .filter((targeting) => targeting.timing === timing && targeting.order < order)
      .map((targeting) => targeting.active),
    name,
  );
}

function nightActionOrder(role: string): number {
  const order: Readonly<Record<string, number>> = {
    Sailor: 10,
    Courtier: 20,
    Innkeeper: 30,
    Gambler: 40,
    "Devil's Advocate": 50,
    Exorcist: 60,
    Zombuul: 70,
    Pukka: 80,
    Shabaloth: 90,
    Po: 100,
    Assassin: 110,
    Godfather: 120,
    Gossip: 125,
    Professor: 130,
    Tinker: 140,
    Moonchild: 150,
    Chambermaid: 200,
  };
  return order[role] ?? 150;
}

function applyConditionalWakeSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Godfather")) return;
  for (const timing of collectTimings(doc)) {
    const previousDay = previousDayForNight(timing);
    if (previousDay === undefined) continue;
    const outsiderDied = game.anyOf(
      (doc.timeline ?? []).flatMap((event) =>
        event.timing === previousDay && isTimelineDeathEvent(event)
          ? event.players.map((player) => game.hasCharacterType(player, CharacterType.Outsider))
          : [],
      ),
      `${timing}_godfather_outsider_died_previous_day`,
    );
    for (const player of doc.players) {
      game.registerConditionalWake(
        player,
        "Godfather",
        timing,
        game.allOf(
          [game.hasRoleAt(player, "Godfather", timing), outsiderDied],
          `${timing}_${slug(player)}_godfather_conditional_wake`,
        ),
      );
    }
  }
}

function applyGlobalConstraints(game: BOTCModel, doc: PuzzleDoc, ctx: Omit<CompileCtx, "nameRoot">): void {
  for (const [index, constraint] of (doc.constraints ?? []).entries()) {
    const expression = constraint.expression.trim();
    if (expression === "") continue;
    game.addTruth(
      compile(expression, game, {
        ...ctx,
        nameRoot: `global_constraint_${index + 1}`,
      }) as BoolLike,
    );
  }
}

function applyChangedRoleClaimExplanations(game: BOTCModel, doc: PuzzleDoc): void {
  const claimsByPlayer = new Map<
    string,
    Array<{ readonly index: number; readonly claim: PuzzleDoc["claims"][number] }>
  >();
  for (const [index, claim] of doc.claims.entries()) {
    if (claim.timing === undefined) continue;
    const role = claimRoleRef(claim);
    if (role === undefined) continue;

    const claims = claimsByPlayer.get(claim.name);
    if (claims === undefined) claimsByPlayer.set(claim.name, [{ index, claim }]);
    else claims.push({ index, claim });
  }

  for (const claims of claimsByPlayer.values()) {
    const timedClaims = claims.sort(
      (left, right) =>
        phaseStartOrder(left.claim.timing as Timing) - phaseStartOrder(right.claim.timing as Timing) ||
        left.index - right.index,
    );
    for (let index = 1; index < timedClaims.length; index += 1) {
      const previous = timedClaims[index - 1] as (typeof timedClaims)[number];
      const current = timedClaims[index] as (typeof timedClaims)[number];
      const previousRole = claimRoleRef(previous.claim);
      const currentRole = claimRoleRef(current.claim);
      if (previousRole === undefined || currentRole === undefined) continue;
      if (roleName(previousRole) === roleName(currentRole)) continue;
      if (phaseStartOrder(current.claim.timing as Timing) <= phaseStartOrder(previous.claim.timing as Timing)) continue;

      explainChangedRoleClaim(game, doc, current.claim, currentRole);
    }
  }
}

function explainChangedRoleClaim(
  game: BOTCModel,
  doc: PuzzleDoc,
  claim: PuzzleDoc["claims"][number],
  claimedRole: RoleRef,
): void {
  if (claim.timing === undefined) return;
  const claimTiming = claim.timing as Timing;
  const sourceTiming = roleChangeSourceTiming(claimTiming);
  const claimedRoleName = roleName(claimedRole);
  const claimedRoleAtTiming = game.hasRoleAt(claim.name, claimedRole, claimTiming);
  const claimantEvil = game.hasAlignmentOverrideAt(claim.name, claimTiming)
    ? game.isEvilAt(claim.name, claimTiming)
    : game.isEvil(claim.name);
  const explanations: BoolLike[] = [claimedRoleAtTiming, claimantEvil];

  if (doc.script.includes("Pit-Hag")) {
    const activePitHag = game.roleSoberAndHealthyAt(
      "Pit-Hag",
      sourceTiming,
      `${sourceTiming}_${slug(claim.name)}_${slug(claimedRoleName)}_pit_hag_active`,
    );
    const legalPitHagTransformation = game.allOf(
      [activePitHag, game.roleInPlay(claimedRole).not()],
      `${sourceTiming}_${slug(claim.name)}_${slug(claimedRoleName)}_pit_hag_transform`,
    );
    game.addRoleAt(claim.name, claimedRole, claimTiming, legalPitHagTransformation);
  }

  if (doc.script.includes("Cerenovus") && roleAlignment(claimedRole) === Alignment.Good) {
    explanations.push(
      game.roleSoberAndHealthyAt(
        "Cerenovus",
        sourceTiming,
        `${sourceTiming}_${slug(claim.name)}_cerenovus_mad_as_${slug(claimedRoleName)}`,
      ),
    );
  }

  game.addTruth(
    game.anyOf(explanations, `${claimTiming}_${slug(claim.name)}_${slug(claimedRoleName)}_role_change_explained`),
  );
}

function claimRoleRef(claim: PuzzleDoc["claims"][number]): RoleRef | undefined {
  return resolveClaimTypeRoleRef(claim.type);
}

function resolveClaimTypeRoleRef(type: string): RoleRef | undefined {
  try {
    return resolveRoleRef(type);
  } catch {
    const spaced = type.replace(/([a-z])([A-Z])/g, "$1 $2");
    try {
      return resolveRoleRef(spaced);
    } catch {
      return undefined;
    }
  }
}

function roleChangeSourceTiming(timing: Timing): Timing {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null || match[2] === undefined) throw new Error(`Invalid timing '${timing}'.`);
  return `night_${match[2]}` as Timing;
}

function applyPreNightDeathSnakeCharmerChecks(game: BOTCModel, doc: PuzzleDoc): ReadonlySet<string> {
  const handled = new Set<string>();
  const nightDeathEventByTiming = new Map<Timing, NonNullable<PuzzleDoc["timeline"]>[number]>();
  for (const event of doc.timeline ?? []) {
    if (event.type === "nightDeath") nightDeathEventByTiming.set(event.timing as Timing, event);
  }
  if (nightDeathEventByTiming.size === 0) return handled;

  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === CharacterType.Demon);
  if (demonRoles.length === 0) return handled;

  for (const [claimIndex, claim] of doc.claims.entries()) {
    if (claim.type !== "Snake Charmer") continue;
    for (const [checkIndex, check] of claim.checks.entries()) {
      if (check.timing === undefined) continue;
      const timing = check.timing as Timing;
      const event = nightDeathEventByTiming.get(timing);
      if (event === undefined) continue;

      const checkedIsDemonBeforeDeath = game.anyOf(
        demonRoles.map((role) => roleAtBeforeEvent(game, doc, check.player, role, event)),
        `${timing}_${slug(claim.name)}_snake_charmer_check_${checkIndex + 1}_pre_death_demon`,
      );
      game.addInfoClaim({
        player: claim.name,
        role: "Snake Charmer",
        timing,
        learned: check.demon
          ? checkedIsDemonBeforeDeath
          : game.not(
              checkedIsDemonBeforeDeath,
              `${timing}_${slug(claim.name)}_snake_charmer_check_${checkIndex + 1}_pre_death_not_demon`,
            ),
      });
      handled.add(preNightDeathSnakeCharmerCheckKey(claimIndex, checkIndex));
    }
  }
  return handled;
}

function removePreNightDeathSnakeCharmerChecks(
  claim: PuzzleDoc["claims"][number],
  claimIndex: number,
  handled: ReadonlySet<string>,
): PuzzleDoc["claims"][number] {
  if (claim.type !== "Snake Charmer") return claim;
  const checks = claim.checks.filter(
    (_, checkIndex) => !handled.has(preNightDeathSnakeCharmerCheckKey(claimIndex, checkIndex)),
  );
  return checks.length === claim.checks.length ? claim : { ...claim, checks };
}

function preNightDeathSnakeCharmerCheckKey(claimIndex: number, checkIndex: number): string {
  return `${claimIndex}:${checkIndex}`;
}

function applyPhilosopherDrunking(game: BOTCModel, doc: PuzzleDoc): void {
  const philosopherClaims = doc.claims.filter(
    (claim): claim is Extract<PuzzleDoc["claims"][number], { readonly type: "Philosopher" }> =>
      claim.type === "Philosopher" && claim.role !== undefined && claim.timing !== undefined,
  );
  const timings = collectTimings(doc);
  for (const claim of philosopherClaims) {
    const choiceTiming = claim.timing as Timing;
    const affectedTimings = timings.filter((timing) => phaseStartOrder(timing) >= phaseStartOrder(choiceTiming));
    if (affectedTimings.length === 0) continue;
    const choiceActive = game.allOf(
      [game.actualIs(claim.name, "Philosopher"), game.soberAndHealthy(claim.name, choiceTiming)],
      `${slug(claim.name)}_philosopher_choice_active`,
    );

    for (const timing of affectedTimings) {
      const philosopherAlive = game.anyOf(
        doc.players
          .filter((player) => !deadPlayersBefore(doc, timing).has(player))
          .map((player) => game.actualIs(player, "Philosopher")),
        `${slug(claim.name)}_philosopher_alive_at_${timing}`,
      );
      game.addRoleDrunking(resolveRoleRef(claim.role as string), [timing], {
        activeIf: game.allOf([choiceActive, philosopherAlive], `${slug(claim.name)}_philosopher_drunking_${timing}`),
        excludedPlayers: [claim.name],
      });
    }
  }
}

function applyAtheistSetup(game: BOTCModel, doc: PuzzleDoc): void {
  const evilRoles = doc.script.map(resolveRoleRef).filter((role) => roleAlignment(role) === Alignment.Evil);
  for (const player of doc.players) {
    for (const role of evilRoles) game.fixNotActual(player, role);
  }
  if (doc.script.includes("Atheist")) game.addTruth(game.roleInPlay("Atheist"));
}

function applyTimelineConstraints(game: BOTCModel, doc: PuzzleDoc): void {
  const timelineEvents = doc.timeline ?? [];
  if (timelineEvents.length === 0) return;

  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === CharacterType.Demon);
  for (const event of timelineEvents) {
    if (event.type === "survivedExecution") {
      for (const player of event.players) {
        const timing = event.timing as Timing;
        const foolProtection = registerFoolExecutionProtection(game, doc, player, timing);
        game.addTruth(executionSurvivalAt(game, doc, player, timing, foolProtection));
      }
      continue;
    }
    if (event.type === "resurrection") continue;

    if (isTimelineDeathEvent(event) && event.type !== "nightDeath") {
      for (const player of event.players) {
        game.addFalse(deathProtectionAt(game, doc, player, event.timing as Timing));
      }
    }

    if (event.type === "doomsayerDeath" && event.caller !== undefined) {
      for (const player of event.players) {
        game.addTruth(doomsayerSameRegisteredAlignment(game, event.caller, player));
      }
    }
    if (event.type === "witchCurse" && event.caller !== undefined && doc.script.includes("Witch")) {
      game.addTruth(witchCurseSourceAvailable(game, doc, event));
    }
    if (event.type === "nominationDeath" && event.caller !== undefined && doc.script.includes("Golem")) {
      const timing = event.timing as Timing;
      const activeHealthyGolem = game.allOf(
        [
          game.hasRoleAt(event.caller, "Golem", timing),
          game.soberAndHealthy(event.caller, healthTimingForDayAbility(timing)),
        ],
        `${timing}_${slug(event.caller)}_golem_nomination_active`,
      );
      game.addTruth(activeHealthyGolem);
    }
    if (event.type === "tinkerDeath") {
      for (const player of event.players) {
        game.addTruth(
          game.allOf(
            [
              game.hasRoleAt(player, "Tinker", event.timing as Timing),
              game.soberAndHealthy(player, healthTimingForDayAbility(event.timing as Timing)),
            ],
            `${event.timing}_${slug(player)}_healthy_tinker_storyteller_death`,
          ),
        );
      }
      continue;
    }
    if (event.type === "nightDeath") continue;
    if (event.type === "witchCurse" || event.type === "slayerShot") {
      for (const player of event.players) {
        for (const demonRole of demonRoles) {
          const demonRoleName = roleName(demonRole);
          if (demonRoleName === "Legion") continue;
          if (demonRoleName === "Zombuul") continue;
          game.addImplication(game.actualIs(player, demonRole), livingScarletWomanCanCatchDemonDeath(game, doc, event));
        }
      }
      continue;
    }
    if (event.type === "doomsayerDeath") continue;
    if (event.type === "execution") {
      if (doc.script.includes("Saint")) {
        for (const player of event.players) game.fixNotActual(player, "Saint");
      }
      if (doc.script.includes("Hermit")) {
        for (const player of event.players) game.fixNotActual(player, "Hermit");
      }
    }
    if (event.type === "nominationDeath" && doc.script.includes("Riot")) continue;
    for (const player of event.players) {
      for (const demonRole of demonRoles) {
        if (event.type === "execution" && roleName(demonRole) === "Legion") continue;
        if (
          event.type === "execution" &&
          doc.script.includes("Mastermind") &&
          doc.setup !== "none" &&
          doc.setup !== "atheist"
        )
          continue;
        if (roleName(demonRole) === "Zombuul") continue;
        game.fixNotActual(player, demonRole);
      }
    }
  }
}

function applyResurrectionConstraints(
  game: BOTCModel,
  doc: PuzzleDoc,
  nightDeathTiming: NightDeathTimingContext,
): void {
  const professorActions = declaredProfessorActions(game, doc);
  for (const event of doc.timeline ?? []) {
    if (event.type !== "resurrection") continue;
    const timing = event.timing as Timing;
    const priorNight = previousNight(timing);
    for (const player of event.players) {
      const wasDead = deadPlayersBefore(doc, timing).has(player);
      if (!wasDead) {
        game.addFalse(game.constantBool(true, `${timing}_${slug(player)}_resurrected_while_alive`));
        continue;
      }

      const professorSources = professorActions
        .filter((action) => action.timing === timing && action.target === player)
        .map((action) => {
          const source = game.allOf(
            [
              action.active,
              game.soberAndHealthy(action.claimant, timing),
              game.hasCharacterType(player, CharacterType.Townsfolk),
            ],
            `${timing}_${slug(action.claimant)}_professor_resurrects_${slug(player)}`,
          );
          return source;
        });

      const priorNightDeath = (doc.timeline ?? []).findIndex(
        (candidate) =>
          candidate.type === "nightDeath" && candidate.timing === priorNight && candidate.players.includes(player),
      );
      const priorDemonKill =
        priorNightDeath === -1
          ? undefined
          : nightDeathTiming.demonKillAssignmentsByEventPlayer.get(timelineEventPlayerKey(priorNightDeath, player));
      const wasDeadWhenChosen =
        priorNight !== undefined && deadPlayersBefore(doc, priorNight).has(player)
          ? game.constantBool(true, `${priorNight}_${slug(player)}_was_dead_when_shabaloth_chose_them`)
          : game.constantBool(false, `${timing}_${slug(player)}_was_not_dead_for_prior_shabaloth_choice`);
      const shabalothSource =
        doc.script.includes("Shabaloth") && priorNight !== undefined
          ? game.allOf(
              [
                healthyRoleAliveAt(game, doc, "Shabaloth", timing),
                game.anyOf(
                  [...(priorDemonKill === undefined ? [] : [priorDemonKill]), wasDeadWhenChosen],
                  `${priorNight}_${slug(player)}_could_have_been_chosen_by_shabaloth`,
                ),
              ],
              `${timing}_${slug(player)}_shabaloth_regurgitation`,
            )
          : game.constantBool(false, `${timing}_${slug(player)}_not_a_shabaloth_regurgitation`);

      game.addTruth(
        game.anyOf([...professorSources, shabalothSource], `${timing}_${slug(player)}_has_resurrection_source`),
      );
    }
  }
  game.addEnforcedAtMostN(
    professorActions.map((action) => action.active),
    1,
    game.constantBool(true, "professor_once_per_game"),
  );
}

interface DeclaredProfessorAction {
  readonly claimant: string;
  readonly target: string;
  readonly timing: Timing;
  readonly active: BoolLike;
}

function declaredProfessorActions(game: BOTCModel, doc: PuzzleDoc): DeclaredProfessorAction[] {
  return doc.claims.flatMap((claim, index) => {
    if (claim.type !== "Professor" || claim.target === undefined || claim.target === "") return [];
    const timing = (claim.timing ?? "night_2") as Timing;
    const active = game.hasRoleAt(claim.name, "Professor", timing);
    const validTiming = /^night_([2-9]|[1-9]\d+)$/.test(timing);
    const claimantAlive = livingPlayersAt(doc, timing).includes(claim.name);
    const targetDead = deadPlayersBefore(doc, timing).has(claim.target);
    game.addImplication(
      active,
      game.constantBool(
        validTiming && claimantAlive && targetDead,
        `${timing}_${slug(claim.name)}_professor_action_${index + 1}_is_legal`,
      ),
    );
    game.registerAbilityUse(claim.name, "Professor", timing, active);
    return [{ claimant: claim.name, target: claim.target, timing, active }];
  });
}

function applyRiotTransformations(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Riot")) return;
  const minionRoles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === CharacterType.Minion);
  if (minionRoles.length === 0) return;

  const affectedTimings = collectTimings(doc).filter((timing) => phaseStartOrder(timing) >= phaseStartOrder("day_3"));
  for (const timing of affectedTimings) {
    for (const player of doc.players) {
      const startsAsMinion = game.anyOf(
        minionRoles.map((role) => game.actualIs(player, role)),
        `${timing}_${slug(player)}_starts_as_minion`,
      );
      game.addRoleAt(player, "Riot", timing, startsAsMinion);
      for (const minionRole of minionRoles) {
        game.removeRoleAt(player, minionRole, timing, game.actualIs(player, minionRole));
      }
    }
  }
}

function doomsayerSameRegisteredAlignment(game: BOTCModel, caller: string, deadPlayer: string): BoolLike {
  return game.anyOf(
    [
      game.allOf(
        [
          game.registersAsGood(caller, `${caller}_${deadPlayer}_doomsayer_caller_good`),
          game.registersAsGood(deadPlayer, `${caller}_${deadPlayer}_doomsayer_dead_good`),
        ],
        `${caller}_${deadPlayer}_doomsayer_both_good`,
      ),
      game.allOf(
        [
          game.registersAsEvil(caller, `${caller}_${deadPlayer}_doomsayer_caller_evil`),
          game.registersAsEvil(deadPlayer, `${caller}_${deadPlayer}_doomsayer_dead_evil`),
        ],
        `${caller}_${deadPlayer}_doomsayer_both_evil`,
      ),
    ],
    `${caller}_${deadPlayer}_doomsayer_same_registered_alignment`,
  );
}

function deathProtectionAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  return game.anyOf(
    [
      teaLadyProtectsAt(game, doc, player, timing),
      foolProtectsAt(game, doc, player, timing),
      sailorProtectsAt(game, doc, player, timing),
      ...(doc.script.includes("Innkeeper") ? [innkeeperProtectionAt(game, doc, player, timing)] : []),
    ],
    `${timing}_${slug(player)}_death_protected`,
  );
}

function executionSurvivalAt(
  game: BOTCModel,
  doc: PuzzleDoc,
  player: string,
  timing: Timing,
  foolProtection: BoolLike = foolProtectsAt(game, doc, player, timing),
): BoolLike {
  return game.anyOf(
    [
      teaLadyProtectsAt(game, doc, player, timing),
      foolProtection,
      sailorProtectsAt(game, doc, player, timing),
      pacifistProtectsExecutionAt(game, doc, player, timing),
      devilsAdvocateProtectsExecutionAt(game, doc, player, timing),
    ],
    `${timing}_${slug(player)}_survived_execution_source`,
  );
}

function registerFoolExecutionProtection(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Fool"))
    return game.constantBool(false, `${timing}_${slug(player)}_no_fool_execution_protection`);
  const used = game.newBool(`${timing}_${slug(player)}_fool_ability_used_for_execution`);
  game.addImplication(used, foolProtectsAt(game, doc, player, timing));
  game.addImplication(
    used,
    game.not(
      game.anyOf(
        [
          teaLadyProtectsAt(game, doc, player, timing),
          sailorProtectsAt(game, doc, player, timing),
          devilsAdvocateProtectsExecutionAt(game, doc, player, timing),
        ],
        `${timing}_${slug(player)}_mandatory_non_fool_execution_protection`,
      ),
      `${timing}_${slug(player)}_fool_save_not_preempted`,
    ),
  );
  game.registerAbilityUse(player, "Fool", timing, used);
  return used;
}

function sailorProtectsAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Sailor")) return game.constantBool(false, `${timing}_${slug(player)}_no_sailor_on_script`);
  return game.allOf(
    [game.hasRoleAt(player, "Sailor", timing), game.soberAndHealthy(player, healthTimingForDayAbility(timing))],
    `${timing}_${slug(player)}_sober_sailor_protection`,
  );
}

function foolProtectsAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Fool")) return game.constantBool(false, `${timing}_${slug(player)}_no_fool_on_script`);
  return game.allOf(
    [
      game.hasRoleAt(player, "Fool", timing),
      game.soberAndHealthy(player, healthTimingForDayAbility(timing)),
      game.not(
        game.abilityUsedBefore(player, "Fool", timing, `${timing}_${slug(player)}_fool_ability_used_before`),
        `${timing}_${slug(player)}_fool_ability_unused`,
      ),
    ],
    `${timing}_${slug(player)}_healthy_fool_protection`,
  );
}

function pacifistProtectsExecutionAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Pacifist"))
    return game.constantBool(false, `${timing}_${slug(player)}_no_pacifist_on_script`);
  const healthTiming = healthTimingForDayAbility(timing);
  return game.anyOf(
    livingPlayersAt(doc, timing).map((candidate) =>
      game.allOf(
        [
          game.hasRoleAt(candidate, "Pacifist", timing),
          game.soberAndHealthy(candidate, healthTiming),
          game.isGoodAt(player, timing),
        ],
        `${timing}_${slug(candidate)}_pacifist_protects_${slug(player)}`,
      ),
    ),
    `${timing}_${slug(player)}_pacifist_execution_protection`,
  );
}

function teaLadyProtectsAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Tea Lady")) {
    return game.constantBool(false, `${timing}_${slug(player)}_no_tea_lady_protection`);
  }
  const healthTiming = healthTimingForDayAbility(timing);
  const protectors = livingPlayersAt(doc, timing).flatMap((candidate): BoolLike[] => {
    if (candidate === player) return [];
    const [left, right] = livingNeighborsAt(doc, candidate, timing);
    if (left !== player && right !== player) return [];
    const goodNeighbors =
      left === right
        ? game.isGoodAt(left, timing)
        : game.allOf(
            [game.isGoodAt(left, timing), game.isGoodAt(right, timing)],
            `${timing}_${slug(candidate)}_tea_lady_neighbors_good`,
          );
    return [
      game.allOf(
        [game.hasRoleAt(candidate, "Tea Lady", timing), game.soberAndHealthy(candidate, healthTiming), goodNeighbors],
        `${timing}_${slug(candidate)}_tea_lady_protects_${slug(player)}`,
      ),
    ];
  });
  return game.anyOf(protectors, `${timing}_${slug(player)}_tea_lady_protected`);
}

function devilsAdvocateProtectsExecutionAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Devil's Advocate")) {
    return game.constantBool(false, `${timing}_no_devils_advocate_protection`);
  }
  const abilityTiming = healthTimingForDayAbility(timing);
  const protectors = livingPlayersAt(doc, abilityTiming).map((candidate) =>
    game.allOf(
      [
        game.hasRoleAt(candidate, "Devil's Advocate", abilityTiming),
        game.soberAndHealthy(candidate, abilityTiming),
        game.abilityTargetedAt(
          candidate,
          "Devil's Advocate",
          player,
          abilityTiming,
          `${timing}_${slug(candidate)}_devils_advocate_targeted_${slug(player)}`,
        ),
      ],
      `${timing}_${slug(candidate)}_devils_advocate_protects_${slug(player)}`,
    ),
  );
  return game.anyOf(protectors, `${timing}_devils_advocate_protects_execution`);
}

function witchCurseSourceAvailable(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const timing = event.timing as Timing;
  if (event.sourceActedBeforeDeath === true) {
    return game.constantBool(true, `${timing}_witch_curse_source_acted_before_death`);
  }
  const abilityTiming = healthTimingForDayAbility(timing);
  return game.anyOf(
    livingPlayersBeforeDeathEvent(doc, event).map((player) =>
      game.allOf(
        [
          game.hasRoleAt(player, "Witch", abilityTiming),
          roleAtBeforeEvent(game, doc, player, "Witch", event),
          game.soberAndHealthy(player, abilityTiming),
        ],
        `${timing}_${slug(player)}_witch_curse_source_available`,
      ),
    ),
    `${timing}_witch_curse_source_available`,
  );
}

function livingMinionCanCatchDemonDeath(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  return game.anyOf(
    candidates.map((player) => isMinionBeforeEvent(game, doc, player, event)),
    `${event.timing}_minion_can_catch_imp_death`,
  );
}

function livingScarletWomanCanCatchDemonDeath(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  if (!doc.script.includes("Scarlet Woman")) return game.constantBool(false, "no_scarlet_woman_to_catch_demon");
  if (livingPlayersBeforeDeathEvent(doc, event).length < 5)
    return game.constantBool(false, `${event.timing}_fewer_than_five_alive_for_scarlet_woman`);
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  return game.anyOf(
    candidates.map((player) => roleAtBeforeEvent(game, doc, player, "Scarlet Woman", event)),
    `${event.timing}_scarlet_woman_can_catch_demon_death`,
  );
}

function livingOutsiderCanCatchFangGuJump(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  return game.anyOf(
    candidates.map((player) => characterTypeBeforeEvent(game, doc, player, CharacterType.Outsider, event)),
    `${event.timing}_outsider_can_catch_fang_gu_jump`,
  );
}

function livingPlayersAfterDeathEvent(
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): readonly string[] {
  const deadPlayers = deadPlayersBefore(doc, event.timing as Timing);
  const dyingPlayers = new Set(event.players);
  return doc.players.filter((player) => !deadPlayers.has(player) && !dyingPlayers.has(player));
}

function applyOngoingGameConstraint(game: BOTCModel, doc: PuzzleDoc): void {
  if (doc.setup === "none" || doc.setup === "atheist" || (doc.timeline?.length ?? 0) === 0) return;

  const finalLivingPlayers = livingPlayersAfterTimeline(doc);
  const finalDeadPlayers = doc.players.filter((player) => !finalLivingPlayers.includes(player));
  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === CharacterType.Demon);
  const finalTiming = collectTimings(doc).at(-1);
  const finalLivingStartingDemon = finalLivingPlayers.flatMap((player) =>
    demonRoles.map((role) =>
      finalTiming === undefined ? game.actualIs(player, role) : game.hasRoleAt(player, role, finalTiming),
    ),
  );
  const possibleSuccessions: BoolLike[] = [];

  if (doc.script.includes("Zombuul")) {
    const apparentlyDeadOnce = finalDeadPlayers.flatMap((player): BoolLike[] => {
      const deaths = (doc.timeline ?? []).filter(
        (event) => isTimelineDeathEvent(event) && event.players.includes(player),
      );
      if (deaths.length !== 1) return [];
      const death = deaths[0] as NonNullable<PuzzleDoc["timeline"]>[number];
      return [
        game.allOf(
          [
            roleAtBeforeEvent(game, doc, player, "Zombuul", death),
            game.soberAndHealthy(player, healthTimingForDayAbility(death.timing as Timing)),
          ],
          `${death.timing}_${slug(player)}_healthy_zombuul_apparently_dead`,
        ),
      ];
    });
    possibleSuccessions.push(game.anyOf(apparentlyDeadOnce, "apparently_dead_zombuul_can_still_be_alive"));
  }

  if (doc.script.includes("Scarlet Woman")) {
    const deadNonImpDemons = finalDeadPlayers.flatMap((player) =>
      demonRoles.filter((role) => roleName(role) !== "Imp").map((role) => game.actualIs(player, role)),
    );
    possibleSuccessions.push(
      game.allOf(
        [
          game.anyOf(deadNonImpDemons, "dead_non_imp_demon_before_current_state"),
          game.anyOf(
            finalLivingPlayers.map((player) => game.actualIs(player, "Scarlet Woman")),
            "final_living_scarlet_woman_can_be_demon",
          ),
        ],
        "final_scarlet_woman_successor_can_be_alive",
      ),
    );
  }
  if (doc.script.includes("Fang Gu")) {
    possibleSuccessions.push(
      game.allOf(
        [
          game.anyOf(
            finalDeadPlayers.map((player) => game.actualIs(player, "Fang Gu")),
            "dead_fang_gu_before_current_state",
          ),
          game.anyOf(
            finalLivingPlayers.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
            "final_living_outsider_can_be_fang_gu",
          ),
        ],
        "final_fang_gu_successor_can_be_alive",
      ),
    );
  }
  if (doc.script.includes("Mastermind")) {
    possibleSuccessions.push(...mastermindExtraDayPaths(game, doc, demonRoles, finalTiming));
  }

  game.addTruth(
    game.anyOf([...finalLivingStartingDemon, ...possibleSuccessions], "ongoing_game_has_living_demon_or_successor"),
  );
}

function zombuulDiesForRealAt(
  game: BOTCModel,
  doc: PuzzleDoc,
  player: string,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const diedBefore = (doc.timeline ?? []).some(
    (candidate) =>
      isTimelineDeathEvent(candidate) &&
      candidate.players.includes(player) &&
      deathEventOrder(candidate) < deathEventOrder(event),
  );
  if (diedBefore) return game.constantBool(true, `${event.timing}_${slug(player)}_zombuul_died_before`);
  return game.not(
    game.soberAndHealthy(player, healthTimingForDayAbility(event.timing as Timing)),
    `${event.timing}_${slug(player)}_droisoned_zombuul_dies_for_real`,
  );
}

function mastermindExtraDayPaths(
  game: BOTCModel,
  doc: PuzzleDoc,
  demonRoles: readonly RoleRef[],
  finalTiming: Timing | undefined,
): readonly BoolLike[] {
  if (finalTiming === undefined) return [];
  const finalOrder = phaseStartOrder(finalTiming);
  return (doc.timeline ?? []).flatMap((event): BoolLike[] => {
    if (event.type !== "execution") return [];
    const timing = event.timing as Timing;
    const match = /^day_(\d+)$/.exec(timing);
    if (match === null) return [];
    const extraDay = `day_${Number(match[1]) + 1}` as Timing;
    if (finalOrder < phaseStartOrder(timing) || finalOrder > phaseStartOrder(extraDay)) return [];
    const laterExecution = (doc.timeline ?? []).some(
      (candidate) =>
        (candidate.type === "execution" || candidate.type === "survivedExecution") &&
        deathEventOrder(candidate) > deathEventOrder(event),
    );
    if (laterExecution) return [];

    const demonDies = game.anyOf(
      event.players.flatMap((player) =>
        demonRoles.map((role) => {
          const actualDemon = roleAtBeforeEvent(game, doc, player, role, event);
          if (roleName(role) !== "Zombuul") return actualDemon;
          return game.allOf(
            [actualDemon, zombuulDiesForRealAt(game, doc, player, event)],
            `${timing}_${slug(player)}_zombuul_really_dies_for_mastermind`,
          );
        }),
      ),
      `${timing}_demon_dies_by_execution_for_mastermind`,
    );
    const noScarletWomanCatches = game.not(
      livingScarletWomanCanCatchDemonDeath(game, doc, event),
      `${timing}_no_scarlet_woman_catches_demon_for_mastermind`,
    );
    const activeMastermind = game.anyOf(
      livingPlayersAfterDeathEvent(doc, event).map((player) =>
        game.allOf(
          [
            roleAtBeforeEvent(game, doc, player, "Mastermind", event),
            game.soberAndHealthy(player, healthTimingForDayAbility(timing)),
          ],
          `${timing}_${slug(player)}_mastermind_extra_day_active`,
        ),
      ),
      `${timing}_living_healthy_mastermind_for_extra_day`,
    );
    return [
      game.allOf([demonDies, noScarletWomanCatches, activeMastermind], `${timing}_mastermind_extra_day_continues_game`),
    ];
  });
}

interface NightDeathSource {
  readonly id: string;
  readonly available: BoolLike;
  readonly players?: readonly string[];
  readonly maxAssignments?: number;
  readonly targetCountWhenAvailable?: number;
  readonly requiredWhenAvailable?: boolean;
  readonly poKill?: boolean;
  readonly demonKill?: boolean;
  readonly starpassesImp?: boolean;
  readonly fangGuJumps?: boolean;
  readonly deathTiming?: "beforeInfo" | "afterInfo";
  readonly resolutionOrder?: number;
  readonly requiresAliveAtResolution?: string;
  readonly bypassesProtection?: boolean;
  readonly requiresDemonKillOf?: string;
  readonly constrainAssignment?: (player: string, assignment: BoolLike) => void;
}

interface NightDeathTimingContext {
  readonly beforeInfoDeathsByTiming: ReadonlyMap<Timing, ReadonlyMap<string, BoolLike>>;
  readonly demonKillAssignmentsByEventPlayer: ReadonlyMap<string, BoolLike>;
}

function emptyNightDeathTimingContext(): NightDeathTimingContext {
  return { beforeInfoDeathsByTiming: new Map(), demonKillAssignmentsByEventPlayer: new Map() };
}

function applyNightDeathSourceConstraints(
  game: BOTCModel,
  doc: PuzzleDoc,
  ctx: Omit<CompileCtx, "nameRoot">,
  pukkaContext: PukkaContext,
  godfatherContext: GodfatherContext,
  goonContext: GoonContext,
  shabalothContext: ShabalothContext,
): NightDeathTimingContext {
  const roleTimings = collectTimings(doc);
  const beforeInfoAssignments = new Map<Timing, Map<string, BoolLike[]>>();
  const demonKillAssignments = new Map<string, BoolLike[]>();
  const poChosePlayerByTiming = new Map<Timing, BoolLike>();
  for (const [eventIndex, event] of (doc.timeline ?? []).entries()) {
    if (event.type !== "nightDeath") continue;
    const timing = event.timing as Timing;
    const priorNight = previousNight(timing);
    const priorPoChoice = priorNight === undefined ? undefined : poChosePlayerByTiming.get(priorNight);
    const poCharged =
      priorNight === undefined || priorNight === "night_1"
        ? game.constantBool(false, `${timing}_po_cannot_be_charged`)
        : game.not(priorPoChoice ?? game.constantBool(false, `${timing}_no_prior_po_choice`), `${timing}_po_charged`);
    const sources = nightDeathSources(
      game,
      doc,
      event,
      ctx,
      poCharged,
      pukkaContext,
      godfatherContext,
      goonContext,
      shabalothContext,
    );
    const assignmentsBySource = new Map<NightDeathSource, BoolLike[]>();
    const assignedDeaths: Array<{
      readonly player: string;
      readonly source: NightDeathSource;
      readonly value: BoolLike;
    }> = [];
    if (event.players.length === 0) for (const source of sources) assignmentsBySource.set(source, []);
    const demonAssignmentsByPlayer = new Map<string, BoolLike[]>();
    const demonLinkedAssignments: Array<{ readonly assignment: BoolLike; readonly player: string }> = [];

    for (const player of event.players) {
      const eligibleSources = sources.filter(
        (source) => source.players === undefined || source.players.includes(player),
      );
      const assignments = eligibleSources.map((source) => {
        const assignment = game.newBool(`${event.timing}_${player}_death_from_${source.id}`);
        game.addImplication(assignment, source.available);
        if (source.bypassesProtection !== true) {
          game.addImplication(
            assignment,
            game.not(
              deathProtectionAt(game, doc, player, timing),
              `${timing}_${slug(player)}_${slug(source.id)}_not_death_protected`,
            ),
          );
        }
        source.constrainAssignment?.(player, assignment);
        if (source.starpassesImp === true) applyImpStarpass(game, doc, event, player, assignment, roleTimings);
        if (source.fangGuJumps === true) applyFangGuJump(game, doc, event, player, assignment, roleTimings);
        if (source.starpassesImp !== true && doc.script.includes("Imp")) {
          game.addImplication(
            game.allOf(
              [assignment, roleAtBeforeEvent(game, doc, player, "Imp", event)],
              `${timing}_${slug(player)}_non_imp_kill_source_kills_imp`,
            ),
            livingScarletWomanCanCatchDemonDeath(game, doc, event),
          );
        }
        if (source.fangGuJumps !== true && doc.script.includes("Fang Gu")) {
          game.addImplication(
            game.allOf(
              [assignment, roleAtBeforeEvent(game, doc, player, "Fang Gu", event)],
              `${timing}_${slug(player)}_non_fang_gu_kill_source_kills_fang_gu`,
            ),
            livingScarletWomanCanCatchDemonDeath(game, doc, event),
          );
        }
        applyScarletWomanCatch(game, doc, event, player, assignment, roleTimings, {
          excludedRoles: [
            ...(source.starpassesImp === true ? ["Imp"] : []),
            ...(source.fangGuJumps === true ? ["Fang Gu"] : []),
          ],
        });
        if (source.demonKill === true) {
          const key = timelineEventPlayerKey(eventIndex, player);
          demonKillAssignments.set(key, [...(demonKillAssignments.get(key) ?? []), assignment]);
          demonAssignmentsByPlayer.set(player, [...(demonAssignmentsByPlayer.get(player) ?? []), assignment]);
        }
        if (source.requiresDemonKillOf !== undefined)
          demonLinkedAssignments.push({ assignment, player: source.requiresDemonKillOf });
        if (source.deathTiming === "beforeInfo") {
          const timing = event.timing as Timing;
          let deathsByPlayer = beforeInfoAssignments.get(timing);
          if (deathsByPlayer === undefined) {
            deathsByPlayer = new Map();
            beforeInfoAssignments.set(timing, deathsByPlayer);
          }
          deathsByPlayer.set(player, [...(deathsByPlayer.get(player) ?? []), assignment]);
        }
        assignmentsBySource.set(source, [...(assignmentsBySource.get(source) ?? []), assignment]);
        assignedDeaths.push({ player, source, value: assignment });
        return assignment;
      });
      game.addExactlyOne(assignments);
    }

    for (const linked of demonLinkedAssignments) {
      game.addImplication(
        linked.assignment,
        game.anyOf(
          demonAssignmentsByPlayer.get(linked.player) ?? [],
          `${timing}_${slug(linked.player)}_required_demon_kill`,
        ),
      );
    }
    applyRequiredGrandmotherDeaths(game, doc, event, demonAssignmentsByPlayer);

    const sourceCapacityActive = game.constantBool(true, `${event.timing}_night_death_source_capacity_active`);
    const effectiveAvailabilityBySource = new Map<NightDeathSource, BoolLike>();
    for (const [source, assignments] of assignmentsBySource) {
      game.addEnforcedAtMostN(assignments, source.maxAssignments ?? 1, sourceCapacityActive);
      const sourceAssigned =
        assignments.length === 1
          ? (assignments[0] as BoolLike)
          : game.anyOf(assignments, `${event.timing}_${source.id}_assigned`);
      let effectiveAvailability = source.available;
      if (source.requiresAliveAtResolution !== undefined) {
        const actor = source.requiresAliveAtResolution;
        const aliveAtPhaseStart = game.constantBool(
          livingPlayersAt(doc, timing).includes(actor),
          `${timing}_${slug(actor)}_alive_at_phase_start_for_${slug(source.id)}`,
        );
        const diesEarlier = game.anyOf(
          assignedDeaths
            .filter(
              (death) =>
                death.player === actor &&
                (death.source.resolutionOrder ?? Number.POSITIVE_INFINITY) <
                  (source.resolutionOrder ?? Number.POSITIVE_INFINITY),
            )
            .map((death) => death.value),
          `${timing}_${slug(actor)}_dies_before_${slug(source.id)}`,
        );
        effectiveAvailability = game.allOf(
          [
            source.available,
            aliveAtPhaseStart,
            game.not(diesEarlier, `${timing}_${slug(actor)}_survives_until_${slug(source.id)}`),
          ],
          `${timing}_${slug(source.id)}_effective_availability`,
        );
        for (const assignment of assignments) game.addImplication(assignment, effectiveAvailability);
      }
      effectiveAvailabilityBySource.set(source, effectiveAvailability);
      if (source.requiredWhenAvailable !== false) game.addImplication(effectiveAvailability, sourceAssigned);
    }

    const deadAtPhaseStart = deadPlayersBefore(doc, timing);
    const nonDeathTargetsBySource = new Map<NightDeathSource, readonly BoolLike[]>();
    for (const [source, assignments] of assignmentsBySource) {
      if (source.demonKill !== true) continue;
      const nonDeathTargets = doc.players.map((player) => {
        const killedBySource = game.anyOf(
          assignedDeaths
            .filter((death) => death.player === player && death.source === source)
            .map((death) => death.value),
          `${timing}_${slug(source.id)}_does_not_kill_${slug(player)}`,
        );
        const diesEarlier = game.anyOf(
          assignedDeaths
            .filter(
              (death) =>
                death.player === player &&
                (death.source.resolutionOrder ?? Number.POSITIVE_INFINITY) <
                  (source.resolutionOrder ?? Number.POSITIVE_INFINITY),
            )
            .map((death) => death.value),
          `${timing}_${slug(player)}_dies_before_${slug(source.id)}_targets`,
        );
        const survivesDemonTarget = game.anyOf(
          [
            game.constantBool(
              deadAtPhaseStart.has(player),
              `${timing}_${slug(player)}_dead_before_${slug(source.id)}_targets`,
            ),
            diesEarlier,
            demonKillProtectionAt(game, doc, player, timing),
          ],
          `${timing}_${slug(player)}_can_survive_${slug(source.id)}_target`,
        );
        return game.allOf(
          [
            survivesDemonTarget,
            game.not(killedBySource, `${timing}_${slug(source.id)}_does_not_also_target_${slug(player)}`),
          ],
          `${timing}_${slug(player)}_non_death_target_for_${slug(source.id)}`,
        );
      });
      nonDeathTargetsBySource.set(source, nonDeathTargets);
      if (source.targetCountWhenAvailable !== undefined) {
        game.addEnforcedAtLeastN(
          [...assignments, ...nonDeathTargets],
          source.targetCountWhenAvailable,
          effectiveAvailabilityBySource.get(source) as BoolLike,
        );
      }
    }

    const poSources = [...assignmentsBySource.keys()].filter((source) => source.poKill === true);
    const poKillAssignments = poSources.flatMap((source) => assignmentsBySource.get(source) ?? []);
    const poDeathAssigned = game.anyOf(poKillAssignments, `${timing}_po_death_assigned`);
    const poSourceAvailable = game.anyOf(
      poSources.map((source) => effectiveAvailabilityBySource.get(source) as BoolLike),
      `${timing}_po_source_available`,
    );
    const chargedPoAvailable = game.anyOf(
      poSources
        .filter((source) => source.targetCountWhenAvailable === 3)
        .map((source) => effectiveAvailabilityBySource.get(source) as BoolLike),
      `${timing}_charged_po_available`,
    );
    const poNonDeathTargetAvailable = game.anyOf(
      poSources.flatMap((source) => nonDeathTargetsBySource.get(source) ?? []),
      `${timing}_po_non_death_target_available`,
    );
    const poChosePlayer = game.newBool(`${timing}_po_chose_player`);
    game.addImplication(poChosePlayer, poSourceAvailable);
    game.addImplication(poDeathAssigned, poChosePlayer);
    game.addImplication(chargedPoAvailable, poChosePlayer);
    game.addImplication(
      game.allOf(
        [poChosePlayer, game.not(poDeathAssigned, `${timing}_po_choice_caused_no_death`)],
        `${timing}_po_chose_without_a_death`,
      ),
      poNonDeathTargetAvailable,
    );
    poChosePlayerByTiming.set(timing, poChosePlayer);
  }

  const beforeInfoDeathsByTiming = new Map<Timing, ReadonlyMap<string, BoolLike>>();
  for (const [timing, deathsByPlayer] of beforeInfoAssignments) {
    const combinedDeathsByPlayer = new Map<string, BoolLike>();
    for (const [player, assignments] of deathsByPlayer) {
      combinedDeathsByPlayer.set(
        player,
        assignments.length === 1
          ? (assignments[0] as BoolLike)
          : game.anyOf(assignments, `${timing}_${slug(player)}_dies_before_info`),
      );
    }
    beforeInfoDeathsByTiming.set(timing, combinedDeathsByPlayer);
  }
  const demonKillAssignmentsByEventPlayer = new Map<string, BoolLike>();
  for (const [key, assignments] of demonKillAssignments) {
    demonKillAssignmentsByEventPlayer.set(
      key,
      assignments.length === 1
        ? (assignments[0] as BoolLike)
        : game.anyOf(assignments, `${slug(key)}_demon_kill_assignment`),
    );
  }
  return { beforeInfoDeathsByTiming, demonKillAssignmentsByEventPlayer };
}

function timelineEventPlayerKey(eventIndex: number, player: string): string {
  return `${eventIndex}\u0000${player}`;
}

function nightDeathSources(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  ctx: Omit<CompileCtx, "nameRoot">,
  poCharged: BoolLike,
  pukkaContext: PukkaContext,
  godfatherContext: GodfatherContext,
  goonContext: GoonContext,
  shabalothContext: ShabalothContext,
): readonly NightDeathSource[] {
  const timing = event.timing as Timing;
  return [
    ...atNightResolutionOrder(
      demonKillDeathSources(game, doc, event, poCharged, goonContext, shabalothContext),
      nightActionOrder("Po"),
    ),
    ...atNightResolutionOrder(pukkaDeathSources(game, doc, event, pukkaContext), nightActionOrder("Pukka")),
    ...atNightResolutionOrder(assassinDeathSources(game, doc, timing, goonContext), nightActionOrder("Assassin")),
    ...atNightResolutionOrder(
      godfatherDeathSources(game, doc, timing, godfatherContext),
      nightActionOrder("Godfather"),
    ),
    ...atNightResolutionOrder(grandmotherDeathSources(game, doc, event), nightActionOrder("Godfather") + 1),
    ...atNightResolutionOrder(gossipDeathSources(game, doc, event, ctx), nightActionOrder("Gossip")),
    ...atNightResolutionOrder(tinkerDeathSources(game, doc, timing), nightActionOrder("Tinker")),
    ...atNightResolutionOrder(moonchildDeathSources(game, doc, timing), nightActionOrder("Moonchild")),
    ...atNightResolutionOrder(acrobatDeathSources(game, doc, timing), nightActionOrder("Gossip") + 1),
    ...atNightResolutionOrder(gamblerDeathSources(game, doc, timing), nightActionOrder("Gambler")),
  ];
}

function atNightResolutionOrder(
  sources: readonly NightDeathSource[],
  resolutionOrder: number,
): readonly NightDeathSource[] {
  return sources.map((source) => ({ ...source, resolutionOrder }));
}

function assassinDeathSources(
  game: BOTCModel,
  doc: PuzzleDoc,
  timing: Timing,
  goonContext: GoonContext,
): readonly NightDeathSource[] {
  if (!doc.script.includes("Assassin")) return [];
  return livingPlayersAt(doc, timing).flatMap((actor): NightDeathSource[] => {
    const declaredClaim = doc.claims.find(
      (
        claim,
      ): claim is Extract<PuzzleDoc["claims"][number], { readonly type: "Assassin" }> & {
        readonly target: string;
      } => claim.type === "Assassin" && claim.name === actor && claim.target !== undefined && claim.timing === timing,
    );
    const canBeHiddenAssassin = doc.claims.some((claim) => claim.name === actor);
    if (declaredClaim === undefined && !canBeHiddenAssassin) return [];
    const preGoonHealthy = game.soberAndHealthyBeforeOwnDrunking(
      actor,
      timing,
      goonContext.drunkSourcesByActorTiming.get(`${actor}\u0000${timing}`) ?? [],
      `${timing}_${slug(actor)}_healthy_before_targeting_goon`,
    );
    const activeHealthy = game.allOf(
      [
        game.hasRoleAt(actor, "Assassin", timing),
        preGoonHealthy,
        game.not(
          game.abilityUsedBefore(actor, "Assassin", timing, `${timing}_${slug(actor)}_assassin_ability_used_before`),
          `${timing}_${slug(actor)}_assassin_ability_unused`,
        ),
      ],
      `${timing}_${slug(actor)}_healthy_assassin_kill`,
    );
    if (declaredClaim !== undefined && !nightDeathPlayersAt(doc, timing).has(declaredClaim.target))
      game.addFalse(activeHealthy);
    if (declaredClaim !== undefined) {
      return [
        {
          id: `${timing}_${slug(actor)}_assassin_declared`,
          players: [declaredClaim.target],
          available: activeHealthy,
          bypassesProtection: true,
          deathTiming: "beforeInfo",
        },
      ];
    }
    return [
      {
        id: `${timing}_${slug(actor)}_assassin`,
        available: activeHealthy,
        requiredWhenAvailable: false,
        bypassesProtection: true,
        deathTiming: "beforeInfo",
        constrainAssignment: (target, assignment) => {
          game.registerAbilityUse(actor, "Assassin", timing, assignment);
          game.registerAbilityTarget(actor, "Assassin", target, timing, assignment, nightActionOrder("Assassin"));
        },
      },
    ];
  });
}

function godfatherDeathSources(
  _game: BOTCModel,
  _doc: PuzzleDoc,
  timing: Timing,
  context: GodfatherContext,
): readonly NightDeathSource[] {
  return context.choices.flatMap((choice): NightDeathSource[] => {
    if (choice.timing !== timing) return [];
    return [...choice.targets].map(([target, selected]) => ({
      id: `${timing}_${slug(choice.actor)}_godfather_kills_${slug(target)}`,
      players: [target],
      available: selected,
      deathTiming: "beforeInfo",
    }));
  });
}

function grandmotherDeathSources(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): readonly NightDeathSource[] {
  if (!doc.script.includes("Grandmother")) return [];
  const timing = event.timing as Timing;
  return doc.claims.flatMap((claim, index): NightDeathSource[] => {
    if (claim.type !== "Grandmother" || claim.grandchild === undefined || !event.players.includes(claim.grandchild))
      return [];
    const activeHealthy = game.allOf(
      [game.hasRoleAt(claim.name, "Grandmother", timing), game.soberAndHealthy(claim.name, timing)],
      `${timing}_${slug(claim.name)}_healthy_grandmother_death`,
    );
    if (!event.players.includes(claim.name)) return [];
    return [
      {
        id: `${timing}_${slug(claim.name)}_grandmother_${index + 1}`,
        players: [claim.name],
        available: activeHealthy,
        requiresDemonKillOf: claim.grandchild,
        deathTiming: "beforeInfo",
      },
    ];
  });
}

function applyRequiredGrandmotherDeaths(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  demonAssignmentsByPlayer: ReadonlyMap<string, readonly BoolLike[]>,
): void {
  if (!doc.script.includes("Grandmother")) return;
  const timing = event.timing as Timing;
  for (const claim of doc.claims) {
    if (claim.type !== "Grandmother" || claim.grandchild === undefined) continue;
    const demonKilledGrandchild = game.anyOf(
      demonAssignmentsByPlayer.get(claim.grandchild) ?? [],
      `${timing}_${slug(claim.grandchild)}_demon_killed_grandchild`,
    );
    const trigger = game.allOf(
      [
        game.hasRoleAt(claim.name, "Grandmother", timing),
        game.soberAndHealthy(claim.name, timing),
        demonKilledGrandchild,
      ],
      `${timing}_${slug(claim.name)}_grandmother_death_required`,
    );
    if (!event.players.includes(claim.name)) game.addFalse(trigger);
  }
}

function moonchildDeathSources(game: BOTCModel, doc: PuzzleDoc, timing: Timing): readonly NightDeathSource[] {
  if (!doc.script.includes("Moonchild")) return [];
  return doc.claims.flatMap((claim, index): NightDeathSource[] => {
    if (claim.type !== "Moonchild" || claim.chosen === undefined || claim.timing === undefined) return [];
    if (followingNight(claim.timing as Timing) !== timing) return [];
    const moonchildDead =
      deadPlayersBefore(doc, claim.timing as Timing).has(claim.name) ||
      (doc.timeline ?? []).some(
        (event) => event.timing === claim.timing && isTimelineDeathEvent(event) && event.players.includes(claim.name),
      );
    if (!moonchildDead || !livingPlayersAt(doc, claim.timing as Timing).includes(claim.chosen)) return [];
    const activeHealthyGoodTarget = game.allOf(
      [
        game.actualIs(claim.name, "Moonchild"),
        game.soberAndHealthy(claim.name, timing),
        game.isGoodAt(claim.chosen, claim.timing as Timing),
      ],
      `${timing}_${slug(claim.name)}_moonchild_kills_${slug(claim.chosen)}`,
    );
    if (!nightDeathPlayersAt(doc, timing).has(claim.chosen)) {
      game.addImplication(activeHealthyGoodTarget, deathProtectionAt(game, doc, claim.chosen, timing));
      return [];
    }
    return [
      {
        id: `${timing}_${slug(claim.name)}_moonchild_${index + 1}`,
        players: [claim.chosen],
        available: activeHealthyGoodTarget,
        deathTiming: "beforeInfo",
      },
    ];
  });
}

function tinkerDeathSources(game: BOTCModel, doc: PuzzleDoc, timing: Timing): readonly NightDeathSource[] {
  if (!doc.script.includes("Tinker")) return [];
  return [
    {
      id: `${timing}_tinker_death`,
      available: game.roleInPlay("Tinker"),
      requiredWhenAvailable: false,
      deathTiming: "beforeInfo",
      constrainAssignment: (player, assignment) =>
        game.addImplication(
          assignment,
          game.allOf(
            [game.hasRoleAt(player, "Tinker", timing), game.soberAndHealthy(player, timing)],
            `${timing}_${slug(player)}_healthy_tinker_death`,
          ),
        ),
    },
  ];
}

function pukkaDeathSources(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  pukkaContext: PukkaContext,
): readonly NightDeathSource[] {
  const timing = event.timing as Timing;
  const poisonedPlayers = pukkaContext.poisonedBeforeResolutionByTiming.get(timing);
  const resolves = pukkaContext.resolvesByTiming.get(timing);
  if (poisonedPlayers === undefined || resolves === undefined) return [];
  return doc.players.map((player): NightDeathSource => ({
    id: `${timing}_pukka_kills_${slug(player)}`,
    players: [player],
    available: game.allOf(
      [
        resolves,
        poisonedPlayers.get(player) ?? game.constantBool(false, `${timing}_${slug(player)}_not_pukka_poisoned`),
      ],
      `${timing}_pukka_poisoned_target_${slug(player)}_dies`,
    ),
    demonKill: true,
    deathTiming: "beforeInfo",
    constrainAssignment: (victim, assignment) => constrainDemonKillVictim(game, doc, timing, victim, assignment),
  }));
}

function demonKillDeathSources(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  poCharged: BoolLike,
  goonContext: GoonContext,
  shabalothContext: ShabalothContext,
): readonly NightDeathSource[] {
  const timing = event.timing as Timing;
  const unblockedDemonKill = game.not(demonKillBlockedAt(game, doc, timing), `${timing}_demon_kill_not_blocked`);
  const demonRoleNames = doc.script
    .map(resolveRoleRef)
    .filter((role) => roleCharacterType(role) === CharacterType.Demon)
    .map(roleName);
  const sourceSpecs: readonly {
    readonly id: string;
    readonly roles: readonly string[];
    readonly activeIf?: BoolLike;
    readonly demonPath?: BoolLike;
    readonly maxAssignments: number;
    readonly requiredWhenAvailable: boolean;
    readonly targetCountWhenAvailable?: number;
    readonly poKill?: boolean;
  }[] = [
    {
      id: "demon_kill",
      roles: demonRoleNames.filter(
        (role) =>
          role !== "Leviathan" && role !== "Po" && role !== "Pukka" && role !== "Shabaloth" && role !== "Zombuul",
      ),
      maxAssignments: 1,
      requiredWhenAvailable: false,
      targetCountWhenAvailable: 1,
    },
    {
      id: "shabaloth_kill",
      roles: demonRoleNames.filter((role) => role === "Shabaloth"),
      maxAssignments: 2,
      requiredWhenAvailable: false,
      targetCountWhenAvailable: shabalothContext.choices.length > 0 ? 2 : undefined,
    },
    {
      id: "zombuul_kill",
      roles: demonRoleNames.filter((role) => role === "Zombuul"),
      activeIf: nobodyDiedDuringPreviousDay(game, doc, timing),
      demonPath: doc.script.includes("Zombuul")
        ? game.anyOf(
            doc.players.map((player) =>
              game.allOf(
                [game.actualIs(player, "Zombuul"), game.soberAndHealthy(player, timing)],
                `${timing}_${slug(player)}_healthy_zombuul_path`,
              ),
            ),
            `${timing}_healthy_zombuul_in_play`,
          )
        : game.constantBool(false, `${timing}_no_zombuul_on_script`),
      maxAssignments: 1,
      requiredWhenAvailable: false,
      targetCountWhenAvailable: 1,
    },
    {
      id: "po_regular_kill",
      roles: demonRoleNames.filter((role) => role === "Po"),
      activeIf: game.not(poCharged, `${timing}_po_not_charged`),
      maxAssignments: 1,
      requiredWhenAvailable: false,
      poKill: true,
    },
    {
      id: "po_charged_kill",
      roles: demonRoleNames.filter((role) => role === "Po"),
      activeIf: poCharged,
      maxAssignments: 3,
      requiredWhenAvailable: false,
      targetCountWhenAvailable: 3,
      poKill: true,
    },
  ].filter((source) => source.roles.length > 0);

  return sourceSpecs.map((source): NightDeathSource => ({
    id: `${timing}_${source.id}`,
    available: game.allOf(
      [
        source.demonPath ?? healthyLivingDemonPathBeforeDeathEvent(game, doc, event, new Set(source.roles)),
        unblockedDemonKill,
        ...(source.activeIf === undefined ? [] : [source.activeIf]),
      ],
      `${timing}_${source.id}_source_available`,
    ),
    maxAssignments: source.maxAssignments,
    targetCountWhenAvailable: source.targetCountWhenAvailable,
    requiredWhenAvailable: source.requiredWhenAvailable,
    poKill: source.poKill,
    demonKill: true,
    starpassesImp: source.roles.includes("Imp"),
    fangGuJumps: source.roles.includes("Fang Gu"),
    deathTiming: "beforeInfo",
    constrainAssignment: (player, assignment) => {
      if (source.roles.includes("Fang Gu")) {
        game.addImplication(assignment, fangGuDemonKillVictimAllowed(game, doc, event, player));
      }
      if (source.roles.includes("Shabaloth") && shabalothContext.choices.length > 0) {
        game.addImplication(assignment, shabalothTargetedAt(game, shabalothContext, player, timing));
      }
      constrainDemonKillVictim(game, doc, timing, player, assignment);
      if (doc.script.includes("Goon")) {
        const firstDemonOrder = Math.min(...source.roles.map((role) => nightActionOrder(role)));
        const goonTargetedEarlier = goonWasTargetedBefore(
          game,
          goonContext,
          timing,
          firstDemonOrder,
          `${timing}_${slug(source.id)}_goon_targeted_earlier`,
        );
        const killsGoon = game.allOf(
          [assignment, game.hasRoleAt(player, "Goon", timing)],
          `${timing}_${slug(source.id)}_targets_goon_${slug(player)}`,
        );
        game.addImplication(killsGoon, goonTargetedEarlier);
      }
    },
  }));
}

function constrainDemonKillVictim(
  game: BOTCModel,
  doc: PuzzleDoc,
  timing: Timing,
  player: string,
  assignment: BoolLike,
): void {
  const innkeeperProtected = innkeeperProtectionAt(game, doc, player, timing);
  game.addImplication(assignment, game.not(innkeeperProtected, `${timing}_${slug(player)}_not_innkeeper_protected`));
  if (!doc.script.includes("Soldier")) return;
  const soberHealthySoldier = game.allOf(
    [game.hasRoleAt(player, "Soldier", timing), game.soberAndHealthy(player, timing)],
    `${timing}_${slug(player)}_sober_healthy_soldier`,
  );
  game.addImplication(
    assignment,
    game.not(soberHealthySoldier, `${timing}_${slug(player)}_not_sober_healthy_soldier_demon_kill`),
  );
}

function demonKillProtectionAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  const soberHealthySoldier = doc.script.includes("Soldier")
    ? game.allOf(
        [game.hasRoleAt(player, "Soldier", timing), game.soberAndHealthy(player, timing)],
        `${timing}_${slug(player)}_sober_healthy_soldier_protection`,
      )
    : game.constantBool(false, `${timing}_${slug(player)}_no_soldier_protection`);
  return game.anyOf(
    [deathProtectionAt(game, doc, player, timing), soberHealthySoldier],
    `${timing}_${slug(player)}_survives_demon_target`,
  );
}

function innkeeperProtectionAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Innkeeper"))
    return game.constantBool(false, `${timing}_${slug(player)}_no_innkeeper_on_script`);
  const deadPlayers = deadPlayersBefore(doc, timing);
  const protectors = doc.claims.flatMap((claim) => {
    if (claim.type !== "Innkeeper" || deadPlayers.has(claim.name)) return [];
    return (claim.choices ?? []).flatMap((choice, index): BoolLike[] => {
      if (
        choice.timing !== timing ||
        choice.players.length !== 2 ||
        new Set(choice.players).size !== 2 ||
        choice.players.includes(claim.name) ||
        !choice.players.includes(player)
      )
        return [];
      return [
        game.allOf(
          [game.hasRoleAt(claim.name, "Innkeeper", timing), game.soberAndHealthy(claim.name, timing)],
          `${timing}_${slug(claim.name)}_innkeeper_choice_${index + 1}_protects_${slug(player)}`,
        ),
      ];
    });
  });
  return game.anyOf(protectors, `${timing}_${slug(player)}_innkeeper_protected`);
}

function nobodyDiedDuringPreviousDay(game: BOTCModel, doc: PuzzleDoc, timing: Timing): BoolLike {
  const match = /^night_(\d+)$/.exec(timing);
  if (match === null || Number(match[1]) <= 1) {
    return game.constantBool(false, `${timing}_zombuul_does_not_attack_first_night`);
  }
  const dayTiming = `day_${Number(match[1]) - 1}`;
  const someoneDied = (doc.timeline ?? []).some(
    (event) => event.timing === dayTiming && isTimelineDeathEvent(event) && event.players.length > 0,
  );
  return game.constantBool(!someoneDied, `${timing}_zombuul_${someoneDied ? "blocked_by_day_death" : "can_attack"}`);
}

function fangGuDemonKillVictimAllowed(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  player: string,
): BoolLike {
  const timing = event.timing as Timing;
  const outsiderBeforeEvent = characterTypeBeforeEvent(game, doc, player, CharacterType.Outsider, event);
  return game.anyOf(
    [
      game.not(outsiderBeforeEvent, `${timing}_${slug(player)}_not_outsider_for_fang_gu_kill`),
      fangGuJumpedBeforeDeathEvent(game, doc, event),
      livingNonFangGuDemonPathBeforeDeathEvent(game, doc, event),
    ],
    `${timing}_${slug(player)}_fang_gu_demon_kill_victim_allowed`,
  );
}

type HealthAt = (player: string, timing: Timing, name: string) => BoolLike;

function demonKillBlockedAt(
  game: BOTCModel,
  doc: PuzzleDoc,
  timing: Timing,
  healthAt: HealthAt = (player, healthTiming) => game.soberAndHealthy(player, healthTiming),
): BoolLike {
  return game.anyOf(
    [
      ...princessDemonKillBlockers(game, doc, timing, healthAt),
      ...exorcistDemonKillBlockers(game, doc, timing, healthAt),
    ],
    `${timing}_demon_kill_blocked`,
  );
}

function princessDemonKillBlockers(
  game: BOTCModel,
  doc: PuzzleDoc,
  timing: Timing,
  healthAt: HealthAt,
): readonly BoolLike[] {
  if (!doc.script.includes("Princess")) return [];
  const deadPlayers = deadPlayersBefore(doc, timing);
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Princess" || deadPlayers.has(claim.name)) return [];
    return (claim.nominations ?? []).flatMap((nomination, index): BoolLike[] => {
      const nominationTiming = nomination.timing as Timing | undefined;
      if (nominationTiming === undefined || followingNight(nominationTiming) !== timing) return [];
      if (!executionPlayersAt(doc, nominationTiming).has(nomination.player)) return [];
      return [
        game.allOf(
          [
            game.hasRoleAt(claim.name, "Princess", timing),
            healthAt(claim.name, timing, `${timing}_${slug(claim.name)}_princess_healthy_before_demon_action`),
          ],
          `${timing}_${slug(claim.name)}_princess_nomination_${index + 1}_blocks_demon`,
        ),
      ];
    });
  });
}

function exorcistDemonKillBlockers(
  game: BOTCModel,
  doc: PuzzleDoc,
  timing: Timing,
  healthAt: HealthAt,
): readonly BoolLike[] {
  if (!doc.script.includes("Exorcist")) return [];
  const deadPlayers = deadPlayersBefore(doc, timing);
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Exorcist" || deadPlayers.has(claim.name)) return [];
    return (claim.choices ?? []).flatMap((choice, index): BoolLike[] => {
      if (choice.timing !== timing) return [];
      return [
        game.allOf(
          [
            game.hasRoleAt(claim.name, "Exorcist", timing),
            healthAt(claim.name, timing, `${timing}_${slug(claim.name)}_exorcist_healthy_before_demon_action`),
            game.isDemonAt(choice.player, timing),
          ],
          `${timing}_${slug(claim.name)}_exorcist_choice_${index + 1}_blocks_demon`,
        ),
      ];
    });
  });
}

function applyImpStarpass(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  deadPlayer: string,
  assignment: BoolLike,
  roleTimings: readonly Timing[],
): void {
  if (!doc.script.includes("Imp")) return;
  const timing = event.timing as Timing;
  const starpass = game.allOf(
    [assignment, roleAtBeforeEvent(game, doc, deadPlayer, "Imp", event)],
    `${timing}_${slug(deadPlayer)}_imp_starpass`,
  );
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  const successors = candidates.map((candidate) => {
    const successor = game.newBool(`${timing}_${slug(deadPlayer)}_starpass_to_${slug(candidate)}`);
    game.addImplication(successor, starpass);
    game.addImplication(successor, isMinionBeforeEvent(game, doc, candidate, event));
    return { player: candidate, value: successor };
  });

  game.addEnforcedExactlyN(
    successors.map(({ value }) => value),
    1,
    starpass,
  );
  game.addEnforcedExactlyN(
    successors.map(({ value }) => value),
    0,
    starpass.not(),
  );

  const futureTimings = roleTimings.filter((futureTiming) => phaseStartOrder(futureTiming) >= phaseStartOrder(timing));
  for (const futureTiming of futureTimings) {
    game.removeRoleAt(deadPlayer, "Imp", futureTiming, starpass);
    for (const { player, value } of successors) {
      game.addRoleAt(player, "Imp", futureTiming, value);
      for (const role of doc.script) {
        if (role === "Imp") continue;
        game.removeRoleAt(player, resolveRoleRef(role), futureTiming, value);
      }
    }
  }
}

function applyFangGuJump(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  deadPlayer: string,
  assignment: BoolLike,
  roleTimings: readonly Timing[],
): void {
  if (!doc.script.includes("Fang Gu")) return;
  const timing = event.timing as Timing;
  const jump = game.allOf(
    [assignment, roleAtBeforeEvent(game, doc, deadPlayer, "Fang Gu", event)],
    `${timing}_${slug(deadPlayer)}_fang_gu_jump`,
  );
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  const successors = candidates.map((candidate) => {
    const successor = game.newBool(`${timing}_${slug(deadPlayer)}_fang_gu_jump_to_${slug(candidate)}`);
    game.addImplication(successor, jump);
    game.addImplication(successor, characterTypeBeforeEvent(game, doc, candidate, CharacterType.Outsider, event));
    return { player: candidate, value: successor };
  });

  game.addEnforcedExactlyN(
    successors.map(({ value }) => value),
    1,
    jump,
  );
  game.addEnforcedExactlyN(
    successors.map(({ value }) => value),
    0,
    jump.not(),
  );

  const futureTimings = roleTimings.filter((futureTiming) => phaseStartOrder(futureTiming) >= phaseStartOrder(timing));
  for (const futureTiming of futureTimings) {
    game.removeRoleAt(deadPlayer, "Fang Gu", futureTiming, jump);
    for (const { player, value } of successors) {
      game.addRoleAt(player, "Fang Gu", futureTiming, value);
      for (const role of doc.script) {
        if (role === "Fang Gu") continue;
        game.removeRoleAt(player, resolveRoleRef(role), futureTiming, value);
      }
    }
  }
}

function applyScarletWomanCatch(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  deadPlayer: string,
  assignment: BoolLike,
  roleTimings: readonly Timing[],
  options: { readonly excludedRoles?: readonly string[] } = {},
): void {
  if (!doc.script.includes("Scarlet Woman")) return;
  if (livingPlayersBeforeDeathEvent(doc, event).length < 5) return;
  const timing = event.timing as Timing;
  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => {
    if (roleCharacterType(role) !== CharacterType.Demon) return false;
    const name = roleName(role);
    return name !== "Zombuul" && name !== "Legion" && name !== "Riot" && !options.excludedRoles?.includes(name);
  });
  if (demonRoles.length === 0) return;

  for (const demonRole of demonRoles) {
    const demonRoleName = roleName(demonRole);
    const caught = game.allOf(
      [assignment, roleAtBeforeEvent(game, doc, deadPlayer, demonRole, event)],
      `${timing}_${slug(deadPlayer)}_${slug(demonRoleName)}_scarlet_woman_catch`,
    );
    const candidates = livingPlayersAfterDeathEvent(doc, event);
    const successors = candidates.map((candidate) => {
      const successor = game.newBool(
        `${timing}_${slug(deadPlayer)}_${slug(demonRoleName)}_scarlet_woman_to_${slug(candidate)}`,
      );
      game.addImplication(successor, caught);
      game.addImplication(successor, roleAtBeforeEvent(game, doc, candidate, "Scarlet Woman", event));
      return { player: candidate, value: successor };
    });

    game.addEnforcedExactlyN(
      successors.map(({ value }) => value),
      1,
      caught,
    );
    game.addEnforcedExactlyN(
      successors.map(({ value }) => value),
      0,
      caught.not(),
    );

    const futureTimings = roleTimings.filter(
      (futureTiming) => phaseStartOrder(futureTiming) >= phaseStartOrder(timing),
    );
    for (const futureTiming of futureTimings) {
      game.removeRoleAt(deadPlayer, demonRole, futureTiming, caught);
      for (const { player, value } of successors) {
        game.addRoleAt(player, demonRole, futureTiming, value);
        for (const role of doc.script) {
          if (role === demonRoleName) continue;
          game.removeRoleAt(player, resolveRoleRef(role), futureTiming, value);
        }
      }
    }
  }
}

function gossipDeathSources(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  ctx: Omit<CompileCtx, "nameRoot">,
): readonly NightDeathSource[] {
  const timing = event.timing as Timing;
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Gossip") return [];
    return (claim.statements ?? []).flatMap((statement, index): NightDeathSource[] => {
      const statementTiming = statement.timing as Timing | undefined;
      if (statementTiming === undefined || followingNight(statementTiming) !== event.timing) return [];
      const learned = compile(statement.expression, game, {
        ...ctx,
        nameRoot: `${slug(claim.name)}_gossip_source_${index + 1}`,
        timing: statementTiming,
      });
      return [
        {
          id: `${event.timing}_${slug(claim.name)}_gossip_${index + 1}`,
          deathTiming: "beforeInfo",
          requiresAliveAtResolution: claim.name,
          available: game.allOf(
            [
              game.hasRoleAt(claim.name, "Gossip", statementTiming),
              game.hasRoleAt(claim.name, "Gossip", timing),
              game.soberAndHealthy(claim.name, timing),
              learned,
            ],
            `${event.timing}_${slug(claim.name)}_gossip_${index + 1}_source_available`,
          ),
        },
      ];
    });
  });
}

function acrobatDeathSources(game: BOTCModel, doc: PuzzleDoc, timing: Timing): readonly NightDeathSource[] {
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Acrobat") return [];
    return (claim.choices ?? []).flatMap((choice, index): NightDeathSource[] => {
      if (!choice.died || choice.timing !== timing) return [];
      const targetDrunkOrPoisoned = game.anyOf(
        [game.isDroisonedAt(choice.player, timing), game.noDashiiPoisonedAt(choice.player, timing)],
        `${timing}_${slug(claim.name)}_acrobat_${index + 1}_${slug(choice.player)}_drunk_or_poisoned_source`,
      );
      return [
        {
          id: `${timing}_${slug(claim.name)}_acrobat_${index + 1}`,
          players: [claim.name],
          available: game.allOf(
            [
              game.hasRoleAt(claim.name, "Acrobat", timing),
              game.soberAndHealthy(claim.name, timing),
              targetDrunkOrPoisoned,
            ],
            `${timing}_${slug(claim.name)}_acrobat_${index + 1}_source_available`,
          ),
        },
      ];
    });
  });
}

function gamblerDeathSources(game: BOTCModel, doc: PuzzleDoc, timing: Timing): readonly NightDeathSource[] {
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Gambler") return [];
    return (claim.guesses ?? []).flatMap((guess, index): NightDeathSource[] => {
      if (guess.timing !== timing) return [];
      const correct = game.registersAsRole(
        guess.player,
        resolveRoleRef(guess.role),
        `${timing}_${slug(claim.name)}_gambler_${index + 1}_${slug(guess.player)}_correct_source`,
      );
      return [
        {
          id: `${timing}_${slug(claim.name)}_gambler_${index + 1}`,
          players: [claim.name],
          available: game.allOf(
            [
              game.hasRoleAt(claim.name, "Gambler", timing),
              game.soberAndHealthy(claim.name, timing),
              game.not(correct, `${timing}_${slug(claim.name)}_gambler_${index + 1}_wrong_source`),
            ],
            `${timing}_${slug(claim.name)}_gambler_${index + 1}_source_available`,
          ),
        },
      ];
    });
  });
}

function livingDemonPathBeforeDeathEvent(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  allowedRoles?: ReadonlySet<string>,
): BoolLike {
  const livingPlayers = livingPlayersBeforeDeathEvent(doc, event);
  const livingPlayerSet = new Set(livingPlayers);
  const deadPlayers = doc.players.filter((player) => !livingPlayerSet.has(player));
  const demonRoles = doc.script
    .map(resolveRoleRef)
    .filter(
      (role) =>
        roleCharacterType(role) === CharacterType.Demon &&
        (allowedRoles === undefined || allowedRoles.has(roleName(role))),
    );
  const livingDemonBeforeDeath = livingPlayers.flatMap((player) =>
    demonRoles.map((role) => roleAtBeforeEvent(game, doc, player, role, event)),
  );
  const possibleSuccessions: BoolLike[] = [];

  if (demonRoles.some((role) => roleName(role) === "Imp")) {
    possibleSuccessions.push(
      game.allOf(
        [
          game.anyOf(
            deadPlayers.map((player) => game.actualIs(player, "Imp")),
            `${event.timing}_dead_imp_before_death_event`,
          ),
          game.anyOf(
            livingPlayers.map((player) => isMinionBeforeEvent(game, doc, player, event)),
            `${event.timing}_living_minion_before_death_event`,
          ),
        ],
        `${event.timing}_imp_successor_alive_before_death_event`,
      ),
    );
  }

  if (doc.script.includes("Scarlet Woman")) {
    const deadNonImpDemons = deadPlayers.flatMap((player) =>
      demonRoles.filter((role) => roleName(role) !== "Imp").map((role) => game.actualIs(player, role)),
    );
    possibleSuccessions.push(
      game.allOf(
        [
          game.anyOf(deadNonImpDemons, `${event.timing}_dead_non_imp_demon_before_death_event`),
          game.anyOf(
            livingPlayers.map((player) => roleAtBeforeEvent(game, doc, player, "Scarlet Woman", event)),
            `${event.timing}_living_scarlet_woman_before_death_event`,
          ),
        ],
        `${event.timing}_scarlet_woman_successor_alive_before_death_event`,
      ),
    );
  }

  return game.anyOf(
    [...livingDemonBeforeDeath, ...possibleSuccessions],
    `${event.timing}_living_demon_path_before_death_event`,
  );
}

function healthyLivingDemonPathBeforeDeathEvent(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  allowedRoles: ReadonlySet<string>,
): BoolLike {
  const timing = event.timing as Timing;
  const livingPlayers = livingPlayersBeforeDeathEvent(doc, event);
  const livingPlayerSet = new Set(livingPlayers);
  const deadPlayers = doc.players.filter((player) => !livingPlayerSet.has(player));
  const demonRoles = doc.script
    .map(resolveRoleRef)
    .filter((role) => roleCharacterType(role) === CharacterType.Demon && allowedRoles.has(roleName(role)));
  const healthyLivingDemons = livingPlayers.flatMap((player) =>
    demonRoles.map((role) =>
      game.allOf(
        [roleAtBeforeEvent(game, doc, player, role, event), game.soberAndHealthy(player, timing)],
        `${timing}_${slug(player)}_${slug(roleName(role))}_healthy_demon_path`,
      ),
    ),
  );
  const healthySuccessions: BoolLike[] = [];

  if (demonRoles.some((role) => roleName(role) === "Imp")) {
    healthySuccessions.push(
      game.allOf(
        [
          game.anyOf(
            deadPlayers.map((player) => game.actualIs(player, "Imp")),
            `${timing}_dead_imp_before_healthy_demon_path`,
          ),
          game.anyOf(
            livingPlayers.map((player) =>
              game.allOf(
                [isMinionBeforeEvent(game, doc, player, event), game.soberAndHealthy(player, timing)],
                `${timing}_${slug(player)}_healthy_imp_successor`,
              ),
            ),
            `${timing}_healthy_imp_successor_alive`,
          ),
        ],
        `${timing}_healthy_imp_succession_path`,
      ),
    );
  }

  if (doc.script.includes("Scarlet Woman")) {
    const deadNonImpDemons = deadPlayers.flatMap((player) =>
      demonRoles.filter((role) => roleName(role) !== "Imp").map((role) => game.actualIs(player, role)),
    );
    healthySuccessions.push(
      game.allOf(
        [
          game.anyOf(deadNonImpDemons, `${timing}_dead_non_imp_demon_before_healthy_path`),
          game.anyOf(
            livingPlayers.map((player) =>
              game.allOf(
                [roleAtBeforeEvent(game, doc, player, "Scarlet Woman", event), game.soberAndHealthy(player, timing)],
                `${timing}_${slug(player)}_healthy_scarlet_woman_successor`,
              ),
            ),
            `${timing}_healthy_scarlet_woman_successor_alive`,
          ),
        ],
        `${timing}_healthy_scarlet_woman_succession_path`,
      ),
    );
  }

  return game.anyOf(
    [...healthyLivingDemons, ...healthySuccessions],
    `${timing}_healthy_living_demon_path_before_death_event`,
  );
}

function livingNonFangGuDemonPathBeforeDeathEvent(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const livingPlayers = livingPlayersBeforeDeathEvent(doc, event);
  const livingPlayerSet = new Set(livingPlayers);
  const deadPlayers = doc.players.filter((player) => !livingPlayerSet.has(player));
  const demonRoles = doc.script
    .map(resolveRoleRef)
    .filter((role) => roleCharacterType(role) === CharacterType.Demon && roleName(role) !== "Fang Gu");
  const livingDemonBeforeDeath = livingPlayers.flatMap((player) =>
    demonRoles.map((role) => roleAtBeforeEvent(game, doc, player, role, event)),
  );
  const possibleSuccessions: BoolLike[] = [];

  if (doc.script.includes("Imp")) {
    possibleSuccessions.push(
      game.allOf(
        [
          game.anyOf(
            deadPlayers.map((player) => game.actualIs(player, "Imp")),
            `${event.timing}_dead_imp_before_death_event_non_fang_gu`,
          ),
          game.anyOf(
            livingPlayers.map((player) => isMinionBeforeEvent(game, doc, player, event)),
            `${event.timing}_living_minion_before_death_event_non_fang_gu`,
          ),
        ],
        `${event.timing}_imp_successor_alive_before_death_event_non_fang_gu`,
      ),
    );
  }

  if (doc.script.includes("Scarlet Woman")) {
    const deadNonImpNonFangGuDemons = deadPlayers.flatMap((player) =>
      demonRoles.filter((role) => roleName(role) !== "Imp").map((role) => game.actualIs(player, role)),
    );
    possibleSuccessions.push(
      game.allOf(
        [
          game.anyOf(deadNonImpNonFangGuDemons, `${event.timing}_dead_non_imp_non_fang_gu_demon_before_death_event`),
          game.anyOf(
            livingPlayers.map((player) => roleAtBeforeEvent(game, doc, player, "Scarlet Woman", event)),
            `${event.timing}_living_scarlet_woman_before_death_event_non_fang_gu`,
          ),
        ],
        `${event.timing}_scarlet_woman_successor_alive_before_death_event_non_fang_gu`,
      ),
    );
  }

  return game.anyOf(
    [...livingDemonBeforeDeath, ...possibleSuccessions],
    `${event.timing}_living_non_fang_gu_demon_path_before_death_event`,
  );
}

function fangGuJumpedBeforeDeathEvent(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const priorDeaths =
    doc.timeline?.filter(
      (priorEvent) => priorEvent.type === "nightDeath" && deathEventOrder(priorEvent) < deathEventOrder(event),
    ) ?? [];
  return game.anyOf(
    priorDeaths.flatMap((priorEvent) =>
      priorEvent.players.map((player) => roleAtBeforeEvent(game, doc, player, "Fang Gu", priorEvent)),
    ),
    `${event.timing}_fang_gu_jump_spent_before_death_event`,
  );
}

function livingPlayersBeforeDeathEvent(
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): readonly string[] {
  const deadPlayers = deadPlayersBefore(doc, event.timing as Timing);
  return doc.players.filter((player) => !deadPlayers.has(player));
}

function followingNight(timing: Timing): Timing | undefined {
  const match = /^day_(\d+)$/.exec(timing);
  if (match === null) return undefined;
  return `night_${Number(match[1]) + 1}` as Timing;
}

function previousNight(timing: Timing): Timing | undefined {
  const match = /^night_(\d+)$/.exec(timing);
  if (match === null || Number(match[1]) <= 1) return undefined;
  return `night_${Number(match[1]) - 1}` as Timing;
}

function previousDayForNight(timing: Timing): Timing | undefined {
  const match = /^night_(\d+)$/.exec(timing);
  if (match === null || Number(match[1]) <= 1) return undefined;
  return `day_${Number(match[1]) - 1}` as Timing;
}

function nightDeathPlayersAt(doc: PuzzleDoc, timing: Timing): ReadonlySet<string> {
  const players = new Set<string>();
  for (const event of doc.timeline ?? []) {
    if (event.type !== "nightDeath" || event.timing !== timing) continue;
    for (const player of event.players) players.add(player);
  }
  return players;
}

function healthTimingForDayAbility(timing: Timing): Timing {
  const match = /^day_(\d+)$/.exec(timing);
  return match === null ? timing : (`night_${Number(match[1])}` as Timing);
}

function executionPlayersAt(doc: PuzzleDoc, timing: Timing): ReadonlySet<string> {
  const players = new Set<string>();
  for (const event of doc.timeline ?? []) {
    if (event.type !== "execution" || event.timing !== timing) continue;
    for (const player of event.players) players.add(player);
  }
  return players;
}

function livingPlayersAfterTimeline(doc: PuzzleDoc): readonly string[] {
  const deadPlayers = new Set<string>();
  for (const event of doc.timeline ?? []) {
    if (isTimelineDeathEvent(event)) {
      for (const player of event.players) deadPlayers.add(player);
    } else if (event.type === "resurrection") {
      for (const player of event.players) deadPlayers.delete(player);
    }
  }
  return doc.players.filter((player) => !deadPlayers.has(player));
}

function usesMalfunctionCount(claim: PuzzleDoc["claims"][number]): boolean {
  if (claim.type === "Mathematician" && (claim.malfunctions?.length ?? 0) > 0) return true;
  return claim.info?.some((info) => info.expression?.includes("malfunctions(")) ?? false;
}

function applyTimelineClaimContext(
  claim: PuzzleDoc["claims"][number],
  doc: PuzzleDoc,
  game: BOTCModel,
  nightDeathTiming: NightDeathTimingContext,
): ClaimWithTimelineContext {
  if (claim.type === "Slayer" && claim.timing !== undefined) {
    return { ...claim, alivePlayerCount: livingPlayersAt(doc, claim.timing as Timing).length };
  }
  if (claim.type === "Legionary" && claim.counts !== undefined) {
    return {
      ...claim,
      counts: claim.counts.map((count, index) => {
        const timing = (count.timing ?? `night_${index + 1}`) as Timing;
        return { ...count, timing, alivePlayers: livingPlayersAt(doc, timing) };
      }),
    };
  }
  if (claim.type !== "Empath" || claim.count === undefined || claim.timing === undefined) {
    if (claim.type !== "Oracle" || claim.count === undefined || claim.timing === undefined) {
      return claim;
    }
    const timing = claim.timing as Timing;
    const deadPlayerOptions = oracleDeadPlayerOptionsAt(game, doc, timing, nightDeathTiming);
    if (deadPlayerOptions.length === 1) return { ...claim, deadPlayers: deadPlayerOptions[0]?.deadPlayers };
    return { ...claim, deadPlayerOptions };
  }
  const player = claim.name;
  const timing = claim.timing as Timing;
  const neighborOptions = livingNeighborOptionsAt(game, doc, player, timing, nightDeathTiming);
  if (neighborOptions.length === 1) return { ...claim, neighbors: neighborOptions[0]?.neighbors };
  return { ...claim, neighborOptions };
}

function oracleDeadPlayerOptionsAt(
  game: BOTCModel,
  doc: PuzzleDoc,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): readonly OracleDeadPlayerOption[] {
  const deadPlayers = deadPlayersBefore(doc, timing);
  const sameNightDeaths = [...(nightDeathTiming.beforeInfoDeathsByTiming.get(timing)?.entries() ?? [])].filter(
    ([deadPlayer]) => !deadPlayers.has(deadPlayer),
  );
  if (sameNightDeaths.length === 0) {
    return [
      {
        deadPlayers: playersInDocOrder(doc, deadPlayers),
        activeIf: game.constantBool(true, `${timing}_oracle_dead_players_static`),
      },
    ];
  }

  const optionsByDeadPlayers = new Map<string, { deadPlayers: readonly string[]; activeIf: BoolLike[] }>();
  const subsetCount = 1 << sameNightDeaths.length;
  for (let mask = 0; mask < subsetCount; mask += 1) {
    const optionDeadPlayers = new Set(deadPlayers);
    const conditions: BoolLike[] = [];
    for (let index = 0; index < sameNightDeaths.length; index += 1) {
      const [deadPlayer, beforeInfo] = sameNightDeaths[index] as [string, BoolLike];
      if ((mask & (1 << index)) === 0) {
        conditions.push(game.not(beforeInfo, `${timing}_${slug(deadPlayer)}_alive_for_oracle_${mask}`));
        continue;
      }
      optionDeadPlayers.add(deadPlayer);
      conditions.push(beforeInfo);
    }
    const activeIf = game.allOf(conditions, `${timing}_oracle_dead_player_option_${mask + 1}`);
    const deadPlayerList = playersInDocOrder(doc, optionDeadPlayers);
    const key = deadPlayerList.join("\u0000");
    const existing = optionsByDeadPlayers.get(key);
    if (existing === undefined) optionsByDeadPlayers.set(key, { deadPlayers: deadPlayerList, activeIf: [activeIf] });
    else existing.activeIf.push(activeIf);
  }

  return [...optionsByDeadPlayers.values()].map(({ deadPlayers, activeIf }, index) => ({
    deadPlayers,
    activeIf:
      activeIf.length === 1
        ? (activeIf[0] as BoolLike)
        : game.anyOf(activeIf, `${timing}_oracle_dead_players_${index + 1}`),
  }));
}

function livingNeighborOptionsAt(
  game: BOTCModel,
  doc: PuzzleDoc,
  player: string,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): readonly EmpathNeighborOption[] {
  const deadPlayers = deadPlayersBefore(doc, timing);
  const sameNightDeaths = [...(nightDeathTiming.beforeInfoDeathsByTiming.get(timing)?.entries() ?? [])].filter(
    ([deadPlayer]) => !deadPlayers.has(deadPlayer),
  );
  if (sameNightDeaths.length === 0) {
    return [
      {
        neighbors: livingNeighborsWithDeadPlayers(doc, player, deadPlayers),
        activeIf: game.constantBool(true, `${timing}_${slug(player)}_empath_neighbors_static`),
      },
    ];
  }

  const optionsByNeighbors = new Map<string, { neighbors: [string, string]; activeIf: BoolLike[] }>();
  const subsetCount = 1 << sameNightDeaths.length;
  for (let mask = 0; mask < subsetCount; mask += 1) {
    const optionDeadPlayers = new Set(deadPlayers);
    const conditions: BoolLike[] = [];
    for (let index = 0; index < sameNightDeaths.length; index += 1) {
      const [deadPlayer, beforeInfo] = sameNightDeaths[index] as [string, BoolLike];
      if ((mask & (1 << index)) === 0) {
        conditions.push(game.not(beforeInfo, `${timing}_${slug(deadPlayer)}_survives_until_info_${mask}`));
        continue;
      }
      optionDeadPlayers.add(deadPlayer);
      conditions.push(beforeInfo);
    }
    const activeIf = game.allOf(conditions, `${timing}_${slug(player)}_empath_neighbor_option_${mask + 1}`);
    const neighbors = livingNeighborsWithDeadPlayers(doc, player, optionDeadPlayers);
    const key = neighbors.join("\u0000");
    const existing = optionsByNeighbors.get(key);
    if (existing === undefined) optionsByNeighbors.set(key, { neighbors, activeIf: [activeIf] });
    else existing.activeIf.push(activeIf);
  }

  return [...optionsByNeighbors.values()].map(({ neighbors, activeIf }, index) => ({
    neighbors,
    activeIf:
      activeIf.length === 1
        ? (activeIf[0] as BoolLike)
        : game.anyOf(activeIf, `${timing}_${slug(player)}_empath_neighbors_${index + 1}`),
  }));
}

function applyPoisonerSources(game: BOTCModel, doc: PuzzleDoc, nightDeathTiming: NightDeathTimingContext): void {
  if (!doc.script.includes("Poisoner")) return;
  for (const timing of game.droisonTimingKeys) {
    const poisonerCanAct = roleCanUseAbilityAt(game, doc, "Poisoner", timing as Timing, nightDeathTiming);
    const poisonerDiesBeforeInfo = roleDiesBeforeInfoAt(game, "Poisoner", timing as Timing, nightDeathTiming);
    game.addPoisonerEffect(timing as Timing, {
      activeIf: game.allOf(
        [poisonerCanAct, game.not(poisonerDiesBeforeInfo, `${timing}_poisoner_survives_until_info`)],
        `${timing}_poisoner_active_for_timing`,
      ),
    });
  }
}

function applyVigormortisPoisonSources(
  game: BOTCModel,
  doc: PuzzleDoc,
  nightDeathTiming: NightDeathTimingContext,
): void {
  if (!doc.script.includes("Vigormortis")) return;
  if (!(doc.timeline ?? []).some((event) => event.sourceActedBeforeDeath === true)) return;
  for (const [eventIndex, event] of (doc.timeline ?? []).entries()) {
    if (event.type !== "nightDeath") continue;
    for (const deadPlayer of event.players) {
      const demonKill = nightDeathTiming.demonKillAssignmentsByEventPlayer.get(
        timelineEventPlayerKey(eventIndex, deadPlayer),
      );
      if (demonKill === undefined) continue;
      const active = game.allOf(
        [
          demonKill,
          isMinionBeforeEvent(game, doc, deadPlayer, event),
          livingVigormortisPathBeforeDeathEvent(game, doc, event),
        ],
        `${event.timing}_${slug(deadPlayer)}_vigormortis_killed_minion_poison`,
      );
      const timings = [...game.droisonTimingKeys]
        .filter((timing): timing is Timing => /^(night|day)_\d+$/.test(timing))
        .filter((timing) => phaseStartOrder(timing) > phaseStartOrder(event.timing as Timing));
      game.addPersistentPoisonSource(
        timings,
        game.neighbors(deadPlayer),
        active,
        `${event.timing}_${slug(deadPlayer)}_vigormortis`,
      );
    }
  }
}

function roleCanUseAbilityAt(
  game: BOTCModel,
  doc: PuzzleDoc,
  role: RoleRef,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): BoolLike {
  const roleRef = resolveRoleRef(roleName(role));
  const activeSources = [roleAliveAt(game, doc, roleRef, timing)];
  if (roleCharacterType(roleRef) === CharacterType.Minion) {
    activeSources.push(vigormortisKilledMinionRoleBeforeTiming(game, doc, roleRef, timing, nightDeathTiming));
  }
  return game.anyOf(activeSources, `${slug(roleName(roleRef))}_can_use_ability_at_${timing}`);
}

function vigormortisKilledMinionRoleBeforeTiming(
  game: BOTCModel,
  doc: PuzzleDoc,
  role: RoleRef,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): BoolLike {
  if (!doc.script.includes("Vigormortis")) {
    return game.constantBool(false, `${timing}_${slug(roleName(role))}_not_kept_by_vigormortis`);
  }
  const timingOrder = phaseStartOrder(timing);
  const options = (doc.timeline ?? []).flatMap((event, eventIndex): BoolLike[] => {
    if (event.type !== "nightDeath" || deathEventOrder(event) >= timingOrder) return [];
    return event.players.flatMap((player): BoolLike[] => {
      const demonKill = nightDeathTiming.demonKillAssignmentsByEventPlayer.get(
        timelineEventPlayerKey(eventIndex, player),
      );
      if (demonKill === undefined) return [];
      return [
        game.allOf(
          [
            demonKill,
            roleAtBeforeEvent(game, doc, player, role, event),
            livingVigormortisPathBeforeDeathEvent(game, doc, event),
          ],
          `${timing}_${slug(player)}_${slug(roleName(role))}_kept_by_vigormortis`,
        ),
      ];
    });
  });
  return game.anyOf(options, `${timing}_${slug(roleName(role))}_vigormortis_kept_ability`);
}

function livingVigormortisPathBeforeDeathEvent(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  if (!doc.script.includes("Vigormortis")) {
    return game.constantBool(false, `${event.timing}_no_vigormortis_before_death_event`);
  }
  return game.anyOf(
    livingPlayersBeforeDeathEvent(doc, event).map((player) =>
      roleAtBeforeEvent(game, doc, player, "Vigormortis", event),
    ),
    `${event.timing}_living_vigormortis_path_before_death_event`,
  );
}

function roleDiesBeforeInfoAt(
  game: BOTCModel,
  role: RoleRef,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): BoolLike {
  const beforeInfoDeaths = nightDeathTiming.beforeInfoDeathsByTiming.get(timing);
  if (beforeInfoDeaths === undefined) return game.constantBool(false, `${timing}_${slug(roleName(role))}_not_dying`);
  return game.anyOf(
    [...beforeInfoDeaths.entries()].map(([player, diesBeforeInfo]) =>
      game.allOf(
        [diesBeforeInfo, game.hasRoleAt(player, role, timing)],
        `${timing}_${slug(player)}_${slug(roleName(role))}_dies_before_info`,
      ),
    ),
    `${timing}_${slug(roleName(role))}_dies_before_info`,
  );
}

function applyWidowSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Widow")) return;
  const timings = [...game.droisonTimingKeys].filter((timing): timing is Timing => timing !== "default");
  game.addWidowEffect({ timings, activeIf: roleAliveAt(game, doc, "Widow", "night_1") });
}

function applyXaanActivity(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Xaan")) return;
  for (let count = 0; count <= doc.players.length; count += 1) {
    const timing = `night_${count}` as Timing;
    game.setRoleActiveAt("Xaan", timing, roleAliveAt(game, doc, "Xaan", timing));
  }
}

function applyWidowCallClaims(game: BOTCModel, doc: PuzzleDoc): void {
  const heardCallClaims = doc.claims.filter((claim) => claim.heardWidowCall === true);
  for (const claim of doc.claims) {
    if (claim.heardWidowCall !== true) continue;
    const widowInPlay = doc.script.includes("Widow")
      ? game.roleInPlay("Widow")
      : game.constantBool(false, `${slug(claim.name)}_heard_widow_without_widow_on_script`);
    game.addImplication(claimantIsGoodWhenClaimed(game, claim), widowInPlay);
  }
  if (!doc.script.includes("Widow")) return;
  game.addImplication(
    game.roleInPlay("Widow"),
    game.anyOf(
      heardCallClaims.map((claim) => claimantIsGoodWhenClaimed(game, claim)),
      "good_player_heard_widow_call",
    ),
  );
}

function applyEvilTwinKnowledgeClaims(game: BOTCModel, doc: PuzzleDoc): void {
  const knowledgeClaims = doc.claims.filter(
    (claim): claim is typeof claim & { readonly knownEvilTwin: string } => claim.knownEvilTwin !== undefined,
  );
  for (const claim of knowledgeClaims) {
    const knownPlayerIsEvilTwin = doc.script.includes("Evil Twin")
      ? game.actualIs(claim.knownEvilTwin, "Evil Twin")
      : game.constantBool(false, `${slug(claim.name)}_knows_evil_twin_without_evil_twin_on_script`);
    game.addImplication(claimantIsGoodWhenClaimed(game, claim), knownPlayerIsEvilTwin);
  }
  if (!doc.script.includes("Evil Twin")) return;
  game.addImplication(
    game.roleInPlay("Evil Twin"),
    game.anyOf(
      knowledgeClaims.map((claim) =>
        game.allOf(
          [claimantIsGoodWhenClaimed(game, claim), game.actualIs(claim.knownEvilTwin, "Evil Twin")],
          `${slug(claim.name)}_knows_${slug(claim.knownEvilTwin)}_is_evil_twin`,
        ),
      ),
      "good_player_knows_evil_twin",
    ),
  );
}

function claimantIsGoodWhenClaimed(game: BOTCModel, claim: PuzzleDoc["claims"][number]): BoolLike {
  if (claim.timing === undefined) return game.isGood(claim.name);
  const timing = claim.timing as Timing;
  return game.hasAlignmentOverrideAt(claim.name, timing) ? game.isGoodAt(claim.name, timing) : game.isGood(claim.name);
}

function applyPuzzlemasterSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Puzzlemaster")) return;
  for (const claim of doc.claims) {
    if (claim.type !== "Puzzlemaster") continue;
    game.addPuzzlemasterDrunking({
      excludedPlayers: [claim.name],
      activeIf: game.actualIs(claim.name, "Puzzlemaster"),
      sourceName: `${slug(claim.name)}_puzzlemaster`,
    });
  }
}

function applySweetheartSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Sweetheart")) return;

  const activeByTiming = collectTimings(doc).flatMap((timing) => {
    const possiblePriorSweetheartDeaths = (doc.timeline ?? [])
      .filter((event) => isTimelineDeathEvent(event) && deathEventOrder(event) < phaseStartOrder(timing))
      .flatMap((event) => event.players.map((player) => roleAtBeforeEvent(game, doc, player, "Sweetheart", event)));
    if (possiblePriorSweetheartDeaths.length === 0) return [];
    return [
      {
        timing,
        activeIf: game.anyOf(possiblePriorSweetheartDeaths, `${timing}_sweetheart_dead_before_timing`),
      },
    ];
  });
  if (activeByTiming.length === 0) return;

  game.addPersistentDrunking(
    activeByTiming.map((entry) => entry.timing),
    { activeByTiming, sourceName: "sweetheart" },
  );
}

function applyVillageIdiotSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Village Idiot")) return;
  game.addVillageIdiotDrunking();
}

function roleAliveAt(game: BOTCModel, doc: PuzzleDoc, role: RoleRef, timing: Timing): BoolLike {
  const roleRef = roleName(role);
  const deadPlayers = deadPlayersBefore(doc, timing);
  const candidates = doc.players.filter((player) => !deadPlayers.has(player));
  return game.anyOf(
    candidates.map((player) => game.hasRoleAt(player, roleRef, timing)),
    `${slug(roleRef)}_alive_at_${timing}`,
  );
}

function healthyRoleAliveAt(game: BOTCModel, doc: PuzzleDoc, role: RoleRef, timing: Timing): BoolLike {
  const roleRef = roleName(role);
  const deadPlayers = deadPlayersBefore(doc, timing);
  const candidates = doc.players.filter((player) => !deadPlayers.has(player));
  return game.anyOf(
    candidates.map((player) =>
      game.allOf(
        [game.hasRoleAt(player, roleRef, timing), game.soberAndHealthy(player, timing)],
        `${timing}_${slug(player)}_healthy_living_${slug(roleRef)}`,
      ),
    ),
    `${slug(roleRef)}_healthy_and_alive_at_${timing}`,
  );
}

function isMinionBeforeEvent(
  game: BOTCModel,
  doc: PuzzleDoc,
  player: string,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  return characterTypeBeforeEvent(game, doc, player, CharacterType.Minion, event);
}

function characterTypeBeforeEvent(
  game: BOTCModel,
  doc: PuzzleDoc,
  player: string,
  characterType: CharacterType,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const roles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === characterType);
  return game.anyOf(
    roles.map((role) => roleAtBeforeEvent(game, doc, player, role, event)),
    `${event.timing}_${slug(player)}_${characterType}_before_death_event`,
  );
}

function roleAtBeforeEvent(
  game: BOTCModel,
  doc: PuzzleDoc,
  player: string,
  role: RoleRef,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const previousTiming = latestTimingBeforeEvent(doc, event);
  return previousTiming === undefined ? game.actualIs(player, role) : game.hasRoleAt(player, role, previousTiming);
}

function latestTimingBeforeEvent(
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): Timing | undefined {
  const eventTimingOrder = phaseStartOrder(event.timing as Timing);
  return collectTimings(doc)
    .filter((timing) => phaseStartOrder(timing) < eventTimingOrder)
    .at(-1);
}

function deadPlayersBefore(doc: PuzzleDoc, timing: Timing): ReadonlySet<string> {
  const timingOrder = phaseStartOrder(timing);
  const dead = new Set<string>();
  for (const event of doc.timeline ?? []) {
    if (deathEventOrder(event) >= timingOrder) continue;
    if (isTimelineDeathEvent(event)) {
      for (const player of event.players) dead.add(player);
    } else if (event.type === "resurrection") {
      for (const player of event.players) dead.delete(player);
    }
  }
  return dead;
}

function livingNeighborsAt(doc: PuzzleDoc, player: string, timing: Timing): [string, string] {
  const deadPlayers = deadPlayersBefore(doc, timing);
  return livingNeighborsWithDeadPlayers(doc, player, deadPlayers);
}

function livingNeighborsWithDeadPlayers(
  doc: PuzzleDoc,
  player: string,
  deadPlayers: ReadonlySet<string>,
): [string, string] {
  const playerIndex = doc.players.indexOf(player);
  if (playerIndex === -1) throw new Error(`Unknown player '${player}'.`);
  return [
    livingNeighborInDirection(doc.players, playerIndex, -1, deadPlayers),
    livingNeighborInDirection(doc.players, playerIndex, 1, deadPlayers),
  ];
}

function livingPlayersAt(doc: PuzzleDoc, timing: Timing): readonly string[] {
  const deadPlayers = deadPlayersBefore(doc, timing);
  return doc.players.filter((player) => !deadPlayers.has(player));
}

function playersInDocOrder(doc: PuzzleDoc, players: ReadonlySet<string>): readonly string[] {
  return doc.players.filter((player) => players.has(player));
}

function collectTimings(value: unknown): readonly Timing[] {
  const timings = new Set<Timing>();
  const visit = (entry: unknown): void => {
    if (typeof entry === "string") {
      if (/^(night|day)_\d+$/.test(entry)) timings.add(entry as Timing);
      return;
    }
    if (Array.isArray(entry)) {
      for (const item of entry) visit(item);
      return;
    }
    if (typeof entry !== "object" || entry === null) return;
    for (const item of Object.values(entry)) visit(item);
  };

  visit(value);
  return [...timings].sort((left, right) => phaseStartOrder(left) - phaseStartOrder(right));
}

function allNightTimings(doc: PuzzleDoc): readonly Timing[] {
  const maxRound = collectTimings(doc).reduce((max, timing) => {
    const match = /^(?:night|day)_(\d+)$/.exec(timing);
    return match === null ? max : Math.max(max, Number(match[1]));
  }, 1);
  return Array.from({ length: maxRound }, (_, index) => `night_${index + 1}` as Timing);
}

function livingNeighborInDirection(
  players: readonly string[],
  playerIndex: number,
  direction: -1 | 1,
  deadPlayers: ReadonlySet<string>,
): string {
  for (let offset = 1; offset < players.length; offset += 1) {
    const neighbor = players[(playerIndex + direction * offset + players.length) % players.length] as string;
    if (!deadPlayers.has(neighbor)) return neighbor;
  }
  throw new Error("Empath claims need at least one living neighbor in each direction.");
}

function deathEventOrder(event: NonNullable<PuzzleDoc["timeline"]>[number]): number {
  return phaseStartOrder(event.timing as Timing) + 0.5;
}

function phaseStartOrder(timing: Timing): number {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) throw new Error(`Invalid timing '${timing}'. Expected night_N or day_N.`);
  const phase = match[1] as "night" | "day";
  const number = match[2] as string;
  return Number(number) * 2 + (phase === "day" ? 1 : 0);
}

function slug(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_+|_+$/g, "");
}
