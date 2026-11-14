import { DeathAssignments, type AssignedDeath, type NightDeathSource } from "./nightDeaths";
import { PoChoices } from "./po";
import { slug, addMapValue } from "../model/keys";
import { TimelineFacts, deathEventOrder } from "./timeline";
import { applyBarberSwaps } from "./barber";
import { applyNightwatchmanActions } from "./nightwatchman";
import {
  timingOrder,
  followingNight,
  previousNight,
  previousDayForNight,
  healthTimingForDayAbility,
} from "../model/timing";
import { choose, constrainSelection } from "../model/actions";
import { applyClaims, type EmpathNeighborOption, type OracleDeadPlayerOption } from "../model/characters";
import { Alignment, CharacterType, roleAlignment, roleCharacterType, roleName, type RoleRef } from "../model/core";
import type { BoolLike, BOTCModel, Timing } from "../model/model";
import type { SatBackend } from "../model/sat";
import { buildPuzzleModel, type PuzzleSpec } from "../model/setup";
import { isTimelineDeathEvent, type PuzzleDoc, type TimelineEventDoc } from "../schema/puzzleDoc";
import { compile, type CompileCtx } from "../dsl/compile";
import { buildClaim, type ClaimWithTimelineContext } from "./claim";
import { resolveRoleRef } from "./roleRef";

interface BuildDoc extends PuzzleDoc {
  readonly facts: TimelineFacts;
}

export function buildFromDoc(input: PuzzleDoc, backend: SatBackend): BOTCModel {
  input = { ...input, claims: [...new Map(input.claims.map((claim) => [JSON.stringify(claim), claim])).values()] };
  const doc: BuildDoc = { ...input, facts: new TimelineFacts(input) };
  const spec: PuzzleSpec = {
    players: doc.players,
    characters: doc.script.map(resolveRoleRef),
    uniqueCharacters: doc.uniqueCharacters,
    setup: doc.setup === "none" || doc.setup === "atheist" ? false : "standard",
  };
  const game = buildPuzzleModel(spec, backend);
  const ctx = { players: doc.players, script: doc.script };
  game.withProvenance({ kind: "rule", id: "applyLleechHostChoice" }, () => applyLleechHostChoice(game, doc));
  game.withProvenance({ kind: "rule", id: "applyGlobalConstraints" }, () => applyGlobalConstraints(game, doc, ctx));
  if (doc.setup === "atheist")
    game.withProvenance({ kind: "rule", id: "applyAtheistSetup" }, () => applyAtheistSetup(game, doc));
  const characterActions = game.withProvenance({ kind: "rule", id: "nightlyCharacterChoices" }, () =>
    applyCharacterActions(game, doc),
  );
  game.withProvenance(
    {
      kind: "rule",
      id: "Barber.swaps",
      source: "https://wiki.bloodontheclocktower.com/index.php?title=Barber&oldid=1757",
    },
    () => applyBarberSwaps(game, doc, doc.facts),
  );
  game.withProvenance({ kind: "rule", id: "applyTimelineConstraints" }, () => applyTimelineConstraints(game, doc));
  if (doc.setup !== "atheist")
    game.withProvenance({ kind: "rule", id: "applyMinstrelSources" }, () => applyMinstrelSources(game, doc));
  if (doc.setup !== "atheist")
    game.withProvenance({ kind: "rule", id: "applySailorChoiceLegality" }, () => applySailorChoiceLegality(game, doc));
  game.withProvenance({ kind: "rule", id: "applyConditionalWakeSources" }, () =>
    applyConditionalWakeSources(game, doc),
  );
  game.withProvenance({ kind: "rule", id: "applyRiotTransformations" }, () => applyRiotTransformations(game, doc));
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
    game.withProvenance(
      {
        kind: "rule",
        id: "Shabaloth.targets",
        source: "https://wiki.bloodontheclocktower.com/index.php?title=Shabaloth&oldid=1790",
      },
      () => applyShabalothChoiceConstraints(game, doc, shabalothContext),
    );
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
  game.withProvenance({ kind: "fact", id: "puzzle.ongoing", source: "All puzzles describe ongoing games." }, () =>
    applyFinalDemonPathConstraint(game, doc),
  );
  const preNightDeathSnakeCharmerChecks = applyPreNightDeathSnakeCharmerChecks(game, doc);
  const timelineClaims = doc.claims.map((claim, index) =>
    removePreNightDeathSnakeCharmerChecks(claim, index, preNightDeathSnakeCharmerChecks),
  );
  const claims = timelineClaims.map((claim) => applyTimelineClaimContext(claim, doc, game, nightDeathTiming));
  const reportedClaims = claims.map((claim) => buildClaim(claim, ctx));
  const claimOptions = doc.setup === "atheist" ? { info: () => undefined } : {};
  if (doc.setup !== "atheist") {
    applyPuzzlemasterSources(game, doc);
    applySweetheartSources(game, doc);
  }
  for (const [index, claim] of reportedClaims.entries())
    game.withProvenance({ kind: "assumption", id: `claims[${index}]`, source: doc.claims[index]?.source }, () =>
      applyClaims(game, [claim], claimOptions),
    );
  game.withProvenance({ kind: "rule", id: "applyLleechHostPoisoning" }, () => applyLleechHostPoisoning(game, doc));
  if (doc.script.includes("Assassin")) game.enforceAbilityUseLimit("Assassin", 1);
  if (doc.setup !== "atheist") {
    applyPhilosopherDrunking(game, doc);
    applyNightwatchmanActions(game, doc, doc.facts);
    applyChangedRoleClaimExplanations(game, doc, characterActions);
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

function applyMinstrelSources(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Minstrel")) return;
  for (const event of doc.timeline ?? []) {
    if (event.type !== "execution") continue;
    const timing = event.timing as Timing;
    const match = /^day_(\d+)$/.exec(timing);
    if (match === null) continue;
    const round = Number(match[1]);
    const executedMinion = game.anyOf(
      event.players.map((player) => characterTypeBeforeEvent(game, doc, player, CharacterType.Minion, event)),
    );
    for (const minstrel of doc.facts.livingAt(event.timing as Timing)) {
      const active = game.allOf([
        executedMinion,
        roleAtBeforeEvent(game, doc, minstrel, "Minstrel", event),
        game.soberAndHealthy(minstrel, healthTimingForDayAbility(timing)),
      ]);
      const affectedTimings: Timing[] = [timing, `night_${round + 1}` as Timing, `day_${round + 1}` as Timing];
      for (const player of doc.players) {
        if (player !== minstrel) game.addTimedDrunkSource(player, affectedTimings, active);
      }
    }
  }
}

function applySailorChoiceLegality(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Sailor")) return;
  for (const claim of doc.claims) {
    if (claim.type !== "Sailor") continue;
    for (const choice of claim.choices ?? []) {
      const timing = choice.timing as Timing | undefined;
      const legal =
        timing !== undefined &&
        /^night_\d+$/.test(timing) &&
        doc.facts.livingAt(timing).includes(claim.name) &&
        doc.facts.livingAt(timing).includes(choice.player);
      if (timing === undefined) continue;
      game.addImplication(game.hasAbilityAt(claim.name, "Sailor", timing), game.constantBool(legal));
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

function applyGodfatherChoices(game: BOTCModel, doc: BuildDoc): GodfatherContext {
  if (!doc.script.includes("Godfather")) return { choices: [] };
  const choices: GodfatherChoice[] = [];
  for (const timing of doc.facts.nights) {
    const previousDay = previousDayForNight(timing);
    if (previousDay === undefined) continue;
    const outsiderDied = outsiderDiedDuring(game, doc, previousDay);
    const publicDeaths = doc.facts.nightDeaths(timing);
    const living = doc.facts.livingAt(timing);
    for (const actor of living) {
      const choiceActive = game.allOf([game.hasAbilityAt(actor, "Godfather", timing), outsiderDied]);
      const active = game.allOf([choiceActive, game.soberAndHealthy(actor, timing)]);
      const declaredTarget = doc.claims
        .flatMap((claim) => (claim.type === "Godfather" && claim.name === actor ? (claim.choices ?? []) : []))
        .find((choice) => choice.timing === timing)?.player;
      const targets = new Map<string, BoolLike>();
      const selection = choose(
        game,
        { rule: "Godfather:targets", actor, timing, active: choiceActive, count: 1 },
        living,
      );
      for (const [target, selected] of selection.choices) {
        const effectiveTarget = game.allOf([active, selected]);
        targets.set(target, effectiveTarget);
        if (declaredTarget !== undefined) {
          if (target === declaredTarget) game.addImplication(choiceActive, selected);
          else game.addFalse(selected);
        }
        game.registerAbilityTarget(actor, "Godfather", target, timing, selected, nightActionOrder("Godfather"));
        if (!publicDeaths.has(target)) {
          game.addImplication(
            effectiveTarget,
            game.anyOf([
              deathProtectionAt(game, doc, target, timing),
              innkeeperProtectionAt(game, doc, target, timing),
            ]),
          );
        }
      }
      if (declaredTarget !== undefined && !living.includes(declaredTarget)) game.addFalse(choiceActive);
      choices.push({ actor, timing, active, targets });
    }
  }
  return { choices };
}

function outsiderDiedDuring(game: BOTCModel, doc: BuildDoc, timing: Timing): BoolLike {
  return game.anyOf(
    (doc.timeline ?? []).flatMap((event) =>
      event.timing === timing && isTimelineDeathEvent(event)
        ? event.players.map((player) => game.hasCharacterType(player, CharacterType.Outsider))
        : [],
    ),
  );
}

function applyPukkaPoisonChoices(game: BOTCModel, doc: BuildDoc): PukkaContext {
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
  for (const timing of doc.facts.nights) {
    const match = /^night_(\d+)$/.exec(timing);
    if (match === null) continue;
    const unblocked = game.newBool();
    const livingPukka = game.anyOf(
      doc.facts.livingAt(timing).map((player) => game.hasAbilityAt(player, "Pukka", timing)),
    );
    const choice = game.addRolePoisonChoice("Pukka", timing, [timing], game.allOf([livingPukka, unblocked]));
    const blocked = demonKillBlockedAt(game, doc, timing, (player, healthTiming) => {
      if (healthTiming !== timing) return game.soberAndHealthy(player, healthTiming);
      const currentPukkaPoison = choice.activeTargetsAtChoiceTiming.get(player);
      return game.soberAndHealthyBeforeOwnPoisoning(
        player,
        timing,
        currentPukkaPoison === undefined ? [] : [currentPukkaPoison],
      );
    });
    const notBlocked = game.not(blocked);
    game.equate(unblocked, notBlocked);
    for (const actor of doc.players)
      for (const [target, targeted] of choice.targets) {
        game.registerAbilityTarget(
          actor,
          "Pukka",
          target,
          timing,
          game.allOf([choice.choiceActive, targeted, game.hasAbilityAt(actor, "Pukka", timing)]),
          nightActionOrder("Pukka"),
        );
      }
    choicesByTiming.set(timing, choice);
    resolvesByTiming.set(timing, game.allOf([livingPukka, choice.healthyRoleInPlay]));
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
    const livingAtNight = new Set(doc.facts.livingAt(timing));
    const livingAfterNight = new Set(doc.facts.livingAt(dayTiming));
    const oldPoison = new Map<string, BoolLike>();

    for (const player of livingAtNight) {
      const carriedTargets = poisonSeeds.flatMap((seed): BoolLike[] => {
        const seededTarget = seed.targets.get(player);
        if (seededTarget === undefined) return [];
        const survivedResolutions = nightTimings
          .slice(seed.originIndex + 1, timingIndex)
          .map((interveningTiming) => game.not(resolvesByTiming.get(interveningTiming) as BoolLike));
        return [game.allOf([seededTarget, ...survivedResolutions])];
      });
      if (carriedTargets.length > 0) {
        oldPoison.set(
          player,
          carriedTargets.length === 1 ? (carriedTargets[0] as BoolLike) : game.anyOf(carriedTargets),
        );
      }
    }

    if (oldPoison.size > 0) {
      game.addPoisonState(timing, oldPoison);
      poisonedBeforeResolutionByTiming.set(timing, oldPoison);
    }

    const newPoison = new Map<string, BoolLike>();
    const poisonAfterResolution = new Map<string, BoolLike>();
    for (const player of livingAfterNight) {
      const selected = choice.targets.get(player);
      if (selected === undefined) continue;
      const oldTargetResolves = game.allOf([resolves, oldPoison.get(player) ?? game.constantBool(false)]);
      const newlyPoisoned = game.allOf([choice.active, selected, game.not(oldTargetResolves)]);
      newPoison.set(player, newlyPoisoned);
      const oldPoisonPersists = game.allOf([oldPoison.get(player) ?? game.constantBool(false), game.not(resolves)]);
      poisonAfterResolution.set(player, game.anyOf([newlyPoisoned, oldPoisonPersists]));
    }
    game.addPoisonState(dayTiming, poisonAfterResolution);
    poisonSeeds.push({ originIndex: timingIndex, targets: newPoison });
  }

  for (const [timing, poisonedPlayers] of poisonedBeforeResolutionByTiming) {
    const resolves = resolvesByTiming.get(timing);
    if (resolves === undefined) continue;
    const publicDeaths = doc.facts.nightDeaths(timing);
    const livingPlayers = new Set(doc.facts.livingAt(timing));
    for (const [player, poisoned] of poisonedPlayers) {
      if (!livingPlayers.has(player) || publicDeaths.has(player)) continue;
      const shouldDie = game.allOf([resolves, poisoned]);
      const soldierProtected = doc.script.includes("Soldier")
        ? game.allOf([game.hasAbilityAt(player, "Soldier", timing), game.soberAndHealthy(player, timing)])
        : game.constantBool(false);
      game.addImplication(
        shouldDie,
        game.anyOf([
          deathProtectionAt(game, doc, player, timing),
          innkeeperProtectionAt(game, doc, player, timing),
          soldierProtected,
        ]),
      );
    }
  }
  return { poisonedBeforeResolutionByTiming, resolvesByTiming };
}

function registerDevilsAdvocateTargets(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Devil's Advocate")) return;
  const choicesByActorTiming = new Map<string, Map<string, BoolLike>>();
  for (const timing of doc.facts.nights) {
    const living = doc.facts.livingAt(timing);
    for (const actor of living) {
      const active = game.hasAbilityAt(actor, "Devil's Advocate", timing);
      const declaredTarget = doc.claims
        .flatMap((claim) => (claim.type === "Devil's Advocate" && claim.name === actor ? (claim.choices ?? []) : []))
        .find((choice) => choice.timing === timing)?.player;
      const targets = new Map<string, BoolLike>();
      for (const target of living) {
        const selected = game.newBool();
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
  for (const timing of doc.facts.nights) {
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
          game.addImplication(currentTarget, game.not(priorTarget));
      }
    }
  }
}

function registerDeclaredAbilityTargets(game: BOTCModel, doc: BuildDoc): void {
  const register = (actor: string, role: string, target: string, timing: string | undefined): void => {
    if (!/^(night)_\d+$/.test(timing ?? "") || !doc.players.includes(target)) return;
    const resolvedTiming = timing as Timing;
    if (!doc.facts.livingAt(resolvedTiming).includes(actor)) return;
    game.registerAbilityTarget(
      actor,
      role,
      target,
      resolvedTiming,
      game.hasAbilityAt(actor, role, resolvedTiming),
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

function registerShabalothChoices(game: BOTCModel, doc: BuildDoc): ShabalothContext {
  if (!doc.script.includes("Shabaloth")) return { choices: [] };
  const choices: ShabalothChoice[] = [];
  for (const timing of doc.facts.nights) {
    for (const actor of doc.facts.livingAt(timing)) {
      const targets = new Map<string, BoolLike>();
      for (const target of doc.players) {
        const selected = game.newBool();
        targets.set(target, selected);
        game.addImplication(selected, game.hasAbilityAt(actor, "Shabaloth", timing));
        game.registerAbilityTarget(actor, "Shabaloth", target, timing, selected, nightActionOrder("Shabaloth"));
      }
      choices.push({ actor, timing, targets });
    }
  }
  return { choices };
}

function applyShabalothChoiceConstraints(game: BOTCModel, doc: BuildDoc, context: ShabalothContext): void {
  for (const choice of context.choices) {
    const wakes = game.constantBool(choice.timing !== "night_1");
    const shouldChoose = game.allOf([
      game.hasAbilityAt(choice.actor, "Shabaloth", choice.timing),
      wakes,
      game.not(demonKillBlockedAt(game, doc, choice.timing)),
    ]);
    game.registerChoiceAction({
      rule: "Shabaloth:targets",
      actor: choice.actor,
      timing: choice.timing,
      count: 2,
      active: shouldChoose,
      choices: choice.targets,
    });
    constrainSelection(game, [...choice.targets.values()], 2, shouldChoose);

    const effective = game.allOf([shouldChoose, game.soberAndHealthy(choice.actor, choice.timing)]);
    const publicDeaths = doc.facts.nightDeaths(choice.timing);
    const completeReport = doc.facts.reportedPlayers("nightDeath", choice.timing) !== undefined;
    for (const [target, selected] of choice.targets) {
      if (!completeReport || publicDeaths.has(target) || !doc.facts.livingAt(choice.timing).includes(target)) continue;
      game.addImplication(
        game.allOf([effective, selected]),
        game.anyOf([
          deathProtectionAt(game, doc, target, choice.timing),
          innkeeperProtectionAt(game, doc, target, choice.timing),
          game.pitHagCreatedDemon(choice.timing),
        ]),
      );
    }
  }
}

function shabalothTargetedAt(game: BOTCModel, context: ShabalothContext, player: string, timing: Timing): BoolLike {
  return game.anyOf(
    context.choices.flatMap((choice) =>
      choice.timing === timing && choice.targets.has(player) ? [choice.targets.get(player) as BoolLike] : [],
    ),
  );
}

function emptyGoonContext(): GoonContext {
  return { drunkSourcesByActorTiming: new Map(), targetings: [] };
}

function applyGoonInteractions(game: BOTCModel, doc: BuildDoc): GoonContext {
  if (!doc.script.includes("Goon")) return emptyGoonContext();
  const actions = [...game.registeredAbilityTargets()].sort(
    (left, right) => timingOrder(left.timing) - timingOrder(right.timing) || left.order - right.order,
  );
  const firstGoonTargets: Array<(typeof actions)[number] & { readonly triggers: BoolLike }> = [];
  const targetings: Array<{ readonly timing: Timing; readonly order: number; readonly active: BoolLike }> = [];
  const drunkSourcesByActorTiming = new Map<string, BoolLike[]>();
  for (const timing of doc.facts.nights) {
    const earlier: BoolLike[] = [];
    for (const action of actions.filter((candidate) => candidate.timing === timing)) {
      if (!doc.facts.livingAt(timing).includes(action.target)) continue;
      const targetsGoon = game.allOf([action.activeIf, game.hasAbilityAt(action.target, "Goon", timing)]);
      const triggers = game.allOf([targetsGoon, ...earlier.map((prior) => game.not(prior))]);
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

  for (const timing of doc.facts.nights) {
    const priorTiming = previousNight(timing);
    for (const player of doc.players) {
      const priorGood = priorTiming === undefined ? game.isGood(player) : game.isGoodAt(player, priorTiming);
      const playerTriggers = firstGoonTargets.filter((target) => target.timing === timing && target.target === player);
      const turnsGood = game.anyOf(
        playerTriggers.map((target) => {
          const actorWasGood =
            priorTiming === undefined ? game.isGood(target.actor) : game.isGoodAt(target.actor, priorTiming);
          return game.allOf([target.triggers, actorWasGood]);
        }),
      );
      const turnsEvil = game.anyOf(
        playerTriggers.map((target) => {
          const actorWasEvil = game.not(
            priorTiming === undefined ? game.isGood(target.actor) : game.isGoodAt(target.actor, priorTiming),
          );
          return game.allOf([target.triggers, actorWasEvil]);
        }),
      );
      const goodAtTiming = game.anyOf([turnsGood, game.allOf([priorGood, game.not(turnsEvil)])]);
      game.setGoodAt(player, timing, goodAtTiming);
      const match = /^night_(\d+)$/.exec(timing);
      if (match !== null) game.setGoodAt(player, `day_${match[1]}` as Timing, goodAtTiming);
    }
  }
  return { drunkSourcesByActorTiming, targetings };
}

function goonWasTargetedBefore(game: BOTCModel, context: GoonContext, timing: Timing, order: number): BoolLike {
  return game.anyOf(
    context.targetings
      .filter((targeting) => targeting.timing === timing && targeting.order < order)
      .map((targeting) => targeting.active),
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

function applyConditionalWakeSources(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Godfather")) return;
  for (const timing of doc.facts.timings) {
    const previousDay = previousDayForNight(timing);
    if (previousDay === undefined) continue;
    const outsiderDied = outsiderDiedDuring(game, doc, previousDay);
    for (const player of doc.players) {
      game.registerConditionalWake(
        player,
        "Godfather",
        timing,
        game.allOf([game.hasAbilityAt(player, "Godfather", timing), outsiderDied]),
      );
    }
  }
}

function applyGlobalConstraints(game: BOTCModel, doc: BuildDoc, ctx: Omit<CompileCtx, "nameRoot">): void {
  for (const [index, constraint] of (doc.constraints ?? []).entries()) {
    const expression = constraint.expression.trim();
    if (expression === "") continue;
    const origin = {
      kind: constraint.kind ?? ("fact" as const),
      id: `constraints[${index}]`,
      source: constraint.source,
    };
    game.withProvenance(origin, () =>
      game.addTruth(compile(expression, game, { ...ctx, nameRoot: `global_constraint_${index + 1}`, origin })),
    );
  }
}

interface CharacterActions {
  readonly madness: ReadonlyMap<string, readonly BoolLike[]>;
}

function applyCharacterActions(game: BOTCModel, doc: BuildDoc): CharacterActions {
  const madness = new Map<string, BoolLike[]>();
  for (const timing of doc.facts.nights) {
    for (const role of ["Pit-Hag", "Cerenovus"]) {
      if (!doc.script.includes(role) || (role === "Pit-Hag" && timing === "night_1")) continue;
      for (const actor of doc.facts.livingAt(timing)) {
        const active = game.characterBefore(actor, role, timing);
        const target = choose(game, { rule: `${role}:player`, actor, timing, count: 1, active }, doc.players);
        const roles = doc.script.filter(
          (candidate) => role === "Pit-Hag" || roleAlignment(resolveRoleRef(candidate)) === Alignment.Good,
        );
        const character = choose(game, { rule: `${role}:character`, actor, timing, count: 1, active }, roles);
        const healthy = game.soberAndHealthyBeforeCharacterChange(actor, timing);
        for (const [player, selectedPlayer] of target.choices)
          for (const [chosenRole, selectedRole] of character.choices) {
            const selected = game.allOf([healthy, selectedPlayer, selectedRole]);
            if (role === "Cerenovus") {
              const dayTiming = timing.replace("night_", "day_") as Timing;
              for (const when of [timing, dayTiming]) {
                const key = JSON.stringify([player, chosenRole, when]);
                madness.set(key, [...(madness.get(key) ?? []), selected]);
              }
            } else {
              const inPlay = game.anyOf(
                doc.players.map((candidate) => game.characterBefore(candidate, chosenRole, timing)),
              );
              const changes = game.allOf([selected, inPlay.not()]);
              game.trace.replace({ player, character: chosenRole, timing, active: changes, rule: "Pit-Hag" });
              if (roleCharacterType(resolveRoleRef(chosenRole)) === CharacterType.Demon)
                game.registerPitHagDemonCreation(timing, changes);
            }
          }
      }
    }
  }
  return { madness };
}

function applyChangedRoleClaimExplanations(game: BOTCModel, doc: BuildDoc, actions: CharacterActions): void {
  for (const claim of doc.claims) {
    const claimTiming = claim.roleTiming as Timing | undefined;
    if (claimTiming === undefined || timingOrder(claimTiming) <= timingOrder("night_1")) continue;
    const claimedRole = claimRoleRef(claim);
    if (claimedRole === undefined) continue;
    const claimedRoleName = roleName(claimedRole);
    const claimedRoleAtTiming = game.hasAbilityAt(claim.name, claimedRole, claimTiming);
    const claimantEvil = game.hasAlignmentOverrideAt(claim.name, claimTiming)
      ? game.isEvilAt(claim.name, claimTiming)
      : game.isEvil(claim.name);
    const claimantGood = game.hasAlignmentOverrideAt(claim.name, claimTiming)
      ? game.isGoodAt(claim.name, claimTiming)
      : game.isGood(claim.name);
    const claimedAlignmentMatches =
      claim.alignment === undefined ? undefined : claim.alignment === "good" ? claimantGood : claimantEvil;
    const truthfulClaim =
      claimedAlignmentMatches === undefined
        ? claimedRoleAtTiming
        : game.allOf([claimedRoleAtTiming, claimedAlignmentMatches]);
    const explanations: BoolLike[] = [truthfulClaim, claimantEvil];

    explanations.push(...(actions.madness.get(JSON.stringify([claim.name, claimedRoleName, claimTiming])) ?? []));
    for (const hiddenRole of ["Drunk", "Marionette"]) {
      if (doc.script.includes(hiddenRole) && roleCharacterType(claimedRole) === CharacterType.Townsfolk)
        explanations.push(game.characterAt(claim.name, hiddenRole, claimTiming));
    }
    const repeatsStartingBluff = doc.claims.some(
      (earlier) =>
        earlier.name === claim.name &&
        earlier.type === claim.type &&
        earlier.roleTiming === undefined &&
        earlier.possibleActualRoles?.includes("Mutant"),
    );
    if (repeatsStartingBluff && doc.facts.livingAt(claimTiming).includes(claim.name))
      explanations.push(
        game.allOf([game.actualIs(claim.name, "Mutant"), game.characterAt(claim.name, "Mutant", claimTiming)]),
      );

    game.addTruth(game.anyOf(explanations));
  }
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

function applyPreNightDeathSnakeCharmerChecks(game: BOTCModel, doc: BuildDoc): ReadonlySet<string> {
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
      );
      game.addInfoClaim({
        player: claim.name,
        role: "Snake Charmer",
        timing,
        learned: check.demon ? checkedIsDemonBeforeDeath : game.not(checkedIsDemonBeforeDeath),
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

function applyPhilosopherDrunking(game: BOTCModel, doc: BuildDoc): void {
  const philosopherClaims = doc.claims.filter(
    (claim): claim is Extract<PuzzleDoc["claims"][number], { readonly type: "Philosopher" }> =>
      claim.type === "Philosopher" && claim.role !== undefined && claim.timing !== undefined,
  );
  const timings = doc.facts.timings;
  for (const claim of philosopherClaims) {
    const choiceTiming = claim.timing as Timing;
    const affectedTimings = timings.filter((timing) => timingOrder(timing) >= timingOrder(choiceTiming));
    if (affectedTimings.length === 0) continue;
    const choiceActive = game.allOf([
      game.actualIs(claim.name, "Philosopher"),
      game.soberAndHealthy(claim.name, choiceTiming),
    ]);

    for (const timing of affectedTimings) {
      const philosopherAlive = game.anyOf(
        doc.players
          .filter((player) => !doc.facts.deadBefore(timing).has(player))
          .map((player) => game.actualIs(player, "Philosopher")),
      );
      game.addRoleDrunking(resolveRoleRef(claim.role as string), [timing], {
        activeIf: game.allOf([choiceActive, philosopherAlive]),
        excludedPlayers: [claim.name],
      });
    }
  }
}

function applyAtheistSetup(game: BOTCModel, doc: BuildDoc): void {
  const evilRoles = doc.script.map(resolveRoleRef).filter((role) => roleAlignment(role) === Alignment.Evil);
  for (const player of doc.players) {
    for (const role of evilRoles) game.fixNotActual(player, role);
  }
  if (doc.script.includes("Atheist")) game.addTruth(game.roleInPlay("Atheist"));
}

function applyTimelineConstraints(game: BOTCModel, doc: BuildDoc): void {
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
      const activeHealthyGolem = game.allOf([
        game.hasAbilityAt(event.caller, "Golem", timing),
        game.soberAndHealthy(event.caller, healthTimingForDayAbility(timing)),
      ]);
      game.addTruth(activeHealthyGolem);
    }
    if (event.type === "tinkerDeath") {
      for (const player of event.players) {
        game.addTruth(
          game.allOf([
            game.hasAbilityAt(player, "Tinker", event.timing as Timing),
            game.soberAndHealthy(player, healthTimingForDayAbility(event.timing as Timing)),
          ]),
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
        game.addFalse(roleAtBeforeEvent(game, doc, player, demonRole, event));
      }
    }
  }
}

function applyResurrectionConstraints(game: BOTCModel, doc: BuildDoc, nightDeathTiming: NightDeathTimingContext): void {
  const professorActions = declaredProfessorActions(game, doc);
  for (const event of doc.timeline ?? []) {
    if (event.type !== "resurrection") continue;
    const timing = event.timing as Timing;
    const priorNight = previousNight(timing);
    for (const player of event.players) {
      const wasDead = doc.facts.deadBefore(timing).has(player);
      if (!wasDead) {
        game.addFalse(game.constantBool(true));
        continue;
      }

      const professorSources = professorActions
        .filter((action) => action.timing === timing && action.target === player)
        .map((action) => {
          const source = game.allOf([
            action.active,
            game.soberAndHealthy(action.claimant, timing),
            game.hasCharacterType(player, CharacterType.Townsfolk),
          ]);
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
        priorNight !== undefined && doc.facts.deadBefore(priorNight).has(player)
          ? game.constantBool(true)
          : game.constantBool(false);
      const shabalothSource =
        doc.script.includes("Shabaloth") && priorNight !== undefined
          ? game.allOf([
              healthyRoleAliveAt(game, doc, "Shabaloth", timing),
              game.anyOf([...(priorDemonKill === undefined ? [] : [priorDemonKill]), wasDeadWhenChosen]),
            ])
          : game.constantBool(false);

      game.addTruth(game.anyOf([...professorSources, shabalothSource]));
    }
  }
  game.addEnforcedAtMostN(
    professorActions.map((action) => action.active),
    1,
    game.constantBool(true),
  );
}

interface DeclaredProfessorAction {
  readonly claimant: string;
  readonly target: string;
  readonly timing: Timing;
  readonly active: BoolLike;
}

function declaredProfessorActions(game: BOTCModel, doc: BuildDoc): DeclaredProfessorAction[] {
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Professor" || claim.target === undefined || claim.target === "") return [];
    const timing = (claim.timing ?? "night_2") as Timing;
    const active = game.hasAbilityAt(claim.name, "Professor", timing);
    const validTiming = /^night_([2-9]|[1-9]\d+)$/.test(timing);
    const claimantAlive = doc.facts.livingAt(timing).includes(claim.name);
    const targetDead = doc.facts.deadBefore(timing).has(claim.target);
    game.addImplication(active, game.constantBool(validTiming && claimantAlive && targetDead));
    game.registerAbilityUse(claim.name, "Professor", timing, active);
    return [{ claimant: claim.name, target: claim.target, timing, active }];
  });
}

function applyRiotTransformations(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Riot")) return;
  const minionRoles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === CharacterType.Minion);
  if (minionRoles.length === 0) return;

  const affectedTimings = doc.facts.timings.filter((timing) => timingOrder(timing) >= timingOrder("day_3"));
  for (const timing of affectedTimings) {
    for (const player of doc.players) {
      const startsAsMinion = game.anyOf(minionRoles.map((role) => game.actualIs(player, role)));
      game.replaceCharacter(player, "Riot", timing, startsAsMinion);
      for (const minionRole of minionRoles) {
        game.removeAbility(player, minionRole, timing, game.actualIs(player, minionRole));
      }
    }
  }
}

function doomsayerSameRegisteredAlignment(game: BOTCModel, caller: string, deadPlayer: string): BoolLike {
  return game.anyOf([
    game.allOf([game.registersAsGood(caller), game.registersAsGood(deadPlayer)]),
    game.allOf([game.registersAsEvil(caller), game.registersAsEvil(deadPlayer)]),
  ]);
}

function deathProtectionAt(game: BOTCModel, doc: BuildDoc, player: string, timing: Timing): BoolLike {
  return game.anyOf([
    teaLadyProtectsAt(game, doc, player, timing),
    foolProtectsAt(game, doc, player, timing),
    sailorProtectsAt(game, doc, player, timing),
    ...(doc.script.includes("Innkeeper") ? [innkeeperProtectionAt(game, doc, player, timing)] : []),
  ]);
}

function executionSurvivalAt(
  game: BOTCModel,
  doc: BuildDoc,
  player: string,
  timing: Timing,
  foolProtection: BoolLike = foolProtectsAt(game, doc, player, timing),
): BoolLike {
  return game.anyOf([
    teaLadyProtectsAt(game, doc, player, timing),
    foolProtection,
    sailorProtectsAt(game, doc, player, timing),
    pacifistProtectsExecutionAt(game, doc, player, timing),
    devilsAdvocateProtectsExecutionAt(game, doc, player, timing),
  ]);
}

function registerFoolExecutionProtection(game: BOTCModel, doc: BuildDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Fool")) return game.constantBool(false);
  const used = game.newBool();
  game.addImplication(used, foolProtectsAt(game, doc, player, timing));
  game.addImplication(
    used,
    game.not(
      game.anyOf([
        teaLadyProtectsAt(game, doc, player, timing),
        sailorProtectsAt(game, doc, player, timing),
        devilsAdvocateProtectsExecutionAt(game, doc, player, timing),
      ]),
    ),
  );
  game.registerAbilityUse(player, "Fool", timing, used);
  return used;
}

function sailorProtectsAt(game: BOTCModel, doc: BuildDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Sailor")) return game.constantBool(false);
  return game.allOf([
    game.hasAbilityAt(player, "Sailor", timing),
    game.soberAndHealthy(player, healthTimingForDayAbility(timing)),
  ]);
}

function foolProtectsAt(game: BOTCModel, doc: BuildDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Fool")) return game.constantBool(false);
  return game.allOf([
    game.hasAbilityAt(player, "Fool", timing),
    game.soberAndHealthy(player, healthTimingForDayAbility(timing)),
    game.not(game.abilityUsedBefore(player, "Fool", timing)),
  ]);
}

function pacifistProtectsExecutionAt(game: BOTCModel, doc: BuildDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Pacifist")) return game.constantBool(false);
  const healthTiming = healthTimingForDayAbility(timing);
  return game.anyOf(
    doc.facts
      .livingAt(timing)
      .map((candidate) =>
        game.allOf([
          game.hasAbilityAt(candidate, "Pacifist", timing),
          game.soberAndHealthy(candidate, healthTiming),
          game.isGoodAt(player, timing),
        ]),
      ),
  );
}

function teaLadyProtectsAt(game: BOTCModel, doc: BuildDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Tea Lady")) {
    return game.constantBool(false);
  }
  const healthTiming = healthTimingForDayAbility(timing);
  const protectors = doc.facts.livingAt(timing).flatMap((candidate): BoolLike[] => {
    if (candidate === player) return [];
    const [left, right] = doc.facts.neighbors(candidate, doc.facts.deadBefore(timing));
    if (left !== player && right !== player) return [];
    const goodNeighbors =
      left === right
        ? game.isGoodAt(left, timing)
        : game.allOf([game.isGoodAt(left, timing), game.isGoodAt(right, timing)]);
    return [
      game.allOf([
        game.hasAbilityAt(candidate, "Tea Lady", timing),
        game.soberAndHealthy(candidate, healthTiming),
        goodNeighbors,
      ]),
    ];
  });
  return game.anyOf(protectors);
}

function devilsAdvocateProtectsExecutionAt(game: BOTCModel, doc: BuildDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Devil's Advocate")) {
    return game.constantBool(false);
  }
  const abilityTiming = healthTimingForDayAbility(timing);
  const protectors = doc.facts
    .livingAt(abilityTiming)
    .map((candidate) =>
      game.allOf([
        game.hasAbilityAt(candidate, "Devil's Advocate", abilityTiming),
        game.soberAndHealthy(candidate, abilityTiming),
        game.abilityTargetedAt(candidate, "Devil's Advocate", player, abilityTiming),
      ]),
    );
  return game.anyOf(protectors);
}

function witchCurseSourceAvailable(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const timing = event.timing as Timing;
  if (event.sourceActedBeforeDeath === true) {
    return game.constantBool(true);
  }
  const abilityTiming = healthTimingForDayAbility(timing);
  return game.anyOf(
    doc.facts
      .livingAt(event.timing as Timing)
      .map((player) =>
        game.allOf([
          game.hasAbilityAt(player, "Witch", abilityTiming),
          roleAtBeforeEvent(game, doc, player, "Witch", event),
          game.soberAndHealthy(player, abilityTiming),
        ]),
      ),
  );
}

function livingScarletWomanCanCatchDemonDeath(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  if (!doc.script.includes("Scarlet Woman")) return game.constantBool(false);
  if (doc.facts.livingAt(event.timing as Timing).length < 5) return game.constantBool(false);
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  return game.anyOf(candidates.map((player) => roleAtBeforeEvent(game, doc, player, "Scarlet Woman", event)));
}

function livingPlayersAfterDeathEvent(
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): readonly string[] {
  const deadPlayers = doc.facts.deadBefore(event.timing as Timing);
  const dyingPlayers = new Set(event.players);
  return doc.players.filter((player) => !deadPlayers.has(player) && !dyingPlayers.has(player));
}

function applyFinalDemonPathConstraint(game: BOTCModel, doc: BuildDoc): void {
  if (doc.setup === "atheist" || (doc.timeline?.length ?? 0) === 0) return;

  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === CharacterType.Demon);
  if (demonRoles.length === 0) return;

  const finalLivingPlayers = doc.facts.finalLiving;
  const finalDeadPlayers = doc.players.filter((player) => !finalLivingPlayers.includes(player));
  const finalTiming = doc.facts.timings.at(-1);
  const finalLivingStartingDemon = finalLivingPlayers.flatMap((player) =>
    demonRoles.map((role) =>
      finalTiming === undefined ? game.actualIs(player, role) : game.hasAbilityAt(player, role, finalTiming),
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
        game.allOf([
          roleAtBeforeEvent(game, doc, player, "Zombuul", death),
          game.soberAndHealthy(player, healthTimingForDayAbility(death.timing as Timing)),
        ]),
      ];
    });
    possibleSuccessions.push(game.anyOf(apparentlyDeadOnce));
  }

  if (doc.script.includes("Scarlet Woman")) {
    const deadDemons = finalDeadPlayers.flatMap((player) => demonRoles.map((role) => game.actualIs(player, role)));
    possibleSuccessions.push(
      game.allOf([
        game.anyOf(deadDemons),
        game.anyOf(finalLivingPlayers.map((player) => game.actualIs(player, "Scarlet Woman"))),
      ]),
    );
  }
  if (doc.script.includes("Fang Gu")) {
    possibleSuccessions.push(
      game.allOf([
        game.anyOf(finalDeadPlayers.map((player) => game.actualIs(player, "Fang Gu"))),
        game.anyOf(finalLivingPlayers.map((player) => game.hasCharacterType(player, CharacterType.Outsider))),
      ]),
    );
  }
  if (doc.script.includes("Mastermind")) {
    possibleSuccessions.push(...mastermindExtraDayPaths(game, doc, demonRoles, finalTiming));
  }

  game.addTruth(game.anyOf([...finalLivingStartingDemon, ...possibleSuccessions]));
}

function zombuulDiesForRealAt(
  game: BOTCModel,
  doc: BuildDoc,
  player: string,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const diedBefore = (doc.timeline ?? []).some(
    (candidate) =>
      isTimelineDeathEvent(candidate) &&
      candidate.players.includes(player) &&
      deathEventOrder(candidate) < deathEventOrder(event),
  );
  if (diedBefore) return game.constantBool(true);
  return game.not(game.soberAndHealthy(player, healthTimingForDayAbility(event.timing as Timing)));
}

function mastermindExtraDayPaths(
  game: BOTCModel,
  doc: BuildDoc,
  demonRoles: readonly RoleRef[],
  finalTiming: Timing | undefined,
): readonly BoolLike[] {
  if (finalTiming === undefined) return [];
  const finalOrder = timingOrder(finalTiming);
  return (doc.timeline ?? []).flatMap((event): BoolLike[] => {
    if (event.type !== "execution") return [];
    const timing = event.timing as Timing;
    const match = /^day_(\d+)$/.exec(timing);
    if (match === null) return [];
    const extraDay = `day_${Number(match[1]) + 1}` as Timing;
    if (finalOrder < timingOrder(timing) || finalOrder > timingOrder(extraDay)) return [];
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
          return game.allOf([actualDemon, zombuulDiesForRealAt(game, doc, player, event)]);
        }),
      ),
    );
    const noScarletWomanCatches = game.not(livingScarletWomanCanCatchDemonDeath(game, doc, event));
    const activeMastermind = game.anyOf(
      livingPlayersAfterDeathEvent(doc, event).map((player) =>
        game.allOf([
          roleAtBeforeEvent(game, doc, player, "Mastermind", event),
          game.soberAndHealthy(player, healthTimingForDayAbility(timing)),
        ]),
      ),
    );
    return [game.allOf([demonDies, noScarletWomanCatches, activeMastermind])];
  });
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
  doc: BuildDoc,
  ctx: Omit<CompileCtx, "nameRoot">,
  pukkaContext: PukkaContext,
  godfatherContext: GodfatherContext,
  goonContext: GoonContext,
  shabalothContext: ShabalothContext,
): NightDeathTimingContext {
  const beforeInfoAssignments = new Map<Timing, Map<string, BoolLike[]>>();
  const demonKillAssignments = new Map<string, BoolLike[]>();
  const po = new PoChoices(game);
  for (const [eventIndex, event] of (doc.timeline ?? []).entries()) {
    if (event.type !== "nightDeath") continue;
    const timing = event.timing as Timing;
    const sources = nightDeathSources(
      game,
      doc,
      event,
      ctx,
      po.chargedAt(timing),
      pukkaContext,
      godfatherContext,
      goonContext,
      shabalothContext,
    );
    const resolution = new DeathAssignments(
      game,
      doc.players,
      doc.facts.deadBefore(timing),
      doc.noKillSinking ?? false,
    );
    if (event.players.length === 0) for (const source of sources) resolution.bySource.set(source, []);
    for (const player of event.players) {
      const eligible = sources.filter((source) => source.players === undefined || source.players.includes(player));
      game.addExactlyOne(
        eligible.map((source) => {
          const value = resolution.assign(player, source);
          applyDeathConsequences(game, doc, event, { player, source, value });
          return value;
        }),
      );
    }
    for (const death of resolution.deaths) {
      const { player, source, value } = death;
      if (source.requiresDemonKillOf !== undefined)
        game.addImplication(value, game.anyOf(resolution.demonKills.get(source.requiresDemonKillOf) ?? []));
      if (source.kind !== undefined)
        addMapValue(demonKillAssignments, timelineEventPlayerKey(eventIndex, player), value);
      if (source.deathTiming === "beforeInfo") {
        let players = beforeInfoAssignments.get(timing);
        if (players === undefined) beforeInfoAssignments.set(timing, (players = new Map()));
        addMapValue(players, player, value);
      }
    }
    applyRequiredGrandmotherDeaths(game, doc, event, resolution.demonKills);
    resolution.constrainSources();
    game.withProvenance(
      {
        kind: doc.noKillSinking ? "assumption" : "rule",
        id: doc.noKillSinking ? "noKillSinking" : "nightDeathTargets",
      },
      () => resolution.constrainTargets((player) => demonKillProtectionAt(game, doc, player, timing)),
    );
    po.record(
      timing,
      resolution,
      game.not(
        game.anyOf(
          exorcistDemonKillBlockers(game, doc, timing, (player, healthTiming) =>
            game.soberAndHealthy(player, healthTiming),
          ),
        ),
      ),
    );
  }
  return {
    beforeInfoDeathsByTiming: new Map(
      [...beforeInfoAssignments].map(([timing, players]) => [timing, unionAssignments(game, players)]),
    ),
    demonKillAssignmentsByEventPlayer: unionAssignments(game, demonKillAssignments),
  };
}

function unionAssignments<K>(
  game: BOTCModel,
  assignments: ReadonlyMap<K, readonly BoolLike[]>,
): ReadonlyMap<K, BoolLike> {
  return new Map([...assignments].map(([key, values]) => [key, values.length === 1 ? values[0]! : game.anyOf(values)]));
}

function applyDeathConsequences(
  game: BOTCModel,
  doc: BuildDoc,
  event: TimelineEventDoc,
  { player, source, value: assignment }: AssignedDeath,
): void {
  const timing = event.timing as Timing;
  const roleTimings = doc.facts.timings;
  if (source.bypassesProtection !== true) {
    game.addImplication(assignment, game.not(deathProtectionAt(game, doc, player, timing)));
  }
  source.constrainAssignment?.(player, assignment);
  const succession = source.succession ?? [];
  if (succession.includes("Imp")) applyImpStarpass(game, doc, event, player, assignment, roleTimings);
  if (succession.includes("Fang Gu")) applyFangGuJump(game, doc, event, player, assignment, roleTimings);
  for (const role of ["Imp", "Fang Gu"] as const) {
    if (succession.includes(role) || !doc.script.includes(role)) continue;
    game.addImplication(
      game.allOf([assignment, roleAtBeforeEvent(game, doc, player, role, event)]),
      livingScarletWomanCanCatchDemonDeath(game, doc, event),
    );
  }
  applyScarletWomanCatch(game, doc, event, player, assignment, roleTimings, { excludedRoles: succession });
}

function timelineEventPlayerKey(eventIndex: number, player: string): string {
  return `${eventIndex}\u0000${player}`;
}

function nightDeathSources(
  game: BOTCModel,
  doc: BuildDoc,
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
    ...(doc.script.includes("Pit-Hag")
      ? [
          {
            id: `${timing}_pit_hag_arbitrary_death`,
            available: game.pitHagCreatedDemon(timing),
            maxAssignments: doc.players.length,
            requiredWhenAvailable: false,
            deathTiming: "beforeInfo" as const,
          },
        ]
      : []),
    ...atNightResolutionOrder(
      demonKillDeathSources(game, doc, event, poCharged, goonContext, shabalothContext),
      nightActionOrder("Po"),
    ),
    ...atNightResolutionOrder(pukkaDeathSources(game, doc, event, pukkaContext), nightActionOrder("Pukka")),
    ...atNightResolutionOrder(assassinDeathSources(game, doc, timing, goonContext), nightActionOrder("Assassin")),
    ...atNightResolutionOrder(godfatherDeathSources(timing, godfatherContext), nightActionOrder("Godfather")),
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
  doc: BuildDoc,
  timing: Timing,
  goonContext: GoonContext,
): readonly NightDeathSource[] {
  if (!doc.script.includes("Assassin")) return [];
  return doc.facts.livingAt(timing).flatMap((actor): NightDeathSource[] => {
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
    );
    const activeHealthy = game.allOf([
      game.hasAbilityAt(actor, "Assassin", timing),
      preGoonHealthy,
      game.not(game.abilityUsedBefore(actor, "Assassin", timing)),
    ]);
    if (declaredClaim !== undefined && !doc.facts.nightDeaths(timing).has(declaredClaim.target))
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

function godfatherDeathSources(timing: Timing, context: GodfatherContext): readonly NightDeathSource[] {
  return context.choices.flatMap((choice): NightDeathSource[] => {
    if (choice.timing !== timing) return [];
    return [...choice.targets].map(([target, selected]) => ({
      id: `${timing}_${slug(choice.actor)}_godfather_kills_${slug(target)}`,
      players: [target],
      available: selected,
      requiredWhenAvailable: false,
      deathTiming: "beforeInfo",
    }));
  });
}

function grandmotherDeathSources(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): readonly NightDeathSource[] {
  if (!doc.script.includes("Grandmother")) return [];
  const timing = event.timing as Timing;
  return doc.claims.flatMap((claim, index): NightDeathSource[] => {
    if (claim.type !== "Grandmother" || claim.grandchild === undefined || !event.players.includes(claim.grandchild))
      return [];
    const activeHealthy = game.allOf([
      game.hasAbilityAt(claim.name, "Grandmother", timing),
      game.soberAndHealthy(claim.name, timing),
    ]);
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
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  demonAssignmentsByPlayer: ReadonlyMap<string, readonly BoolLike[]>,
): void {
  if (!doc.script.includes("Grandmother")) return;
  const timing = event.timing as Timing;
  for (const claim of doc.claims) {
    if (claim.type !== "Grandmother" || claim.grandchild === undefined) continue;
    const demonKilledGrandchild = game.anyOf(demonAssignmentsByPlayer.get(claim.grandchild) ?? []);
    const trigger = game.allOf([
      game.hasAbilityAt(claim.name, "Grandmother", timing),
      game.soberAndHealthy(claim.name, timing),
      demonKilledGrandchild,
    ]);
    if (!event.players.includes(claim.name)) game.addFalse(trigger);
  }
}

function moonchildDeathSources(game: BOTCModel, doc: BuildDoc, timing: Timing): readonly NightDeathSource[] {
  if (!doc.script.includes("Moonchild")) return [];
  return doc.claims.flatMap((claim, index): NightDeathSource[] => {
    if (claim.type !== "Moonchild" || claim.chosen === undefined || claim.timing === undefined) return [];
    if (followingNight(claim.timing as Timing) !== timing) return [];
    const moonchildDead =
      doc.facts.deadBefore(claim.timing as Timing).has(claim.name) ||
      (doc.timeline ?? []).some(
        (event) => event.timing === claim.timing && isTimelineDeathEvent(event) && event.players.includes(claim.name),
      );
    if (!moonchildDead || !doc.facts.livingAt(claim.timing as Timing).includes(claim.chosen)) return [];
    const activeHealthyGoodTarget = game.allOf([
      game.actualIs(claim.name, "Moonchild"),
      game.soberAndHealthy(claim.name, timing),
      game.isGoodAt(claim.chosen, claim.timing as Timing),
    ]);
    if (!doc.facts.nightDeaths(timing).has(claim.chosen)) {
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

function tinkerDeathSources(game: BOTCModel, doc: BuildDoc, timing: Timing): readonly NightDeathSource[] {
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
          game.allOf([game.hasAbilityAt(player, "Tinker", timing), game.soberAndHealthy(player, timing)]),
        ),
    },
  ];
}

function pukkaDeathSources(
  game: BOTCModel,
  doc: BuildDoc,
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
    available: game.allOf([resolves, poisonedPlayers.get(player) ?? game.constantBool(false)]),
    kind: "demon",
    deathTiming: "beforeInfo",
    constrainAssignment: (victim, assignment) => constrainDemonKillVictim(game, doc, timing, victim, assignment),
  }));
}

function demonKillDeathSources(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  poCharged: BoolLike,
  goonContext: GoonContext,
  shabalothContext: ShabalothContext,
): readonly NightDeathSource[] {
  const timing = event.timing as Timing;
  const unblockedDemonKill = game.not(demonKillBlockedAt(game, doc, timing));
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
      targetCountWhenAvailable: 2,
    },
    {
      id: "zombuul_kill",
      roles: demonRoleNames.filter((role) => role === "Zombuul"),
      activeIf: nobodyDiedDuringPreviousDay(game, doc, timing),
      demonPath: doc.script.includes("Zombuul")
        ? game.anyOf(
            doc.players.map((player) =>
              game.allOf([game.actualIs(player, "Zombuul"), game.soberAndHealthy(player, timing)]),
            ),
          )
        : game.constantBool(false),
      maxAssignments: 1,
      requiredWhenAvailable: false,
      targetCountWhenAvailable: 1,
    },
    {
      id: "po_regular_kill",
      roles: demonRoleNames.filter((role) => role === "Po"),
      activeIf: game.not(poCharged),
      maxAssignments: 1,
      requiredWhenAvailable: false,
    },
    {
      id: "po_charged_kill",
      roles: demonRoleNames.filter((role) => role === "Po"),
      activeIf: poCharged,
      maxAssignments: 3,
      requiredWhenAvailable: false,
      targetCountWhenAvailable: 3,
    },
  ].filter((source) => source.roles.length > 0);

  return sourceSpecs.map((source): NightDeathSource => ({
    id: `${timing}_${source.id}`,
    available: game.allOf([
      source.demonPath ??
        livingDemonPathBeforeDeathEvent(game, doc, event, new Set(source.roles), (player) =>
          game.soberAndHealthy(player, timing),
        ),
      unblockedDemonKill,
      ...(source.activeIf === undefined ? [] : [source.activeIf]),
    ]),
    maxAssignments: source.maxAssignments,
    targetCountWhenAvailable: source.targetCountWhenAvailable,
    requiredWhenAvailable: source.requiredWhenAvailable,
    kind: source.roles.includes("Po") ? "po" : "demon",
    succession: source.roles.filter((role): role is "Imp" | "Fang Gu" => role === "Imp" || role === "Fang Gu"),
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
        const goonTargetedEarlier = goonWasTargetedBefore(game, goonContext, timing, firstDemonOrder);
        const killsGoon = game.allOf([assignment, game.hasAbilityAt(player, "Goon", timing)]);
        game.addImplication(killsGoon, goonTargetedEarlier);
      }
    },
  }));
}

function constrainDemonKillVictim(
  game: BOTCModel,
  doc: BuildDoc,
  timing: Timing,
  player: string,
  assignment: BoolLike,
): void {
  const innkeeperProtected = innkeeperProtectionAt(game, doc, player, timing);
  game.addImplication(assignment, game.not(innkeeperProtected));
  if (!doc.script.includes("Soldier")) return;
  const soberHealthySoldier = game.allOf([
    game.hasAbilityAt(player, "Soldier", timing),
    game.soberAndHealthy(player, timing),
  ]);
  game.addImplication(assignment, game.not(soberHealthySoldier));
}

function demonKillProtectionAt(game: BOTCModel, doc: BuildDoc, player: string, timing: Timing): BoolLike {
  const soberHealthySoldier = doc.script.includes("Soldier")
    ? game.allOf([game.hasAbilityAt(player, "Soldier", timing), game.soberAndHealthy(player, timing)])
    : game.constantBool(false);
  return game.anyOf([
    deathProtectionAt(game, doc, player, timing),
    soberHealthySoldier,
    game.pitHagCreatedDemon(timing),
  ]);
}

function innkeeperProtectionAt(game: BOTCModel, doc: BuildDoc, player: string, timing: Timing): BoolLike {
  if (!doc.script.includes("Innkeeper")) return game.constantBool(false);
  const deadPlayers = doc.facts.deadBefore(timing);
  const protectors = doc.claims.flatMap((claim) => {
    if (claim.type !== "Innkeeper" || deadPlayers.has(claim.name)) return [];
    return (claim.choices ?? []).flatMap((choice): BoolLike[] => {
      if (
        choice.timing !== timing ||
        choice.players.length !== 2 ||
        new Set(choice.players).size !== 2 ||
        choice.players.includes(claim.name) ||
        !choice.players.includes(player)
      )
        return [];
      return [
        game.allOf([game.hasAbilityAt(claim.name, "Innkeeper", timing), game.soberAndHealthy(claim.name, timing)]),
      ];
    });
  });
  return game.anyOf(protectors);
}

function nobodyDiedDuringPreviousDay(game: BOTCModel, doc: BuildDoc, timing: Timing): BoolLike {
  const match = /^night_(\d+)$/.exec(timing);
  if (match === null || Number(match[1]) <= 1) {
    return game.constantBool(false);
  }
  const dayTiming = `day_${Number(match[1]) - 1}`;
  const someoneDied = (doc.timeline ?? []).some(
    (event) => event.timing === dayTiming && isTimelineDeathEvent(event) && event.players.length > 0,
  );
  return game.constantBool(!someoneDied);
}

function fangGuDemonKillVictimAllowed(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  player: string,
): BoolLike {
  const outsiderBeforeEvent = characterTypeBeforeEvent(game, doc, player, CharacterType.Outsider, event);
  return game.anyOf([
    game.not(outsiderBeforeEvent),
    fangGuJumpedBeforeDeathEvent(game, doc, event),
    livingDemonPathBeforeDeathEvent(game, doc, event, new Set(doc.script.filter((role) => role !== "Fang Gu")), () =>
      game.constantBool(true),
    ),
  ]);
}

type HealthAt = (player: string, timing: Timing) => BoolLike;

function demonKillBlockedAt(
  game: BOTCModel,
  doc: BuildDoc,
  timing: Timing,
  healthAt: HealthAt = (player, healthTiming) => game.soberAndHealthy(player, healthTiming),
): BoolLike {
  return game.anyOf([
    ...princessDemonKillBlockers(game, doc, timing, healthAt),
    ...exorcistDemonKillBlockers(game, doc, timing, healthAt),
  ]);
}

function princessDemonKillBlockers(
  game: BOTCModel,
  doc: BuildDoc,
  timing: Timing,
  healthAt: HealthAt,
): readonly BoolLike[] {
  if (!doc.script.includes("Princess")) return [];
  const deadPlayers = doc.facts.deadBefore(timing);
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Princess" || deadPlayers.has(claim.name)) return [];
    return (claim.nominations ?? []).flatMap((nomination): BoolLike[] => {
      const nominationTiming = nomination.timing as Timing | undefined;
      if (nominationTiming === undefined || followingNight(nominationTiming) !== timing) return [];
      if (!doc.facts.executions(nominationTiming).has(nomination.player)) return [];
      return [game.allOf([game.hasAbilityAt(claim.name, "Princess", timing), healthAt(claim.name, timing)])];
    });
  });
}

function exorcistDemonKillBlockers(
  game: BOTCModel,
  doc: BuildDoc,
  timing: Timing,
  healthAt: HealthAt,
): readonly BoolLike[] {
  if (!doc.script.includes("Exorcist")) return [];
  const deadPlayers = doc.facts.deadBefore(timing);
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Exorcist" || deadPlayers.has(claim.name)) return [];
    return (claim.choices ?? []).flatMap((choice): BoolLike[] => {
      if (choice.timing !== timing) return [];
      return [
        game.allOf([
          game.hasAbilityAt(claim.name, "Exorcist", timing),
          healthAt(claim.name, timing),
          game.isDemonAt(choice.player, timing),
        ]),
      ];
    });
  });
}

function applyImpStarpass(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  deadPlayer: string,
  assignment: BoolLike,
  roleTimings: readonly Timing[],
): void {
  if (!doc.script.includes("Imp")) return;
  const timing = event.timing as Timing;
  const starpass = game.allOf([assignment, roleAtBeforeEvent(game, doc, deadPlayer, "Imp", event)]);
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  const successors = candidates.map((candidate) => {
    const successor = game.newBool();
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

  const futureTimings = roleTimings.filter((futureTiming) => timingOrder(futureTiming) >= timingOrder(timing));
  for (const futureTiming of futureTimings) {
    game.removeAbility(deadPlayer, "Imp", futureTiming, starpass);
    for (const { player, value } of successors) {
      game.replaceCharacter(player, "Imp", futureTiming, value);
    }
  }
}

function applyFangGuJump(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  deadPlayer: string,
  assignment: BoolLike,
  roleTimings: readonly Timing[],
): void {
  if (!doc.script.includes("Fang Gu")) return;
  const timing = event.timing as Timing;
  const jump = game.allOf([assignment, roleAtBeforeEvent(game, doc, deadPlayer, "Fang Gu", event)]);
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  const successors = candidates.map((candidate) => {
    const successor = game.newBool();
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

  const futureTimings = roleTimings.filter((futureTiming) => timingOrder(futureTiming) >= timingOrder(timing));
  for (const futureTiming of futureTimings) {
    game.removeAbility(deadPlayer, "Fang Gu", futureTiming, jump);
    for (const { player, value } of successors) {
      game.replaceCharacter(player, "Fang Gu", futureTiming, value);
    }
  }
}

function applyScarletWomanCatch(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  deadPlayer: string,
  assignment: BoolLike,
  roleTimings: readonly Timing[],
  options: { readonly excludedRoles?: readonly string[] } = {},
): void {
  if (!doc.script.includes("Scarlet Woman")) return;
  if (doc.facts.livingAt(event.timing as Timing).length < 5) return;
  const timing = event.timing as Timing;
  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => {
    if (roleCharacterType(role) !== CharacterType.Demon) return false;
    const name = roleName(role);
    return name !== "Zombuul" && name !== "Legion" && name !== "Riot" && !options.excludedRoles?.includes(name);
  });
  if (demonRoles.length === 0) return;

  for (const demonRole of demonRoles) {
    const caught = game.allOf([
      assignment,
      roleAtBeforeEvent(game, doc, deadPlayer, demonRole, event),
      livingScarletWomanCanCatchDemonDeath(game, doc, event),
    ]);
    const candidates = livingPlayersAfterDeathEvent(doc, event);
    const successors = candidates.map((candidate) => {
      const successor = game.newBool();
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

    const futureTimings = roleTimings.filter((futureTiming) => timingOrder(futureTiming) >= timingOrder(timing));
    for (const futureTiming of futureTimings) {
      game.removeAbility(deadPlayer, demonRole, futureTiming, caught);
      for (const { player, value } of successors) {
        game.replaceCharacter(player, demonRole, futureTiming, value);
      }
    }
  }
}

function gossipDeathSources(
  game: BOTCModel,
  doc: BuildDoc,
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
          available: game.allOf([
            game.hasAbilityAt(claim.name, "Gossip", statementTiming),
            game.hasAbilityAt(claim.name, "Gossip", timing),
            game.soberAndHealthy(claim.name, timing),
            learned,
          ]),
        },
      ];
    });
  });
}

function acrobatDeathSources(game: BOTCModel, doc: BuildDoc, timing: Timing): readonly NightDeathSource[] {
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Acrobat") return [];
    return (claim.choices ?? []).flatMap((choice, index): NightDeathSource[] => {
      if (!choice.died || choice.timing !== timing) return [];
      const targetDrunkOrPoisoned = game.anyOf([
        game.isDroisonedAt(choice.player, timing),
        game.noDashiiPoisonedAt(choice.player, timing),
      ]);
      return [
        {
          id: `${timing}_${slug(claim.name)}_acrobat_${index + 1}`,
          players: [claim.name],
          available: game.allOf([
            game.hasAbilityAt(claim.name, "Acrobat", timing),
            game.soberAndHealthy(claim.name, timing),
            targetDrunkOrPoisoned,
          ]),
        },
      ];
    });
  });
}

function gamblerDeathSources(game: BOTCModel, doc: BuildDoc, timing: Timing): readonly NightDeathSource[] {
  return doc.claims.flatMap((claim) => {
    if (claim.type !== "Gambler") return [];
    return (claim.guesses ?? []).flatMap((guess, index): NightDeathSource[] => {
      if (guess.timing !== timing) return [];
      const correct = game.registersAsRole(guess.player, resolveRoleRef(guess.role));
      return [
        {
          id: `${timing}_${slug(claim.name)}_gambler_${index + 1}`,
          players: [claim.name],
          available: game.allOf([
            game.hasAbilityAt(claim.name, "Gambler", timing),
            game.soberAndHealthy(claim.name, timing),
            game.not(correct),
          ]),
        },
      ];
    });
  });
}

function livingDemonPathBeforeDeathEvent(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  allowedRoles: ReadonlySet<string>,
  eligible: (player: string) => BoolLike,
): BoolLike {
  const livingPlayers = doc.facts.livingAt(event.timing as Timing);
  const livingPlayerSet = new Set(livingPlayers);
  const deadPlayers = doc.players.filter((player) => !livingPlayerSet.has(player));
  const demonRoles = doc.script
    .map(resolveRoleRef)
    .filter((role) => roleCharacterType(role) === CharacterType.Demon && allowedRoles.has(roleName(role)));
  const healthyLivingDemons = livingPlayers.flatMap((player) =>
    demonRoles.map((role) => game.allOf([roleAtBeforeEvent(game, doc, player, role, event), eligible(player)])),
  );
  const healthySuccessions: BoolLike[] = [];

  if (demonRoles.some((role) => roleName(role) === "Imp")) {
    healthySuccessions.push(
      game.allOf([
        game.anyOf(deadPlayers.map((player) => game.actualIs(player, "Imp"))),
        game.anyOf(
          livingPlayers.map((player) => game.allOf([isMinionBeforeEvent(game, doc, player, event), eligible(player)])),
        ),
      ]),
    );
  }

  if (doc.script.includes("Scarlet Woman")) {
    const deadNonImpDemons = deadPlayers.flatMap((player) =>
      demonRoles.filter((role) => roleName(role) !== "Imp").map((role) => game.actualIs(player, role)),
    );
    healthySuccessions.push(
      game.allOf([
        game.anyOf(deadNonImpDemons),
        game.anyOf(
          livingPlayers.map((player) =>
            game.allOf([roleAtBeforeEvent(game, doc, player, "Scarlet Woman", event), eligible(player)]),
          ),
        ),
      ]),
    );
  }

  return game.anyOf([...healthyLivingDemons, ...healthySuccessions]);
}

function fangGuJumpedBeforeDeathEvent(
  game: BOTCModel,
  doc: BuildDoc,
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
  );
}

function applyTimelineClaimContext(
  claim: PuzzleDoc["claims"][number],
  doc: BuildDoc,
  game: BOTCModel,
  nightDeathTiming: NightDeathTimingContext,
): ClaimWithTimelineContext {
  if (claim.type === "Slayer" && claim.timing !== undefined) {
    return { ...claim, alivePlayerCount: doc.facts.livingAt(claim.timing as Timing).length };
  }
  if (claim.type === "Legionary" && claim.counts !== undefined) {
    return {
      ...claim,
      counts: claim.counts.map((count, index) => {
        const timing = (count.timing ?? `night_${index + 1}`) as Timing;
        return { ...count, timing, alivePlayers: doc.facts.livingAt(timing) };
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

function infoLifeOptions(
  game: BOTCModel,
  doc: BuildDoc,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): readonly { deadPlayers: ReadonlySet<string>; activeIf: BoolLike }[] {
  const deadPlayers = doc.facts.deadBefore(timing);
  const sameNightDeaths = [...(nightDeathTiming.beforeInfoDeathsByTiming.get(timing)?.entries() ?? [])].filter(
    ([player]) => !deadPlayers.has(player),
  );
  return Array.from({ length: 1 << sameNightDeaths.length }, (_, mask) => {
    const dead = new Set(deadPlayers);
    const conditions = sameNightDeaths.map(([player, beforeInfo], index) => {
      if ((mask & (1 << index)) === 0) return game.not(beforeInfo);
      dead.add(player);
      return beforeInfo;
    });
    return { deadPlayers: dead, activeIf: game.allOf(conditions) };
  });
}

function oracleDeadPlayerOptionsAt(
  game: BOTCModel,
  doc: BuildDoc,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): readonly OracleDeadPlayerOption[] {
  return infoLifeOptions(game, doc, timing, nightDeathTiming).map(({ deadPlayers, activeIf }) => ({
    deadPlayers: playersInDocOrder(doc, deadPlayers),
    activeIf,
  }));
}

function livingNeighborOptionsAt(
  game: BOTCModel,
  doc: BuildDoc,
  player: string,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): readonly EmpathNeighborOption[] {
  const groups = new Map<string, { neighbors: [string, string]; conditions: BoolLike[] }>();
  for (const { deadPlayers, activeIf } of infoLifeOptions(game, doc, timing, nightDeathTiming)) {
    const neighbors = doc.facts.neighbors(player, deadPlayers);
    const key = neighbors.join("\u0000");
    const group = groups.get(key) ?? { neighbors, conditions: [] };
    group.conditions.push(activeIf);
    groups.set(key, group);
  }
  return [...groups.values()].map(({ neighbors, conditions }) => ({
    neighbors,
    activeIf: game.anyOf(conditions),
  }));
}

function applyPoisonerSources(game: BOTCModel, doc: BuildDoc, nightDeathTiming: NightDeathTimingContext): void {
  if (!doc.script.includes("Poisoner")) return;
  const timings = new Set([
    ...game.droisonTimingKeys,
    ...doc.facts.nights.flatMap((timing) => [timing, timing.replace("night_", "day_")]),
  ]);
  for (const timing of timings) {
    const poisonerCanAct = roleCanUseAbilityAt(game, doc, "Poisoner", timing as Timing, nightDeathTiming);
    const poisonerDiesBeforeInfo = roleDiesBeforeInfoAt(game, "Poisoner", timing as Timing, nightDeathTiming);
    game.addPoisonerEffect(timing as Timing, {
      activeIf: game.allOf([poisonerCanAct, game.not(poisonerDiesBeforeInfo)]),
    });
  }
}

function applyVigormortisPoisonSources(
  game: BOTCModel,
  doc: BuildDoc,
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
      const active = game.allOf([
        demonKill,
        isMinionBeforeEvent(game, doc, deadPlayer, event),
        livingVigormortisPathBeforeDeathEvent(game, doc, event),
      ]);
      const timings = [...game.droisonTimingKeys]
        .filter((timing): timing is Timing => /^(night|day)_\d+$/.test(timing))
        .filter((timing) => timingOrder(timing) > timingOrder(event.timing as Timing));
      game.addPersistentPoisonSource(timings, game.neighbors(deadPlayer), active);
    }
  }
}

function roleCanUseAbilityAt(
  game: BOTCModel,
  doc: BuildDoc,
  role: RoleRef,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): BoolLike {
  const roleRef = resolveRoleRef(roleName(role));
  const activeSources = [roleAliveAt(game, doc, roleRef, timing)];
  if (roleCharacterType(roleRef) === CharacterType.Minion) {
    activeSources.push(vigormortisKilledMinionRoleBeforeTiming(game, doc, roleRef, timing, nightDeathTiming));
  }
  return game.anyOf(activeSources);
}

function vigormortisKilledMinionRoleBeforeTiming(
  game: BOTCModel,
  doc: BuildDoc,
  role: RoleRef,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): BoolLike {
  if (!doc.script.includes("Vigormortis")) {
    return game.constantBool(false);
  }
  const phaseOrder = timingOrder(timing);
  const options = (doc.timeline ?? []).flatMap((event, eventIndex): BoolLike[] => {
    if (event.type !== "nightDeath" || deathEventOrder(event) >= phaseOrder) return [];
    return event.players.flatMap((player): BoolLike[] => {
      const demonKill = nightDeathTiming.demonKillAssignmentsByEventPlayer.get(
        timelineEventPlayerKey(eventIndex, player),
      );
      if (demonKill === undefined) return [];
      return [
        game.allOf([
          demonKill,
          roleAtBeforeEvent(game, doc, player, role, event),
          livingVigormortisPathBeforeDeathEvent(game, doc, event),
        ]),
      ];
    });
  });
  return game.anyOf(options);
}

function livingVigormortisPathBeforeDeathEvent(
  game: BOTCModel,
  doc: BuildDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  if (!doc.script.includes("Vigormortis")) {
    return game.constantBool(false);
  }
  return game.anyOf(
    doc.facts
      .livingAt(event.timing as Timing)
      .map((player) => roleAtBeforeEvent(game, doc, player, "Vigormortis", event)),
  );
}

function roleDiesBeforeInfoAt(
  game: BOTCModel,
  role: RoleRef,
  timing: Timing,
  nightDeathTiming: NightDeathTimingContext,
): BoolLike {
  const beforeInfoDeaths = nightDeathTiming.beforeInfoDeathsByTiming.get(timing);
  if (beforeInfoDeaths === undefined) return game.constantBool(false);
  return game.anyOf(
    [...beforeInfoDeaths.entries()].map(([player, diesBeforeInfo]) =>
      game.allOf([diesBeforeInfo, game.hasAbilityAt(player, role, timing)]),
    ),
  );
}

function applyWidowSources(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Widow")) return;
  const timings = [...game.droisonTimingKeys].filter((timing): timing is Timing => timing !== "default");
  game.addWidowEffect({ timings, activeIf: roleAliveAt(game, doc, "Widow", "night_1") });
}

function applyXaanActivity(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Xaan")) return;
  for (let count = 1; count <= doc.players.length; count += 1) {
    const timing = `night_${count}` as Timing;
    game.setRoleActiveAt("Xaan", timing, roleAliveAt(game, doc, "Xaan", timing));
  }
}

function applyWidowCallClaims(game: BOTCModel, doc: BuildDoc): void {
  const heardCallClaims = doc.claims.filter((claim) => claim.heardWidowCall === true);
  for (const claim of doc.claims) {
    if (claim.heardWidowCall !== true) continue;
    const widowInPlay = doc.script.includes("Widow") ? game.roleInPlay("Widow") : game.constantBool(false);
    game.addImplication(claimantIsGoodWhenClaimed(game, claim), widowInPlay);
  }
  if (!doc.script.includes("Widow")) return;
  game.addImplication(
    game.roleInPlay("Widow"),
    game.anyOf(heardCallClaims.map((claim) => claimantIsGoodWhenClaimed(game, claim))),
  );
}

function applyEvilTwinKnowledgeClaims(game: BOTCModel, doc: BuildDoc): void {
  const knowledgeClaims = doc.claims.filter(
    (claim): claim is typeof claim & { readonly knownEvilTwin: string } => claim.knownEvilTwin !== undefined,
  );
  for (const claim of knowledgeClaims) {
    const knownPlayerIsEvilTwin = doc.script.includes("Evil Twin")
      ? game.actualIs(claim.knownEvilTwin, "Evil Twin")
      : game.constantBool(false);
    game.addImplication(claimantIsGoodWhenClaimed(game, claim), knownPlayerIsEvilTwin);
  }
  if (!doc.script.includes("Evil Twin")) return;
  game.addImplication(
    game.roleInPlay("Evil Twin"),
    game.anyOf(
      knowledgeClaims.map((claim) =>
        game.allOf([claimantIsGoodWhenClaimed(game, claim), game.actualIs(claim.knownEvilTwin, "Evil Twin")]),
      ),
    ),
  );
}

function claimantIsGoodWhenClaimed(game: BOTCModel, claim: PuzzleDoc["claims"][number]): BoolLike {
  if (claim.timing === undefined) return game.isGood(claim.name);
  const timing = claim.timing as Timing;
  return game.hasAlignmentOverrideAt(claim.name, timing) ? game.isGoodAt(claim.name, timing) : game.isGood(claim.name);
}

function applyPuzzlemasterSources(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Puzzlemaster")) return;
  for (const claim of doc.claims) {
    if (claim.type !== "Puzzlemaster") continue;
    game.addPuzzlemasterDrunking({
      excludedPlayers: [claim.name],
      activeIf: game.actualIs(claim.name, "Puzzlemaster"),
    });
  }
}

function applyLleechHostChoice(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Lleech")) return;
  game.addLleechHostChoice();
  const finalLivingPlayers = new Set(doc.facts.finalLiving);
  for (const player of doc.players) {
    if (!finalLivingPlayers.has(player)) {
      game.addFalse(game.lleechHost(player));
    }
  }
}

function applyLleechHostPoisoning(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Lleech")) return;
  const timings = [...game.droisonTimingKeys].filter((timing): timing is Timing => timing !== "default");
  game.addLleechHostPoisoning(timings);
}

function applySweetheartSources(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Sweetheart")) return;

  const activeByTiming = doc.facts.timings.flatMap((timing) => {
    const possiblePriorSweetheartDeaths = (doc.timeline ?? [])
      .filter((event) => isTimelineDeathEvent(event) && deathEventOrder(event) < timingOrder(timing))
      .flatMap((event) => event.players.map((player) => roleAtBeforeEvent(game, doc, player, "Sweetheart", event)));
    if (possiblePriorSweetheartDeaths.length === 0) return [];
    return [
      {
        timing,
        activeIf: game.anyOf(possiblePriorSweetheartDeaths),
      },
    ];
  });
  if (activeByTiming.length === 0) return;

  game.addPersistentDrunking(
    activeByTiming.map((entry) => entry.timing),
    { activeByTiming },
  );
}

function applyVillageIdiotSources(game: BOTCModel, doc: BuildDoc): void {
  if (!doc.script.includes("Village Idiot")) return;
  game.addVillageIdiotDrunking();
}

function roleAliveAt(game: BOTCModel, doc: BuildDoc, role: RoleRef, timing: Timing): BoolLike {
  const roleRef = roleName(role);
  const deadPlayers = doc.facts.deadBefore(timing);
  const candidates = doc.players.filter((player) => !deadPlayers.has(player));
  return game.anyOf(candidates.map((player) => game.hasAbilityAt(player, roleRef, timing)));
}

function healthyRoleAliveAt(game: BOTCModel, doc: BuildDoc, role: RoleRef, timing: Timing): BoolLike {
  const roleRef = roleName(role);
  const deadPlayers = doc.facts.deadBefore(timing);
  const candidates = doc.players.filter((player) => !deadPlayers.has(player));
  return game.anyOf(
    candidates.map((player) =>
      game.allOf([game.hasAbilityAt(player, roleRef, timing), game.soberAndHealthy(player, timing)]),
    ),
  );
}

function isMinionBeforeEvent(
  game: BOTCModel,
  doc: BuildDoc,
  player: string,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  return characterTypeBeforeEvent(game, doc, player, CharacterType.Minion, event);
}

function characterTypeBeforeEvent(
  game: BOTCModel,
  doc: BuildDoc,
  player: string,
  characterType: CharacterType,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const roles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === characterType);
  return game.anyOf(roles.map((role) => roleAtBeforeEvent(game, doc, player, role, event)));
}

function roleAtBeforeEvent(
  game: BOTCModel,
  doc: BuildDoc,
  player: string,
  role: RoleRef,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const previousTiming = doc.facts.previousTiming(event.timing as Timing);
  return previousTiming === undefined ? game.actualIs(player, role) : game.hasAbilityAt(player, role, previousTiming);
}

function playersInDocOrder(doc: BuildDoc, players: ReadonlySet<string>): readonly string[] {
  return doc.players.filter((player) => players.has(player));
}
