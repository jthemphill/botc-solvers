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
  applyRiotTransformations(game, doc);
  applyOngoingGameConstraint(game, doc);
  const nightDeathTiming =
    doc.setup === "atheist" ? emptyNightDeathTimingContext() : applyNightDeathSourceConstraints(game, doc, ctx);
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
  if (doc.setup !== "atheist") {
    applyPhilosopherDrunking(game, doc);
    applyChangedRoleClaimExplanations(game, doc);
    applyXaanActivity(game, doc);
    applyPoisonerSources(game, doc, nightDeathTiming);
    applyWidowSources(game, doc);
    applyWidowCallClaims(game, doc);
    applyEvilTwinDeclarationClaims(game, doc);
    applyVillageIdiotSources(game, doc);
  }
  return game;
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
  const explanations: BoolLike[] = [claimedRoleAtTiming, game.isEvil(claim.name)];

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
      for (const player of event.players) game.addTruth(executionSurvivalAt(game, doc, player, event.timing as Timing));
      continue;
    }

    if (isTimelineDeathEvent(event)) {
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
    if (event.type === "nightDeath" || event.type === "witchCurse" || event.type === "slayerShot") {
      for (const player of event.players) {
        for (const demonRole of demonRoles) {
          const demonRoleName = roleName(demonRole);
          if (demonRoleName === "Legion") continue;
          game.addImplication(
            game.actualIs(player, demonRole),
            event.type === "nightDeath" && demonRoleName === "Imp"
              ? livingMinionCanCatchDemonDeath(game, doc, event)
              : event.type === "nightDeath" && demonRoleName === "Fang Gu"
                ? livingOutsiderCanCatchFangGuJump(game, doc, event)
                : livingScarletWomanCanCatchDemonDeath(game, doc, event),
          );
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
        game.fixNotActual(player, demonRole);
      }
    }
  }
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
  return teaLadyProtectsAt(game, doc, player, timing);
}

function executionSurvivalAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  return game.anyOf(
    [teaLadyProtectsAt(game, doc, player, timing), devilsAdvocateProtectsExecutionAt(game, doc, timing)],
    `${timing}_${slug(player)}_survived_execution_source`,
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
        ? game.isGood(left)
        : game.allOf([game.isGood(left), game.isGood(right)], `${timing}_${slug(candidate)}_tea_lady_neighbors_good`);
    return [
      game.allOf(
        [game.hasRoleAt(candidate, "Tea Lady", timing), game.soberAndHealthy(candidate, healthTiming), goodNeighbors],
        `${timing}_${slug(candidate)}_tea_lady_protects_${slug(player)}`,
      ),
    ];
  });
  return game.anyOf(protectors, `${timing}_${slug(player)}_tea_lady_protected`);
}

function devilsAdvocateProtectsExecutionAt(game: BOTCModel, doc: PuzzleDoc, timing: Timing): BoolLike {
  if (!doc.script.includes("Devil's Advocate")) {
    return game.constantBool(false, `${timing}_no_devils_advocate_protection`);
  }
  const abilityTiming = healthTimingForDayAbility(timing);
  return game.anyOf(
    livingPlayersAt(doc, abilityTiming).map((candidate) =>
      game.allOf(
        [game.hasRoleAt(candidate, "Devil's Advocate", abilityTiming), game.soberAndHealthy(candidate, abilityTiming)],
        `${timing}_${slug(candidate)}_devils_advocate_execution_protection`,
      ),
    ),
    `${timing}_devils_advocate_protects_execution`,
  );
}

function witchCurseSourceAvailable(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const timing = event.timing as Timing;
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

  game.addTruth(
    game.anyOf([...finalLivingStartingDemon, ...possibleSuccessions], "ongoing_game_has_living_demon_or_successor"),
  );
}

interface NightDeathSource {
  readonly id: string;
  readonly available: BoolLike;
  readonly players?: readonly string[];
  readonly demonKill?: boolean;
  readonly starpassesImp?: boolean;
  readonly fangGuJumps?: boolean;
  readonly deathTiming?: "beforeInfo" | "afterInfo";
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
): NightDeathTimingContext {
  const roleTimings = collectTimings(doc);
  const beforeInfoAssignments = new Map<Timing, Map<string, BoolLike[]>>();
  const demonKillAssignments = new Map<string, BoolLike[]>();
  for (const [eventIndex, event] of (doc.timeline ?? []).entries()) {
    if (event.type !== "nightDeath") continue;
    const sources = nightDeathSources(game, doc, event, ctx);
    const assignmentsBySource = new Map<NightDeathSource, BoolLike[]>();

    for (const player of event.players) {
      const eligibleSources = sources.filter(
        (source) => source.players === undefined || source.players.includes(player),
      );
      const assignments = eligibleSources.map((source) => {
        const assignment = game.newBool(`${event.timing}_${player}_death_from_${source.id}`);
        game.addImplication(assignment, source.available);
        source.constrainAssignment?.(player, assignment);
        if (source.starpassesImp === true) applyImpStarpass(game, doc, event, player, assignment, roleTimings);
        if (source.fangGuJumps === true) applyFangGuJump(game, doc, event, player, assignment, roleTimings);
        applyScarletWomanCatch(game, doc, event, player, assignment, roleTimings);
        if (source.demonKill === true) {
          const key = timelineEventPlayerKey(eventIndex, player);
          demonKillAssignments.set(key, [...(demonKillAssignments.get(key) ?? []), assignment]);
        }
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
        return assignment;
      });
      game.addExactlyOne(assignments);
    }

    const sourceCapacityActive = game.constantBool(true, `${event.timing}_night_death_source_capacity_active`);
    for (const [source, assignments] of assignmentsBySource) {
      game.addEnforcedAtMostN(assignments, 1, sourceCapacityActive);
      const sourceAssigned =
        assignments.length === 1
          ? (assignments[0] as BoolLike)
          : game.anyOf(assignments, `${event.timing}_${source.id}_assigned`);
      game.addImplication(source.available, sourceAssigned);
    }
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
): readonly NightDeathSource[] {
  const timing = event.timing as Timing;
  return [
    demonKillDeathSource(game, doc, event),
    ...gossipDeathSources(game, doc, event, ctx),
    ...acrobatDeathSources(game, doc, timing),
    ...gamblerDeathSources(game, doc, timing),
  ];
}

function demonKillDeathSource(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): NightDeathSource {
  const timing = event.timing as Timing;
  const unblockedDemonKill = game.not(demonKillBlockedAt(game, doc, timing), `${timing}_demon_kill_not_blocked`);
  return {
    id: `${timing}_demon_kill`,
    available: game.allOf(
      [livingDemonPathBeforeDeathEvent(game, doc, event), unblockedDemonKill],
      `${timing}_demon_kill_source_available`,
    ),
    demonKill: true,
    starpassesImp: true,
    fangGuJumps: true,
    deathTiming: "beforeInfo",
    constrainAssignment: (player, assignment) => {
      if (doc.script.includes("Fang Gu")) {
        game.addImplication(assignment, fangGuDemonKillVictimAllowed(game, doc, event, player));
      }
      if (!doc.script.includes("Soldier")) return;
      const soberHealthySoldier = game.allOf(
        [game.hasRoleAt(player, "Soldier", timing), game.soberAndHealthy(player, timing)],
        `${timing}_${slug(player)}_sober_healthy_soldier`,
      );
      game.addImplication(
        assignment,
        game.not(soberHealthySoldier, `${timing}_${slug(player)}_not_sober_healthy_soldier_demon_kill`),
      );
    },
  };
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

function demonKillBlockedAt(game: BOTCModel, doc: PuzzleDoc, timing: Timing): BoolLike {
  return game.anyOf(
    [...princessDemonKillBlockers(game, doc, timing), ...exorcistDemonKillBlockers(game, doc, timing)],
    `${timing}_demon_kill_blocked`,
  );
}

function princessDemonKillBlockers(game: BOTCModel, doc: PuzzleDoc, timing: Timing): readonly BoolLike[] {
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
          [game.hasRoleAt(claim.name, "Princess", timing), game.soberAndHealthy(claim.name, timing)],
          `${timing}_${slug(claim.name)}_princess_nomination_${index + 1}_blocks_demon`,
        ),
      ];
    });
  });
}

function exorcistDemonKillBlockers(game: BOTCModel, doc: PuzzleDoc, timing: Timing): readonly BoolLike[] {
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
            game.soberAndHealthy(claim.name, timing),
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
): void {
  if (!doc.script.includes("Scarlet Woman")) return;
  const timing = event.timing as Timing;
  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => {
    if (roleCharacterType(role) !== CharacterType.Demon) return false;
    const name = roleName(role);
    return name !== "Imp" && name !== "Fang Gu";
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
      });
      return [
        {
          id: `${event.timing}_${slug(claim.name)}_gossip_${index + 1}`,
          deathTiming: "beforeInfo",
          available: game.allOf(
            [game.hasRoleAt(claim.name, "Gossip", statementTiming), game.soberAndHealthy(claim.name, timing), learned],
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
        [
          game.isDrunkAt(choice.player, timing),
          game.isPoisonedAt(choice.player, timing),
          game.noDashiiPoisonedAt(choice.player, timing),
        ],
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
      if (guess.timing !== timing || guess.survived === true) return [];
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
): BoolLike {
  const livingPlayers = livingPlayersBeforeDeathEvent(doc, event);
  const livingPlayerSet = new Set(livingPlayers);
  const deadPlayers = doc.players.filter((player) => !livingPlayerSet.has(player));
  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === CharacterType.Demon);
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
    if (!isTimelineDeathEvent(event)) continue;
    for (const player of event.players) deadPlayers.add(player);
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
  for (const timing of game.poisonTimingKeys) {
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
  const timings = [...game.poisonTimingKeys].filter((timing): timing is Timing => timing !== "default");
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
    game.addImplication(game.isGood(claim.name), widowInPlay);
  }
  if (!doc.script.includes("Widow")) return;
  game.addImplication(
    game.roleInPlay("Widow"),
    game.anyOf(
      heardCallClaims.map((claim) => game.isGood(claim.name)),
      "good_player_heard_widow_call",
    ),
  );
}

function applyEvilTwinDeclarationClaims(game: BOTCModel, doc: PuzzleDoc): void {
  const declarationClaims = doc.claims.flatMap((claim) =>
    claim.type === "Snake Charmer" && claim.evilTwin !== undefined
      ? [{ name: claim.name, player: claim.evilTwin.player }]
      : [],
  );
  for (const claim of declarationClaims) {
    const declaredEvilTwin = doc.script.includes("Evil Twin")
      ? game.actualIs(claim.player, "Evil Twin")
      : game.constantBool(false, `${slug(claim.name)}_declared_evil_twin_without_evil_twin_on_script`);
    game.addImplication(game.isGood(claim.name), declaredEvilTwin);
  }
  if (!doc.script.includes("Evil Twin")) return;
  game.addImplication(
    game.roleInPlay("Evil Twin"),
    game.anyOf(
      declarationClaims.map((claim) =>
        game.allOf(
          [game.isGood(claim.name), game.actualIs(claim.player, "Evil Twin")],
          `${slug(claim.name)}_declares_${slug(claim.player)}_evil_twin`,
        ),
      ),
      "good_player_declared_evil_twin",
    ),
  );
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
    if (!isTimelineDeathEvent(event)) continue;
    if (deathEventOrder(event) >= timingOrder) continue;
    for (const player of event.players) dead.add(player);
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
