import { applyClaims, type EmpathNeighborOption } from "../model/characters";
import { Alignment, CharacterType, roleAlignment, roleCharacterType, roleName, type RoleRef } from "../model/core";
import type { BoolLike, BOTCModel, Timing } from "../model/model";
import type { SatBackend } from "../model/sat";
import { buildPuzzleModel, type PuzzleSpec } from "../model/setup";
import type { PuzzleDoc } from "../schema/puzzleDoc";
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
  for (const fixedRole of doc.fixedRoles ?? []) {
    if (fixedRole.name && fixedRole.roles.length > 0) {
      game.setPossibleActualRoles(fixedRole.name, fixedRole.roles.map(resolveRoleRef));
    }
  }
  for (const forbiddenRole of doc.forbiddenRoles ?? []) {
    if (forbiddenRole.name) {
      for (const role of forbiddenRole.roles) game.fixNotActual(forbiddenRole.name, resolveRoleRef(role));
    }
  }
  if (doc.setup === "atheist") applyAtheistSetup(game, doc);
  applyTimelineConstraints(game, doc);
  applyOngoingGameConstraint(game, doc);
  const ctx = { players: doc.players, script: doc.script };
  const nightDeathTiming =
    doc.setup === "atheist" ? emptyNightDeathTimingContext() : applyNightDeathSourceConstraints(game, doc, ctx);
  const claims = doc.claims.map((claim) => applyTimelineClaimContext(claim, doc, game, nightDeathTiming));
  const ordinaryClaims = claims.filter((claim) => !usesMalfunctionCount(claim)).map((claim) => buildClaim(claim, ctx));
  const malfunctionCountClaims = claims
    .filter((claim) => usesMalfunctionCount(claim))
    .map((claim) => buildClaim(claim, ctx));
  const claimOptions = doc.setup === "atheist" ? { info: () => undefined } : {};
  applyClaims(game, ordinaryClaims, claimOptions);
  applyClaims(game, malfunctionCountClaims, claimOptions);
  if (doc.setup !== "atheist") {
    applyPoisonerSources(game, doc);
    applyXaanSources(game, doc);
    applyWidowSources(game, doc);
    applyWidowCallClaims(game, doc);
    applyPuzzlemasterSources(game, doc);
    applyVillageIdiotSources(game, doc);
  }
  return game;
}

function applyAtheistSetup(game: BOTCModel, doc: PuzzleDoc): void {
  const evilRoles = doc.script.map(resolveRoleRef).filter((role) => roleAlignment(role) === Alignment.Evil);
  for (const player of doc.players) {
    for (const role of evilRoles) game.fixNotActual(player, role);
  }
  if (doc.script.includes("Atheist")) game.addTruth(game.roleInPlay("Atheist"));
}

function applyTimelineConstraints(game: BOTCModel, doc: PuzzleDoc): void {
  const deathEvents = doc.timeline ?? [];
  if (deathEvents.length === 0) return;

  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === CharacterType.Demon);
  for (const event of deathEvents) {
    if (event.type === "doomsayerDeath" && event.caller !== undefined) {
      for (const player of event.players) {
        game.addTruth(doomsayerSameRegisteredAlignment(game, event.caller, player));
      }
    }
    if (event.type === "nightDeath" || event.type === "witchCurse" || event.type === "slayerShot") {
      for (const player of event.players) {
        for (const demonRole of demonRoles) {
          game.addImplication(
            game.actualIs(player, demonRole),
            event.type === "nightDeath" && roleName(demonRole) === "Imp"
              ? livingMinionCanCatchDemonDeath(game, doc, event)
              : livingScarletWomanCanCatchDemonDeath(game, doc, event),
          );
        }
      }
      continue;
    }
    if (event.type === "doomsayerDeath") continue;
    for (const player of event.players) {
      for (const demonRole of demonRoles) game.fixNotActual(player, demonRole);
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
  const finalLivingStartingDemon = finalLivingPlayers.flatMap((player) =>
    demonRoles.map((role) => game.actualIs(player, role)),
  );
  const possibleSuccessions: BoolLike[] = [];

  if (doc.script.includes("Imp")) {
    possibleSuccessions.push(
      game.allOf(
        [
          game.anyOf(
            finalDeadPlayers.map((player) => game.actualIs(player, "Imp")),
            "dead_imp_before_current_state",
          ),
          game.anyOf(
            finalLivingPlayers.map((player) => game.isMinion(player)),
            "final_living_minion_can_be_demon",
          ),
        ],
        "final_imp_successor_can_be_alive",
      ),
    );
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

  game.addTruth(
    game.anyOf([...finalLivingStartingDemon, ...possibleSuccessions], "ongoing_game_has_living_demon_or_successor"),
  );
}

interface NightDeathSource {
  readonly id: string;
  readonly available: BoolLike;
  readonly players?: readonly string[];
  readonly starpassesImp?: boolean;
  readonly deathTiming?: "beforeInfo" | "afterInfo";
  readonly constrainAssignment?: (player: string, assignment: BoolLike) => void;
}

interface NightDeathTimingContext {
  readonly beforeInfoDeathsByTiming: ReadonlyMap<Timing, ReadonlyMap<string, BoolLike>>;
}

function emptyNightDeathTimingContext(): NightDeathTimingContext {
  return { beforeInfoDeathsByTiming: new Map() };
}

function applyNightDeathSourceConstraints(
  game: BOTCModel,
  doc: PuzzleDoc,
  ctx: Omit<CompileCtx, "nameRoot">,
): NightDeathTimingContext {
  const roleTimings = collectTimings(doc);
  const beforeInfoAssignments = new Map<Timing, Map<string, BoolLike[]>>();
  for (const event of doc.timeline ?? []) {
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
    for (const assignments of assignmentsBySource.values()) {
      game.addEnforcedAtMostN(assignments, 1, sourceCapacityActive);
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
  return { beforeInfoDeathsByTiming };
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
  return {
    id: `${timing}_demon_kill`,
    available: livingDemonPathBeforeDeathEvent(game, doc, event),
    starpassesImp: true,
    deathTiming: "beforeInfo",
    constrainAssignment: (player, assignment) => {
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

function gossipDeathSources(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  ctx: Omit<CompileCtx, "nameRoot">,
): readonly NightDeathSource[] {
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
          available: game.allOf(
            [
              game.hasRoleAt(claim.name, "Gossip", statementTiming),
              game.soberAndHealthy(claim.name, statementTiming),
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

function livingPlayersAfterTimeline(doc: PuzzleDoc): readonly string[] {
  const deadPlayers = new Set<string>();
  for (const event of doc.timeline ?? []) {
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
    return claim;
  }
  const player = claim.name;
  const timing = claim.timing as Timing;
  const neighborOptions = livingNeighborOptionsAt(game, doc, player, timing, nightDeathTiming);
  if (neighborOptions.length === 1) return { ...claim, neighbors: neighborOptions[0]?.neighbors };
  return { ...claim, neighborOptions };
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

function applyPoisonerSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Poisoner")) return;
  for (const timing of game.poisonTimingKeys) {
    game.addPoisonerEffect(timing as Timing, {
      activeIf: roleAliveAt(game, doc, "Poisoner", timing as Timing),
    });
  }
}

function applyXaanSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Xaan")) return;
  const maxOutsiderCount = doc.script
    .map(resolveRoleRef)
    .filter((role) => roleCharacterType(role) === CharacterType.Outsider).length;
  for (let count = 1; count <= maxOutsiderCount; count += 1) {
    game.addXaanEffect(`night_${count}` as Timing, {
      activeIf: game.outsiderCountIs(count, { name: `xaan_${count}_outsiders` }),
    });
  }
}

function applyWidowSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Widow")) return;
  const timings = [...game.poisonTimingKeys].filter((timing): timing is Timing => timing !== "default");
  game.addWidowEffect({ timings, activeIf: roleAliveAt(game, doc, "Widow", "night_1") });
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

function applyPuzzlemasterSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Puzzlemaster")) return;
  const fixedPuzzlemaster = doc.fixedRoles?.find(
    (fixedRole) => fixedRole.roles.length === 1 && fixedRole.roles[0] === "Puzzlemaster",
  );
  if (fixedPuzzlemaster === undefined) return;
  if (!doc.claims.some((claim) => claim.name === fixedPuzzlemaster.name && claim.type === "Puzzlemaster")) return;

  game.addPuzzlemasterDrunking({ excludedPlayers: [fixedPuzzlemaster.name] });
}

function applyVillageIdiotSources(game: BOTCModel, doc: PuzzleDoc): void {
  if (!doc.script.includes("Village Idiot")) return;
  game.addVillageIdiotDrunking();
}

function roleAliveAt(game: BOTCModel, doc: PuzzleDoc, role: string, timing: Timing): BoolLike {
  const deadPlayers = deadPlayersBefore(doc, timing);
  const candidates = doc.players.filter((player) => !deadPlayers.has(player));
  return game.anyOf(
    candidates.map((player) => game.hasRoleAt(player, role, timing)),
    `${slug(role)}_alive_at_${timing}`,
  );
}

function isMinionAt(game: BOTCModel, doc: PuzzleDoc, player: string, timing: Timing): BoolLike {
  return characterTypeAt(game, doc, player, CharacterType.Minion, timing);
}

function isMinionBeforeEvent(
  game: BOTCModel,
  doc: PuzzleDoc,
  player: string,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  return characterTypeBeforeEvent(game, doc, player, CharacterType.Minion, event);
}

function characterTypeAt(
  game: BOTCModel,
  doc: PuzzleDoc,
  player: string,
  characterType: CharacterType,
  timing: Timing,
): BoolLike {
  const roles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === characterType);
  return game.anyOf(
    roles.map((role) => game.hasRoleAt(player, role, timing)),
    `${timing}_${slug(player)}_${characterType}_at_timing`,
  );
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
