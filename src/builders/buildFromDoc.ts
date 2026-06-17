import { applyClaims } from "../model/characters";
import { Alignment, CharacterType, roleAlignment, roleCharacterType, roleName } from "../model/core";
import type { BoolLike, BOTCModel, Timing } from "../model/model";
import type { SatBackend } from "../model/sat";
import { buildPuzzleModel, type PuzzleSpec } from "../model/setup";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { compile, type CompileCtx } from "../dsl/compile";
import { buildClaim } from "./claim";
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
  const claims = doc.claims.map((claim) => applyTimelineClaimContext(claim, doc));
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
    applyPuzzlemasterSources(game, doc);
    applyVillageIdiotSources(game, doc);
    applyNightDeathSourceConstraints(game, doc, ctx);
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
  const hasSoldier = doc.script.includes("Soldier");
  for (const event of deathEvents) {
    if (event.type === "doomsayerDeath" && event.caller !== undefined) {
      for (const player of event.players) {
        game.addTruth(doomsayerSameRegisteredAlignment(game, event.caller, player));
      }
    }
    if (event.type === "abilityDeath" || event.type === "nightDeath") {
      for (const player of event.players) {
        for (const demonRole of demonRoles) {
          game.addImplication(
            game.actualIs(player, demonRole),
            roleName(demonRole) === "Imp"
              ? livingMinionCanCatchAbilityDeath(game, doc, event)
              : livingScarletWomanCanCatchAbilityDeath(game, doc, event),
          );
        }
      }
      continue;
    }
    if (event.type === "doomsayerDeath") continue;
    for (const player of event.players) {
      if (hasSoldier && (event.type === "nightKill" || event.type === "nightKillBeforeInfo")) {
        game.addFalse(
          game.allOf(
            [
              game.hasRoleAt(player, "Soldier", event.timing as Timing),
              game.soberAndHealthy(player, event.timing as Timing),
            ],
            `${player}_${event.timing}_sober_healthy_soldier_night_killed`,
          ),
        );
      }
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

function livingMinionCanCatchAbilityDeath(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  return game.anyOf(
    candidates.map((player) => game.isMinion(player)),
    `${event.timing}_minion_can_catch_imp_death`,
  );
}

function livingScarletWomanCanCatchAbilityDeath(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
): BoolLike {
  if (!doc.script.includes("Scarlet Woman")) return game.constantBool(false, "no_scarlet_woman_to_catch_demon");
  const candidates = livingPlayersAfterDeathEvent(doc, event);
  return game.anyOf(
    candidates.map((player) => game.actualIs(player, "Scarlet Woman")),
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
}

function applyNightDeathSourceConstraints(game: BOTCModel, doc: PuzzleDoc, ctx: Omit<CompileCtx, "nameRoot">): void {
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
}

function nightDeathSources(
  game: BOTCModel,
  doc: PuzzleDoc,
  event: NonNullable<PuzzleDoc["timeline"]>[number],
  ctx: Omit<CompileCtx, "nameRoot">,
): readonly NightDeathSource[] {
  const timing = event.timing as Timing;
  return [
    {
      id: `${timing}_demon_kill`,
      available: livingDemonPathBeforeDeathEvent(game, doc, event),
    },
    ...gossipDeathSources(game, doc, event, ctx),
    ...acrobatDeathSources(game, doc, timing),
    ...gamblerDeathSources(game, doc, timing),
  ];
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
  const livingStartingDemon = livingPlayers.flatMap((player) => demonRoles.map((role) => game.actualIs(player, role)));
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
            livingPlayers.map((player) => game.isMinion(player)),
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
            livingPlayers.map((player) => game.actualIs(player, "Scarlet Woman")),
            `${event.timing}_living_scarlet_woman_before_death_event`,
          ),
        ],
        `${event.timing}_scarlet_woman_successor_alive_before_death_event`,
      ),
    );
  }

  return game.anyOf(
    [...livingStartingDemon, ...possibleSuccessions],
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

function applyTimelineClaimContext(claim: PuzzleDoc["claims"][number], doc: PuzzleDoc): PuzzleDoc["claims"][number] {
  if (claim.type === "Legionary" && claim.counts !== undefined) {
    return {
      ...claim,
      counts: claim.counts.map((count, index) => {
        const timing = (count.timing ?? `night_${index + 1}`) as Timing;
        return { ...count, timing, alivePlayers: livingPlayersAt(doc, timing) };
      }),
    };
  }
  if (
    claim.type !== "Empath" ||
    claim.count === undefined ||
    claim.neighbors !== undefined ||
    claim.timing === undefined
  ) {
    return claim;
  }
  return { ...claim, neighbors: livingNeighborsAt(doc, claim.player ?? claim.name, claim.timing as Timing) };
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
    candidates.map((player) => game.actualIs(player, role)),
    `${slug(role)}_alive_at_${timing}`,
  );
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
  if (event.type === "nightKillBeforeInfo") return phaseStartOrder(event.timing as Timing) - 0.5;
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
