import { applyClaims } from "../model/characters";
import { Alignment, CharacterType, roleAlignment, roleCharacterType } from "../model/core";
import type { BoolLike, BOTCModel, Timing } from "../model/model";
import type { SatBackend } from "../model/sat";
import { buildPuzzleModel, type PuzzleSpec } from "../model/setup";
import type { PuzzleDoc } from "../schema/puzzleDoc";
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
    if (event.type === "doomsayerDeath") continue;
    for (const player of event.players) {
      for (const demonRole of demonRoles) game.fixNotActual(player, demonRole);
    }
  }
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
