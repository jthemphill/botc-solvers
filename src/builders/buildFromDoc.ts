import { applyClaims } from "../model/characters";
import { CharacterType, roleCharacterType } from "../model/core";
import type { BOTCModel } from "../model/model";
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
    setup: doc.setup === "none" ? false : "standard",
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
  applyTimelineConstraints(game, doc);
  const ctx = { players: doc.players, script: doc.script };
  const ordinaryClaims = doc.claims
    .filter((claim) => !usesMalfunctionCount(claim))
    .map((claim) => buildClaim(claim, ctx));
  const malfunctionCountClaims = doc.claims
    .filter((claim) => usesMalfunctionCount(claim))
    .map((claim) => buildClaim(claim, ctx));
  applyClaims(game, ordinaryClaims);
  applyClaims(game, malfunctionCountClaims);
  return game;
}

function applyTimelineConstraints(game: BOTCModel, doc: PuzzleDoc): void {
  const deathEvents = (doc.timeline ?? []).filter((event) => event.type === "execution" || event.type === "nightKill");
  if (deathEvents.length === 0) return;

  const demonRoles = doc.script.map(resolveRoleRef).filter((role) => roleCharacterType(role) === CharacterType.Demon);
  for (const event of deathEvents) {
    for (const player of event.players) {
      for (const demonRole of demonRoles) game.fixNotActual(player, demonRole);
    }
  }
}

function usesMalfunctionCount(claim: PuzzleDoc["claims"][number]): boolean {
  if (claim.type === "Mathematician" && (claim.malfunctions?.length ?? 0) > 0) return true;
  return claim.info?.some((info) => info.expression?.includes("malfunctions(")) ?? false;
}
