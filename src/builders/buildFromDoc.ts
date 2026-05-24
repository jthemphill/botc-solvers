import { applyClaims } from "../model/characters";
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
    seating: doc.seating ?? doc.players,
    uniqueCharacters: doc.uniqueCharacters,
    setup: doc.setup === "none" ? false : "standard",
  };
  const game = buildPuzzleModel(spec, backend);
  for (const fixedRole of doc.fixedRoles ?? []) {
    if (fixedRole.name && fixedRole.roles.length > 0) {
      game.setPossibleActualRoles(fixedRole.name, fixedRole.roles.map(resolveRoleRef));
    }
  }
  const ctx = { players: doc.players, script: doc.script };
  applyClaims(
    game,
    doc.claims.map((c) => buildClaim(c, ctx)),
  );
  return game;
}
