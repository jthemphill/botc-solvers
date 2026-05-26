import { day } from "../model";
import { Alignment, CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import type { BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Baron,
  Chef,
  Drunk,
  Empath,
  Imp,
  Investigator,
  Librarian,
  Poisoner,
  Recluse,
  ScarletWoman,
  Slayer,
  Spy,
  Washerwoman,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const PLAYERS = [
  new Investigator({ name: "Sula", role: Baron, among: ["You", "Aoife"] }),
  new Washerwoman({ name: "Matthew", role: Librarian, among: ["Aoife", "Oscar"] }),
  new Librarian({ name: "Oscar", outsiderCount: 0 }),
  new Empath({ name: "Josh", count: 0 }),
  new Slayer({
    timing: "day_1",
    name: "You",
  }),
  new Chef({ name: "Aoife", count: 0 }),
  new Recluse({ name: "Tom" }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Baron,
  Spy,
  Poisoner,
  ScarletWoman,
  Drunk,
  Recluse,
  Chef,
  Empath,
  Investigator,
  Librarian,
  Slayer,
  Washerwoman,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const DAY_1 = day(1);
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.addFalse(game.isEvil("You"));
  game.addPoisonerEffect(DAY_1);
  applyClaims(game, PLAYERS, { timing: "day_1" });
  game.addTruth(game.actualIs("You", Slayer));
  game.addFalse(game.poisoned("You", DAY_1));
  const tomImpWithScarletWoman = game.allOf(
    [game.actualIs("Tom", Imp), game.roleInPlay(ScarletWoman)],
    "tom_imp_with_scarlet_woman",
  );
  const tomRecluseRegistersAsImp = game.allOf(
    [game.actualIs("Tom", Recluse), game.registersAsRole("Tom", Imp, "you_slayer")],
    "tom_recluse_registers_as_imp",
  );
  game.addTruth(
    game.anyOf([tomRecluseRegistersAsImp, tomImpWithScarletWoman], "slayer_shot_tom_died_without_game_ending"),
  );
  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-03a-not-throwing-away-my-shot.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: DAY_1,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk, { missing: "not in play" }),
      forcedRole("Recluse", Recluse, { missing: "not in play" }),
    ],
  });
