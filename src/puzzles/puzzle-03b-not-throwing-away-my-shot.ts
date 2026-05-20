import { day } from "../model";
import { CharacterType } from "../core";
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
  Saint,
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
  new Chef({ name: "Dan", count: 0 }),
  new Recluse({ name: "Anna" }),
  new Washerwoman({ name: "Matt", role: Librarian, among: ["Tim", "Dan"] }),
  new Empath({ name: "Fraser", count: 0 }),
  new Slayer({
    timing: "day_1",
    name: "You",
  }),
  new Librarian({ name: "Tim", role: Drunk, among: ["You", "Hannah"] }),
  new Investigator({ name: "Sarah", role: ScarletWoman, among: ["Tim", "Fraser"] }),
  new Saint({ name: "Hannah" }),
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
  Saint,
  Chef,
  Empath,
  Investigator,
  Librarian,
  Slayer,
  Washerwoman,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const DAY_1 = day(1);
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.addFalse(game.isEvil("You"));
  game.addPoisonerEffect(DAY_1);
  applyClaims(game, PLAYERS, { timing: "day_1" });
  game.addTruth(game.actualIs("You", Slayer));
  game.addFalse(game.poisoned("You", DAY_1));
  const annaImpWithScarletWoman = game.allOf(
    [game.actualIs("Anna", Imp), game.roleInPlay(ScarletWoman)],
    "anna_imp_with_scarlet_woman",
  );
  const annaRecluseRegistersAsImp = game.allOf(
    [game.actualIs("Anna", Recluse), game.registersAsRole("Anna", Imp, "you_slayer")],
    "anna_recluse_registers_as_imp",
  );
  game.addTruth(
    game.anyOf([annaRecluseRegistersAsImp, annaImpWithScarletWoman], "slayer_shot_anna_died_without_game_ending"),
  );
  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-03b-not-throwing-away-my-shot.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: DAY_1,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk, { missing: "not in play" }),
      forcedRole("Recluse", Recluse, { missing: "not in play" }),
    ],
  });
