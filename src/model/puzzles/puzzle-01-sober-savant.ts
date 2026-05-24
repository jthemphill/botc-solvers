import type { BOTCModel } from "../model";
import { printSolution } from "../display";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Chef,
  Drunk,
  Imp,
  Investigator,
  Knight,
  Noble,
  Savant,
  ScarletWoman,
  Seamstress,
  Steward,
  applyClaims,
  playerNames,
  script,
} from "../characters";
import { drunkBetweenTwoTownsfolk } from "../predicates";

export const PLAYERS = [
  new Investigator({ name: "Oscar", minionRole: ScarletWoman, among: ["Anna", "Sula"] }),
  new Noble({ name: "Matt", oneEvilAmong: ["Tim", "Oscar", "Sula"] }),
  new Seamstress({
    timing: "night_1",
    name: "Anna",
    aligned: false,
    among: ["Oscar", "Sula"],
  }),
  new Savant({
    timing: "day_1",
    name: "You",
    statements: [
      (game) => [game.roleInPlay(Investigator), game.sitsNextToEvil("You")],
      (game) => [Chef.learnsCount(game, 1, "you_savant_chef", { registers: false }), drunkBetweenTwoTownsfolk(game)],
      (game) => [
        game.anyOf([game.isMinion("Tim"), game.isMinion("Sula")], "tim_or_sula_minion"),
        game.not(game.roleInPlay(Noble), "noble_not_in_play"),
      ],
    ],
  }),
  new Knight({ name: "Tim", noDemonAmong: ["Anna", "Sula"] }),
  new Steward({ name: "Sula", goodPlayer: "Matt" }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(Imp, ScarletWoman, Drunk, Investigator, Knight, Noble, Savant, Seamstress, Steward);
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixActual("You", Savant);
  applyClaims(game, PLAYERS);
  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-01-sober-savant.ts"))
  printSolution(await solve(), PLAYER_NAMES, { forcedRoles: [Imp, ScarletWoman, Drunk] });
