import { night } from "../model";
import { forcedRole, printSolution } from "../display";
import type { BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import { Drunk, Imp, Poisoner, Seamstress, applyClaims, playerNames, script } from "../characters";

export const NIGHT_1 = night(1);

export const PLAYERS = [
  new Seamstress({ name: "Anna", aligned: false, among: ["Josh", "Matthew"], timing: "night_1" }),
  new Seamstress({ name: "Tim", aligned: false, among: ["You", "Josh"], timing: "night_1" }),
  new Seamstress({
    name: "Matthew",
    aligned: false,
    among: ["Steph", "Fraser"],
    timing: "night_1",
  }),
  new Seamstress({ name: "Fraser", aligned: false, among: ["Steph", "Anna"], timing: "night_1" }),
  new Seamstress({ name: "You", aligned: false, among: ["Anna", "Matthew"], timing: "night_1" }),
  new Seamstress({ name: "Josh", aligned: false, among: ["Anna", "Tim"], timing: "night_1" }),
  new Seamstress({ name: "Steph", aligned: false, among: ["Tim", "Matthew"], timing: "night_1" }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(Imp, Poisoner, Drunk, Seamstress);
export const PUZZLE = {
  players: PLAYER_NAMES,
  characters: CHARACTERS,
  uniqueCharacters: false,
} satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.addPoisonerEffect(NIGHT_1);
  applyClaims(game, PLAYERS);
  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-08-the-stitch-up.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: "night_1",
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", Poisoner, { includeRole: true }),
    ],
  });
