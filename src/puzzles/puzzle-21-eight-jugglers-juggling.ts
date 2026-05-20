import { forcedRole, printSolution } from "../display";
import type { BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import { Drunk, Goblin, Juggler, Leviathan, applyClaims, playerNames, script } from "../characters";

export const PLAYERS = [
  new Juggler({
    timing: "night_2",
    name: "Tim",
    guesses: { You: Leviathan, Josh: Juggler },
    correctCount: 0,
  }),
  new Juggler({
    timing: "night_2",
    name: "Matt",
    guesses: { Josh: Goblin, Tim: Juggler },
    correctCount: 0,
  }),
  new Juggler({
    timing: "night_2",
    name: "Olivia",
    guesses: { You: Juggler, Aoife: Drunk },
    correctCount: 2,
  }),
  new Juggler({
    timing: "night_2",
    name: "Oscar",
    guesses: { Josh: Goblin, Matt: Juggler },
    correctCount: 0,
  }),
  new Juggler({
    timing: "night_2",
    name: "You",
    guesses: { Matt: Goblin, Oscar: Goblin },
    correctCount: 0,
  }),
  new Juggler({
    timing: "night_2",
    name: "Fraser",
    guesses: { Olivia: Juggler, Oscar: Drunk },
    correctCount: 1,
  }),
  new Juggler({
    timing: "night_2",
    name: "Aoife",
    guesses: { Olivia: Leviathan, Oscar: Leviathan },
    correctCount: 0,
  }),
  new Juggler({
    timing: "night_2",
    name: "Josh",
    guesses: { Tim: Goblin, Oscar: Juggler },
    correctCount: 1,
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(Leviathan, Goblin, Drunk, Juggler);
export const PUZZLE = {
  players: PLAYER_NAMES,
  characters: CHARACTERS,
  seating: PLAYER_NAMES,
  uniqueCharacters: false,
} satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);

  applyClaims(game, PLAYERS);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-21-eight-jugglers-juggling.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Leviathan, { includeRole: true }),
      forcedRole("Minion", Goblin, { includeRole: true }),
      forcedRole("Outsider", Drunk, { includeRole: true }),
    ],
  });
