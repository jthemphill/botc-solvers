import { forcedRole, printSolution } from "../display";
import { type BOTCModel, type World } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Alsaahir,
  Drunk,
  Empath,
  Goblin,
  Investigator,
  Knight,
  Leviathan,
  Noble,
  Seamstress,
  Steward,
  applyClaims,
  playerNames,
  script,
} from "../characters";

export interface AlsaahirGuess {
  readonly demon: string;
  readonly minion: string;
  readonly ifWrongDemon: string;
  readonly ifWrongMinion: string;
}

export const PLAYERS = [
  new Investigator({ name: "Matt", role: Goblin, among: ["Anna", "Oscar"] }),
  new Empath({ name: "Anna", count: 1 }),
  new Steward({ name: "Hannah", goodPlayer: "Tom" }),
  new Seamstress({
    name: "Oscar",
    timing: "night_1",
    aligned: false,
    among: ["Tom", "Hannah"],
  }),
  new Alsaahir({ name: "You" }),
  new Noble({ name: "Dan", oneEvilAmong: ["Tom", "Anna", "Hannah"] }),
  new Knight({ name: "Tom", noDemonAmong: ["Anna", "Dan"] }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Leviathan,
  Goblin,
  Drunk,
  Alsaahir,
  Empath,
  Investigator,
  Knight,
  Noble,
  Seamstress,
  Steward,
);
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixActual("You", Alsaahir);
  applyClaims(game, PLAYERS);
  return game;
}

export function possibleAlsaahirGuesses(worlds: readonly World[]): AlsaahirGuess[] {
  return worlds.flatMap((guessedWorld) => {
    const demon = guessedWorld.holder(Leviathan);
    const minion = guessedWorld.holder(Goblin);
    if (demon === undefined || minion === undefined) return [];
    const remainingIfWrong = worlds.filter(
      (world) => world.holder(Leviathan) !== demon || world.holder(Goblin) !== minion,
    );
    if (remainingIfWrong.length !== 1) return [];
    const remaining = remainingIfWrong[0] as World;
    const ifWrongDemon = remaining.holder(Leviathan);
    const ifWrongMinion = remaining.holder(Goblin);
    return ifWrongDemon === undefined || ifWrongMinion === undefined
      ? []
      : [{ demon, minion, ifWrongDemon, ifWrongMinion }];
  });
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-05a-you-only-guess-twice.ts")) {
  const worlds = await solve();
  printSolution(worlds, PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Leviathan, { includeRole: true }),
      forcedRole("Minion", Goblin, { includeRole: true }),
    ],
  });
  const guesses = possibleAlsaahirGuesses(worlds);
  console.log("");
  console.log("Alsaahir guesses");
  for (const guess of guesses)
    console.log(
      `  Guess Leviathan=${guess.demon}, Goblin=${guess.minion}; if wrong, Leviathan=${guess.ifWrongDemon}, Goblin=${guess.ifWrongMinion}`,
    );
}
