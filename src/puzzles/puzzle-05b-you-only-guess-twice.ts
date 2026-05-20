import { forcedRole, printSolution } from "../display";
import { type BOTCModel, type World } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Drunk,
  Empath,
  Goblin,
  Investigator,
  Juggler,
  Knight,
  Leviathan,
  Noble,
  Seamstress,
  Steward,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export interface JuggleGuess {
  readonly player: string;
  readonly role: string;
}

export interface JugglePlan {
  readonly guesses: readonly JuggleGuess[];
  readonly outcomes: ReadonlyMap<number, { readonly demon: string; readonly minion: string }>;
}

export const PLAYERS = [
  new Steward({ name: "Matthew", goodPlayer: "You" }),
  new Investigator({ name: "Steph", role: Goblin, among: ["Sarah", "Fraser"] }),
  new Noble({ name: "Aoife", oneEvilAmong: ["Sarah", "Tim", "Matthew"] }),
  new Knight({ name: "Fraser", noDemonAmong: ["You", "Steph"] }),
  new Juggler({ name: "You" }),
  new Empath({ name: "Sarah", count: 0 }),
  new Seamstress({ name: "Tim", aligned: true, among: ["You", "Fraser"] }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Leviathan,
  Goblin,
  Drunk,
  Empath,
  Investigator,
  Juggler,
  Knight,
  Noble,
  Seamstress,
  Steward,
);
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixActual("You", Juggler);
  applyClaims(game, PLAYERS);
  return game;
}

export function possibleJuggles(
  worlds: readonly World[],
  options: { readonly guessCount?: number; readonly limit?: number } = {},
): JugglePlan[] {
  const guessCount = options.guessCount ?? 3;
  const candidateGuesses = PLAYER_NAMES.flatMap((player) =>
    roleNames(CHARACTERS)
      .filter((role) => role !== "Drunk")
      .map((role) => ({ player, role })),
  );
  const plans: JugglePlan[] = [];
  for (const guesses of combinations(candidateGuesses, guessCount)) {
    const outcomes = new Map<number, { readonly demon: string; readonly minion: string }>();
    let discriminates = true;
    for (const world of worlds) {
      const count = guesses.filter((guess) => world.actualRole(guess.player) === guess.role).length;
      const demon = world.holder(Leviathan);
      const minion = world.holder(Goblin);
      if (demon === undefined || minion === undefined) {
        discriminates = false;
        break;
      }
      const existing = outcomes.get(count);
      if (existing !== undefined && (existing.demon !== demon || existing.minion !== minion)) {
        discriminates = false;
        break;
      }
      outcomes.set(count, { demon, minion });
    }
    if (discriminates && outcomes.size === worlds.length) plans.push({ guesses, outcomes });
    if (options.limit !== undefined && plans.length >= options.limit) break;
  }
  return plans;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function combinations<T>(items: readonly T[], size: number): T[][] {
  if (size === 0) return [[]];
  if (items.length < size) return [];
  return items.flatMap((item, index) =>
    combinations(items.slice(index + 1), size - 1).map((suffix) => [item, ...suffix]),
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-05b-you-only-guess-twice.ts")) {
  const worlds = await solve();
  printSolution(worlds, PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Leviathan, { includeRole: true }),
      forcedRole("Minion", Goblin, { includeRole: true }),
    ],
  });
  const [juggle] = possibleJuggles(worlds, { limit: 1 });
  if (juggle !== undefined) {
    console.log("");
    console.log("Juggle");
    for (const guess of juggle.guesses) console.log(`  ${guess.player} = ${guess.role}`);
    console.log("Outcomes");
    for (const [count, outcome] of [...juggle.outcomes.entries()].sort(([left], [right]) => left - right)) {
      console.log(`  ${count}: Leviathan=${outcome.demon}, Goblin=${outcome.minion}`);
    }
  }
}
