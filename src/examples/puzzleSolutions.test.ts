import { beforeAll, describe, expect, test } from "bun:test";
import { buildFromDoc } from "../builders/buildFromDoc";
import { KissatBackend, type SatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";
import { PUZZLE_EXAMPLES } from "./puzzleCatalog";

const UNIQUE_JSON_PUZZLES = new Set([
  "puzzle-01-sober-savant",
  "puzzle-02-come-fly-with-me",
  "puzzle-34-the-vortox-conjecture",
]);

const INTENTIONALLY_NON_UNIQUE_SOLUTION_COUNTS: Readonly<Record<string, number>> = {
  "puzzle-05a-you-only-guess-twice": 2,
  "puzzle-05b-you-only-guess-twice": 4,
};

// These still need their old TypeScript-only constraints moved into JSON puzzle language.
const KNOWN_INCOMPLETE_JSON_SOLUTION_COUNTS: Readonly<Record<string, number>> = {
  "puzzle-03a-not-throwing-away-my-shot": 3,
  "puzzle-03b-not-throwing-away-my-shot": 6,
  "puzzle-04-the-many-headed-monster": 0,
  "puzzle-06-super-marionette-bros": 43,
  "puzzle-07-the-savant-strikes-back": 22,
  "puzzle-08-the-stitch-up": 0,
  "puzzle-09-the-new-acrobat": 88,
  "puzzle-10-dont-overcook-it": 19,
  "puzzle-11-false-is-the-new-black": 16,
  "puzzle-12a-thunderstruck": 0,
  "puzzle-12b-thunderstruck": 0,
  "puzzle-13-clockblocking": 43,
  "puzzle-14-new-super-marionette-bros": 9,
  "puzzle-15-wake-up-and-choose-violets": 36,
  "puzzle-16-who-watches-the-watchmen": 14,
  "puzzle-17-the-missing-piece": 9,
  "puzzle-18-x-and-the-city": 136,
  "puzzle-19-he-could-be-you-he-could-be-me": 85,
  "puzzle-20-the-three-wise-men": 48,
  "puzzle-21-eight-jugglers-juggling": 0,
  "puzzle-22-one-in-the-chamber": 40,
  "puzzle-23-goblincore": 0,
  "puzzle-24-the-ultimate-blunder": 10,
  "puzzle-26-a-major-problem": 32,
  "puzzle-27-is-this-a-legion-game": 0,
  "puzzle-28-a-study-in-scarlet": 244,
  "puzzle-29-a-dreamer-im-not-the-only-one": 0,
  "puzzle-30-the-babel-fish-is-a-dead-giveaway-left": 120,
  "puzzle-30-the-babel-fish-is-a-dead-giveaway-right": 120,
  "puzzle-31-no-your-other-left": 61,
  "puzzle-32-prepare-for-juggle-and-make-it-double": 27,
  "puzzle-33-twice-is-coincidence-thrice-is-proof": 29,
  "puzzle-35-typhon-season": 504,
  "puzzle-36-what-is-your-weapon-of-choice": 32,
  "puzzle-37-new-super-marionette-bros-u": 136,
  "puzzle-38-snakes-on-a-plane": 48,
  "puzzle-39-squid-game": 17,
  "puzzle-40-nine-lives": 94,
};

function expectedSolutionCount(id: string): number | undefined {
  if (UNIQUE_JSON_PUZZLES.has(id)) return 1;
  return INTENTIONALLY_NON_UNIQUE_SOLUTION_COUNTS[id] ?? KNOWN_INCOMPLETE_JSON_SOLUTION_COUNTS[id];
}

describe("JSON puzzle solutions", () => {
  let backend: SatBackend;

  beforeAll(async () => {
    backend = await KissatBackend.create();
  });

  test("every numbered JSON puzzle has a documented solution-count expectation", () => {
    const catalogIds = PUZZLE_EXAMPLES.map((example) => example.id).filter((id) => id !== "intro");
    expect(new Set(catalogIds)).toEqual(
      new Set([
        ...UNIQUE_JSON_PUZZLES,
        ...Object.keys(INTENTIONALLY_NON_UNIQUE_SOLUTION_COUNTS),
        ...Object.keys(KNOWN_INCOMPLETE_JSON_SOLUTION_COUNTS),
      ]),
    );
  });

  test("numbered JSON puzzle solution counts come from JSON docs", async () => {
    for (const example of PUZZLE_EXAMPLES) {
      if (example.id === "intro") continue;
      const expectedCount = expectedSolutionCount(example.id);
      if (expectedCount === undefined) throw new Error(`Missing expected solution count for ${example.id}.`);

      const doc = validatePuzzleDoc(example.data);
      const worlds = await buildFromDoc(doc, backend).solveAll();

      expect(worlds, example.id).toHaveLength(expectedCount);
    }
  }, 60_000);
});
