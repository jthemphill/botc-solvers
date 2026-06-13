import { describe, expect, test } from "bun:test";
import { validatePuzzleDoc } from "../schema/validate";
import { PUZZLE_EXAMPLES } from "./puzzleCatalog";

describe("puzzle catalog", () => {
  test("loads every dropdown entry as a valid puzzle doc", () => {
    for (const example of PUZZLE_EXAMPLES) {
      expect(() => validatePuzzleDoc(example.data), example.id).not.toThrow();
    }
  });

  test("includes the generated puzzle set without Clockdoku", () => {
    const ids = new Set(PUZZLE_EXAMPLES.map((example) => example.id));

    expect(ids.has("intro")).toBe(true);
    expect(ids.has("puzzle-25-clockdoku")).toBe(false);
    expect(ids.has("puzzle-40-nine-lives")).toBe(true);
    expect(ids.has("puzzle-30-the-babel-fish-is-a-dead-giveaway-left")).toBe(true);
    expect(ids.has("puzzle-30-the-babel-fish-is-a-dead-giveaway-right")).toBe(true);
  });
});
