import { describe, expect, test } from "bun:test";
import { validatePuzzleDoc } from "../schema/validate";
import { PUZZLE_EXAMPLES } from "./puzzleCatalog";

describe("puzzle catalog", () => {
  test("loads every dropdown entry as a valid puzzle doc", () => {
    for (const example of PUZZLE_EXAMPLES) {
      expect(() => validatePuzzleDoc(example.data), example.id).not.toThrow();
    }
  });

  test("includes the JSON puzzle set without Clockdoku", () => {
    const ids = new Set(PUZZLE_EXAMPLES.map((example) => example.id));

    expect(ids.has("intro")).toBe(true);
    expect(ids.has("puzzle-25-clockdoku")).toBe(false);
    expect(ids.has("puzzle-40-nine-lives")).toBe(true);
    expect(ids.has("puzzle-30-the-babel-fish-is-a-dead-giveaway-left")).toBe(true);
    expect(ids.has("puzzle-30-the-babel-fish-is-a-dead-giveaway-right")).toBe(true);
  });

  test("uses structured info for puzzle 34", () => {
    const puzzle34 = PUZZLE_EXAMPLES.find((example) => example.id === "puzzle-34-the-vortox-conjecture");
    const doc = validatePuzzleDoc(puzzle34?.data);
    const clockmaker = doc.claims.find((claim) => claim.type === "Clockmaker");
    const mathematician = doc.claims.find((claim) => claim.type === "Mathematician");

    expect(clockmaker).toMatchObject({ type: "Clockmaker", distance: 3 });
    expect(mathematician).toMatchObject({
      type: "Mathematician",
      malfunctions: [
        { timing: "night_1", count: 1 },
        { timing: "night_2", count: 0 },
      ],
    });
    expect(doc.claims.flatMap((claim) => claim.info ?? []).map((info) => "text" in info)).not.toContain(true);
    expect(doc.timeline).toEqual([
      { timing: "day_1", type: "nominationDeath", players: ["Steph"] },
      { timing: "day_1", type: "execution", players: ["Aoife"] },
      { timing: "night_2", type: "nightKill", players: ["Fraser"] },
    ]);
  });
});
