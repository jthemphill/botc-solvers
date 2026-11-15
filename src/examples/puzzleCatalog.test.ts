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

  test("uses arbitrary expressions only for Gossip, Savant, and Artist", () => {
    for (const example of PUZZLE_EXAMPLES) {
      const doc = validatePuzzleDoc(example.data);

      for (const claim of doc.claims) {
        const infoExpressions = (claim.info ?? []).filter((info) => info.expression?.trim());
        if (claim.type === "Artist") {
          continue;
        }

        expect(infoExpressions, `${example.id}: ${claim.name} ${claim.type}`).toHaveLength(0);
      }
    }
  });

  test("reserves custom constraints for rules specified by the source image", () => {
    const expected = new Set([
      "puzzle-56-meanwhile-at-the-legion-of-doom", // The setup includes standard games and Legion games.
      "puzzle-62-have-you-ever-seen-the-rain", // The Storm Catcher lets the Drunk die only by execution.
      "puzzle-64-copycatholic", // With the Pope, the setup must have a duplicate good character.
      "puzzle-72-one-digit-too-many", // The setup includes standard games and Legion games.
      "puzzle-76-three-for-three", // This puzzle uses a custom setup with three roles.
    ]);
    const actual = new Set(
      PUZZLE_EXAMPLES.filter((example) => (validatePuzzleDoc(example.data).constraints?.length ?? 0) > 0).map(
        (example) => example.id,
      ),
    );

    expect(actual).toEqual(expected);
  });

  test("uses standard setup modifiers for source-specified character counts", () => {
    for (const id of ["puzzle-51-weird-science", "puzzle-84-mech4an4ion-is-inver10d", "puzzle-86-blood-and-ink"]) {
      const example = PUZZLE_EXAMPLES.find((candidate) => candidate.id === id);
      const doc = validatePuzzleDoc(example?.data);

      expect(doc.setup, id).toBeUndefined();
      expect(doc.constraints, id).toBeUndefined();
    }
  });

  test("uses timed claims for puzzle 77's Recluse starpass claim", () => {
    const puzzle77 = PUZZLE_EXAMPLES.find((example) => example.id === "puzzle-77-yes-but-dont");
    const doc = validatePuzzleDoc(puzzle77?.data);
    const matt = doc.claims.filter((claim) => claim.name === "Matt");

    expect(matt).toEqual([
      { type: "Recluse", name: "Matt", timing: "night_1" },
      { type: "Imp", name: "Matt", timing: "night_4", roleTiming: "night_4", alignment: "good" },
    ]);
    expect(doc.constraints).toBeUndefined();
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
      { timing: "day_1", type: "witchCurse", players: ["Steph"] },
      { timing: "day_1", type: "execution", players: ["Aoife"] },
      { timing: "night_2", type: "nightDeath", players: ["Fraser"] },
    ]);
  });

  test("uses specific Witch curse and Slayer shot timeline deaths", () => {
    const examples = new Map(PUZZLE_EXAMPLES.map((example) => [example.id, validatePuzzleDoc(example.data)]));

    expect(examples.get("puzzle-03a-not-throwing-away-my-shot")?.timeline?.[0]).toMatchObject({
      type: "slayerShot",
      players: ["Tom"],
    });
    expect(examples.get("puzzle-03b-not-throwing-away-my-shot")?.timeline?.[0]).toMatchObject({
      type: "slayerShot",
      players: ["Anna"],
    });
    expect(examples.get("puzzle-19-he-could-be-you-he-could-be-me")?.timeline?.[2]).toMatchObject({
      type: "slayerShot",
      players: ["Oscar"],
    });
    expect(examples.get("puzzle-34-the-vortox-conjecture")?.timeline?.[0]).toMatchObject({
      type: "witchCurse",
      players: ["Steph"],
    });
    expect(examples.get("puzzle-39-squid-game")?.timeline?.[0]).toMatchObject({
      type: "witchCurse",
      players: ["Tom"],
    });
  });
});
