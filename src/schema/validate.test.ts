import { describe, expect, test } from "bun:test";
import { validatePuzzleDoc } from "./validate";

const baseDoc = {
  version: 1,
  players: ["You"],
  script: ["Savant"],
};

describe("validatePuzzleDoc", () => {
  test("accepts one statement per Savant claim", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      claims: [
        {
          type: "Savant",
          name: "You",
          timing: "day_1",
          statements: [{ options: ["true", "false"] }],
        },
      ],
    });

    expect(doc.claims[0]).toEqual({
      type: "Savant",
      name: "You",
      timing: "day_1",
      statements: [{ options: ["true", "false"] }],
    });
  });

  test("rejects multiple statements in one Savant claim", () => {
    expect(() =>
      validatePuzzleDoc({
        ...baseDoc,
        claims: [
          {
            type: "Savant",
            name: "You",
            timing: "day_1",
            statements: [{ options: ["true", "false"] }, { options: ["true", "false"] }],
          },
        ],
      }),
    ).toThrow("Savant claims must have exactly one statement");
  });
});
