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

  test("rejects Knight claims with more than two players", () => {
    expect(() =>
      validatePuzzleDoc({
        ...baseDoc,
        players: ["You", "A", "B"],
        script: ["Knight"],
        claims: [{ type: "Knight", name: "You", noDemonAmong: ["You", "A", "B"] }],
      }),
    ).toThrow("Knight 'noDemonAmong' must have at most 2 players");
  });

  test("drops legacy Investigator registration overrides", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      players: ["You", "A"],
      script: ["Investigator"],
      claims: [{ type: "Investigator", name: "You", among: ["A"], registers: false }],
    });

    expect(doc.claims[0]).toEqual({ type: "Investigator", name: "You", among: ["A"] });
  });

  test("accepts custom info statements and forbidden roles", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      players: ["You", "A"],
      script: ["Savant", "Imp"],
      forbiddenRoles: [{ name: "You", roles: ["Imp"] }],
      claims: [
        {
          type: "Savant",
          name: "You",
          info: [
            {
              timing: "night_1",
              text: "A is the Imp",
              expression: "A.role == Imp",
              vortoxAffected: true,
            },
          ],
          statements: [{ options: ["true", "false"] }],
        },
      ],
    });

    expect(doc.forbiddenRoles).toEqual([{ name: "You", roles: ["Imp"] }]);
    expect(doc.claims[0]?.info).toEqual([
      {
        timing: "night_1",
        text: "A is the Imp",
        expression: "A.role == Imp",
        vortoxAffected: true,
      },
    ]);
  });
});
