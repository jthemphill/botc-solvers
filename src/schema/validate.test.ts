import { describe, expect, test } from "bun:test";
import { validatePuzzleDoc } from "./validate";

const baseDoc = {
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

  test("accepts Artist custom info statements and constraints", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      players: ["You", "A"],
      script: ["Artist", "Imp"],
      constraints: [{ expression: "You.role != Imp" }],
      claims: [
        {
          type: "Artist",
          name: "You",
          info: [
            {
              timing: "night_1",
              role: "Artist",
              expression: "A.role == Imp",
            },
          ],
        },
      ],
    });

    expect(doc.constraints).toEqual([{ expression: "You.role != Imp" }]);
    expect(doc.claims[0]?.info).toEqual([
      {
        timing: "night_1",
        role: "Artist",
        expression: "A.role == Imp",
      },
    ]);
  });

  test("accepts hidden-role knowledge on claims", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      script: ["Chef", "Widow", "Evil Twin"],
      claims: [
        {
          type: "Chef",
          name: "You",
          count: 0,
          possibleActualRoles: ["Chef", "Drunk"],
          heardWidowCall: true,
          knownEvilTwin: "A",
        },
      ],
    });

    expect(doc.claims[0]).toEqual({
      type: "Chef",
      name: "You",
      count: 0,
      possibleActualRoles: ["Chef", "Drunk"],
      heardWidowCall: true,
      knownEvilTwin: "A",
    });
  });

  test("accepts Prodigy checks", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      players: ["You", "A", "B"],
      script: ["Solar Prodigy", "Lunar Prodigy"],
      claims: [{ type: "Prodigy", name: "You", checks: [{ chosen: "A", learned: "B", timing: "night_1" }] }],
    });

    expect(doc.claims[0]).toEqual({
      type: "Prodigy",
      name: "You",
      checks: [{ chosen: "A", learned: "B", timing: "night_1" }],
    });
  });

  test("rejects custom info expressions on non-Artist claims", () => {
    expect(() =>
      validatePuzzleDoc({
        ...baseDoc,
        players: ["You", "A"],
        script: ["Savant", "Imp"],
        claims: [
          {
            type: "Savant",
            name: "You",
            info: [{ timing: "night_1", expression: "A.role == Imp" }],
            statements: [{ options: ["true", "false"] }],
          },
        ],
      }),
    ).toThrow("Only Artist claims may use custom info expressions");
  });

  test("accepts timeline events", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      players: ["You", "A"],
      script: ["Savant", "Imp"],
      timeline: [
        { timing: "day_1", type: "nominationDeath", players: ["You"] },
        { timing: "day_1", type: "witchCurse", players: ["A"] },
        { timing: "day_1", type: "slayerShot", players: ["You"] },
        { timing: "day_1", type: "execution", players: ["A"] },
        { timing: "day_1", type: "doomsayerDeath", players: ["A"], caller: "You" },
        { timing: "night_2", type: "nightDeath", players: ["You"] },
      ],
      claims: [{ type: "Savant", name: "You", statements: [{ options: ["true", "false"] }] }],
    });

    expect(doc.timeline).toEqual([
      { timing: "day_1", type: "nominationDeath", players: ["You"] },
      { timing: "day_1", type: "witchCurse", players: ["A"] },
      { timing: "day_1", type: "slayerShot", players: ["You"] },
      { timing: "day_1", type: "execution", players: ["A"] },
      { timing: "day_1", type: "doomsayerDeath", players: ["A"], caller: "You" },
      { timing: "night_2", type: "nightDeath", players: ["You"] },
    ]);
  });

  test("accepts top-level constraints", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      constraints: [{ expression: "#{p : players | p.role == Imp} == 1" }],
      claims: [],
    });

    expect(doc.constraints).toEqual([{ expression: "#{p : players | p.role == Imp} == 1" }]);
  });

  test("rejects legacy top-level role fields", () => {
    expect(() =>
      validatePuzzleDoc({
        ...baseDoc,
        fixedRoles: [{ name: "You", roles: ["Savant"] }],
        claims: [],
      }),
    ).toThrow("Unsupported legacy field 'fixedRoles'");

    expect(() =>
      validatePuzzleDoc({
        ...baseDoc,
        forbiddenRoles: [{ name: "You", roles: ["Imp"] }],
        claims: [],
      }),
    ).toThrow("Unsupported legacy field 'forbiddenRoles'");
  });

  test("rejects legacy claim role extras", () => {
    expect(() =>
      validatePuzzleDoc({
        ...baseDoc,
        script: ["Savant", "Drunk"],
        claims: [
          {
            type: "Savant",
            name: "You",
            statements: [{ options: ["true", "false"] }],
            extraPossibleActualRoles: ["Drunk"],
          },
        ],
      }),
    ).toThrow("Unsupported legacy field 'extraPossibleActualRoles'");
  });

  test("rejects unknown timeline event types", () => {
    expect(() =>
      validatePuzzleDoc({
        ...baseDoc,
        timeline: [{ timing: "day_1", type: "death", players: ["You"] }],
        claims: [],
      }),
    ).toThrow(
      'Timeline event type must be "nominationDeath", "witchCurse", "slayerShot", "execution", "nightDeath", "doomsayerDeath", "survivedExecution"',
    );
  });

  test("accepts standard role info fields", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      players: ["You", "A", "B"],
      script: ["Chambermaid", "Clockmaker", "Courtier", "Klutz", "Mathematician", "Oracle", "Sage", "Snake Charmer"],
      claims: [
        { type: "Chambermaid", name: "You", checks: [{ left: "A", right: "B", timing: "night_1", count: 1 }] },
        { type: "Clockmaker", name: "You", distance: 3 },
        { type: "Courtier", name: "You", timing: "night_1", role: "Vortox", drunkTimings: ["night_1"] },
        { type: "Klutz", name: "You", timing: "night_2", chosen: "A" },
        { type: "Mathematician", name: "You", malfunctions: [{ timing: "night_1", count: 1 }] },
        { type: "Oracle", name: "You", timing: "night_2", count: 1 },
        { type: "Sage", name: "You", demonAmong: ["A", "B"] },
        { type: "Snake Charmer", name: "You", checks: [{ player: "A", demon: false, timing: "night_1" }] },
      ],
    });

    expect(doc.claims).toEqual([
      { type: "Chambermaid", name: "You", checks: [{ left: "A", right: "B", timing: "night_1", count: 1 }] },
      { type: "Clockmaker", name: "You", distance: 3 },
      { type: "Courtier", name: "You", timing: "night_1", role: "Vortox", drunkTimings: ["night_1"] },
      { type: "Klutz", name: "You", timing: "night_2", chosen: "A" },
      { type: "Mathematician", name: "You", malfunctions: [{ timing: "night_1", count: 1 }] },
      { type: "Oracle", name: "You", timing: "night_2", count: 1 },
      { type: "Sage", name: "You", demonAmong: ["A", "B"] },
      { type: "Snake Charmer", name: "You", checks: [{ player: "A", demon: false, timing: "night_1" }] },
    ]);
  });
});
