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
              role: "Artist",
              expression: "A.role == Imp",
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
        role: "Artist",
        expression: "A.role == Imp",
      },
    ]);
  });

  test("accepts timeline events", () => {
    const doc = validatePuzzleDoc({
      ...baseDoc,
      players: ["You", "A"],
      script: ["Savant", "Imp"],
      timeline: [
        { timing: "day_1", type: "nominationDeath", players: ["You"] },
        { timing: "day_1", type: "execution", players: ["A"] },
        { timing: "day_1", type: "doomsayerDeath", players: ["A"], caller: "You" },
        { timing: "night_2", type: "nightDeath", players: ["You"] },
        { timing: "night_2", type: "nightKill", players: ["A"] },
        { timing: "night_2", type: "nightKillBeforeInfo", players: ["You"] },
        { timing: "night_2", type: "abilityDeath", players: ["You"] },
      ],
      claims: [{ type: "Savant", name: "You", statements: [{ options: ["true", "false"] }] }],
    });

    expect(doc.timeline).toEqual([
      { timing: "day_1", type: "nominationDeath", players: ["You"] },
      { timing: "day_1", type: "execution", players: ["A"] },
      { timing: "day_1", type: "doomsayerDeath", players: ["A"], caller: "You" },
      { timing: "night_2", type: "nightDeath", players: ["You"] },
      { timing: "night_2", type: "nightKill", players: ["A"] },
      { timing: "night_2", type: "nightKillBeforeInfo", players: ["You"] },
      { timing: "night_2", type: "abilityDeath", players: ["You"] },
    ]);
  });

  test("rejects unknown timeline event types", () => {
    expect(() =>
      validatePuzzleDoc({
        ...baseDoc,
        timeline: [{ timing: "day_1", type: "death", players: ["You"] }],
        claims: [],
      }),
    ).toThrow(
      'Timeline event type must be "nominationDeath", "execution", "nightDeath", "nightKill", "nightKillBeforeInfo", "abilityDeath", or "doomsayerDeath"',
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
        { type: "Klutz", name: "You", timing: "night_2", chosen: "A", lost: false },
        { type: "Mathematician", name: "You", malfunctions: [{ timing: "night_1", count: 1 }] },
        { type: "Oracle", name: "You", timing: "night_2", count: 1, deadPlayers: ["A", "B"] },
        { type: "Sage", name: "You", demonAmong: ["A", "B"] },
        { type: "Snake Charmer", name: "You", checked: "A", demon: false },
      ],
    });

    expect(doc.claims).toEqual([
      { type: "Chambermaid", name: "You", checks: [{ left: "A", right: "B", timing: "night_1", count: 1 }] },
      { type: "Clockmaker", name: "You", distance: 3 },
      { type: "Courtier", name: "You", timing: "night_1", role: "Vortox", drunkTimings: ["night_1"] },
      { type: "Klutz", name: "You", timing: "night_2", chosen: "A", lost: false },
      { type: "Mathematician", name: "You", malfunctions: [{ timing: "night_1", count: 1 }] },
      { type: "Oracle", name: "You", timing: "night_2", count: 1, deadPlayers: ["A", "B"] },
      { type: "Sage", name: "You", demonAmong: ["A", "B"] },
      { type: "Snake Charmer", name: "You", checked: "A", demon: false },
    ]);
  });
});
