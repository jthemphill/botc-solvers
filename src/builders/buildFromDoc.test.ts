import { beforeAll, describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import type { BOTCModel } from "../model/model";
import { KissatBackend, type SatBackend } from "../model/sat";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { validatePuzzleDoc } from "../schema/validate";
import { buildFromDoc as buildPuzzleFromDoc } from "./buildFromDoc";
function loadDoc(name: string) {
  const path = join(import.meta.dir, "..", "examples", name);
  return validatePuzzleDoc(JSON.parse(readFileSync(path, "utf8")));
}

type RoleConstraintFixture = {
  readonly name: string;
  readonly roles: readonly string[];
};

type RoleConstraintsFixture = {
  readonly possible: readonly RoleConstraintFixture[];
  readonly excluded: readonly RoleConstraintFixture[];
};

type TestPuzzleDoc = PuzzleDoc & {
  readonly roleConstraints?: RoleConstraintsFixture;
};

function roleConstraints({
  possible = [],
  excluded = [],
}: {
  readonly possible?: readonly RoleConstraintFixture[];
  readonly excluded?: readonly RoleConstraintFixture[];
}): RoleConstraintsFixture {
  return { possible, excluded };
}

function buildFromDoc(doc: TestPuzzleDoc, backend: SatBackend): BOTCModel {
  const { roleConstraints: roleConstraintFixture, ...puzzleDoc } = doc;
  const game = buildPuzzleFromDoc(puzzleDoc, backend);
  for (const possible of roleConstraintFixture?.possible ?? []) {
    if (possible.name && possible.roles.length > 0) game.setPossibleActualRoles(possible.name, possible.roles);
  }
  for (const excluded of roleConstraintFixture?.excluded ?? []) {
    if (excluded.name) {
      for (const role of excluded.roles) game.fixNotActual(excluded.name, role);
    }
  }
  return game;
}

describe("buildFromDoc", () => {
  let backend: SatBackend;
  beforeAll(async () => {
    backend = await KissatBackend.create();
  });
  test("puzzle-01-sober-savant.json solves to 1 world", async () => {
    const doc = loadDoc("puzzle-01-sober-savant.json");
    const worlds = await buildFromDoc(doc, backend).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Anna");
    expect(worlds[0]?.holder("Scarlet Woman")).toBe("Tim");
    expect(worlds[0]?.holder("Drunk")).toBe("Oscar");
  });
  test("puzzle-05a solves to a unique world", async () => {
    const doc = loadDoc("puzzle-05a-you-only-guess-twice.json");
    const worlds = await buildFromDoc(doc, backend).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
  });
  test("puzzle-05b solves to a non-empty set", async () => {
    const doc = loadDoc("puzzle-05b-you-only-guess-twice.json");
    const worlds = await buildFromDoc(doc, backend).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
  });
  test("puzzle-09 public night deaths require enough hidden death sources", async () => {
    const doc = loadDoc("puzzle-09-the-new-acrobat.json");
    const worlds = await buildFromDoc(doc, backend).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("Anna")).toBe("Imp");
    expect(worlds[0]?.actualRole("Hannah")).toBe("Goblin");
    expect(worlds[0]?.actualRole("Josh")).toBe("Drunk");
  });
  test("juggler count claims default to night 2 when timing is omitted", async () => {
    const doc = loadDoc("puzzle-05b-you-only-guess-twice.json");
    const claims = doc.claims.map((claim) =>
      claim.type === "Juggler" ? { ...claim, timing: undefined, correctCount: 0 } : claim,
    );
    const worlds = await buildFromDoc({ ...doc, claims }, backend).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
  });
  test("intro puzzle parses and solves", async () => {
    const doc = loadDoc("puzzle-intro-chef-empath.json");
    const worlds = await buildFromDoc(doc, backend).solveAll();
    expect(worlds.length).toBeGreaterThanOrEqual(0);
  });
  test("constraints allow multiple possible actual roles", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["You", "A", "B"],
        script: ["Imp", "Marionette", "Drunk", "Investigator"],
        setup: "none",
        roleConstraints: roleConstraints({
          possible: [{ name: "You", roles: ["Drunk", "Investigator"] }],
        }),
        claims: [],
      },
      backend,
    ).solveAll();
    expect(new Set(worlds.map((world) => world.actualRole("You")))).toEqual(new Set(["Drunk", "Investigator"]));
  });
  test("claims can set a possible actual role outside the apparent role", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Lunatic", "Empath", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Lunatic"] },
            { name: "B", roles: ["Empath"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Empath", name: "A", possibleActualRoles: ["Lunatic"], count: 0 }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Lunatic");
  });
  test("claims can set possible actual roles", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["You", "A", "B"],
        script: ["Imp", "Drunk", "Chef", "Soldier"],
        setup: "none",
        claims: [{ type: "Chef", name: "You", possibleActualRoles: ["Chef", "Drunk"], count: 0 }],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(new Set(worlds.map((world) => world.actualRole("You")))).toEqual(new Set(["Chef", "Drunk"]));
  });
  test("Widow in play poisons one player across info timings", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Widow", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Widow"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        claims: [{ type: "Chef", name: "C", count: 0, heardWidowCall: true }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.poisonedByTiming.get("night_1")).toEqual(new Set(["C"]));
  });
  test("heard Widow call claims require Widow in play when the claimant is good", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Widow", "Poisoner", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chef"] },
            { name: "B", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Chef", name: "A", count: 0, heardWidowCall: true }],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(worlds.every((world) => world.holder("Widow") !== undefined)).toBe(true);
  });
  test("Widow in play requires a good player to hear the Widow call", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Widow", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Widow"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        claims: [{ type: "Chef", name: "A", count: 0, heardWidowCall: true }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("evil heard Widow call claims do not force Widow in play", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Widow", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Chef"] },
          ],
        }),
        claims: [{ type: "Chef", name: "A", count: 0, heardWidowCall: true }],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(worlds.some((world) => world.holder("Widow") === undefined)).toBe(true);
  });
  test("Widow and Poisoner on script allow only one active poison source", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Widow", "Poisoner", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Widow"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        claims: [{ type: "Chef", name: "C", count: 0, heardWidowCall: true }],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(worlds.every((world) => world.holder("Poisoner") === undefined)).toBe(true);
    expect(worlds.every((world) => (world.poisonedByTiming.get("night_1")?.size ?? 0) <= 1)).toBe(true);
  });
  test("ordinary poison sources cap the number of poisoned players", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Poisoner", "Imp", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Poisoner"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Empath"] },
          ],
        }),
        claims: [
          { type: "Chef", name: "C", count: 0 },
          { type: "Empath", name: "D", count: 0 },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("heard Widow call claims cannot be true for good players when Widow is off script", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Imp", "Chef"],
        setup: "none",
        roleConstraints: roleConstraints({
          possible: [{ name: "A", roles: ["Chef"] }],
        }),
        claims: [{ type: "Chef", name: "A", count: 0, heardWidowCall: true }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Evil Twin in play requires a good player to declare the Evil Twin", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Evil Twin", "Imp", "Snake Charmer"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Evil Twin"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Snake Charmer"] },
          ],
        }),
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("good Evil Twin declarations identify the actual Evil Twin", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Evil Twin", "Imp", "Snake Charmer"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [{ name: "B", roles: ["Snake Charmer"] }],
        }),
        claims: [{ type: "Snake Charmer", name: "B", checks: [], evilTwin: { player: "A", timing: "night_1" } }],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(worlds.every((world) => world.holder("Evil Twin") === "A")).toBe(true);
  });
  test("wrong good Evil Twin declarations exclude the world", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Evil Twin", "Imp", "Snake Charmer"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Evil Twin"] },
            { name: "B", roles: ["Snake Charmer"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Snake Charmer", name: "B", checks: [], evilTwin: { player: "C", timing: "night_1" } }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("evil Evil Twin declarations do not force Evil Twin in play", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Evil Twin", "Imp", "Snake Charmer", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [{ name: "A", roles: ["Imp"] }],
        }),
        claims: [{ type: "Snake Charmer", name: "A", checks: [], evilTwin: { player: "B", timing: "night_1" } }],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(worlds.every((world) => world.holder("Evil Twin") === undefined)).toBe(true);
  });
  test("custom info statements and excluded role constraints constrain the model", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Sage", "Imp"],
        setup: "none",
        roleConstraints: roleConstraints({
          possible: [{ name: "A", roles: ["Sage"] }],
          excluded: [{ name: "B", roles: ["Sage"] }],
        }),
        claims: [
          {
            type: "Sage",
            name: "A",
            info: [{ timing: "night_1", expression: "B.role == Imp" }],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Sage");
    expect(worlds[0]?.actualRole("B")).toBe("Imp");
  });
  test("later good changed-role claims require Pit-Hag transformation or Cerenovus madness", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Cerenovus", "Pit-Hag", "Seamstress", "Artist", "Clockmaker", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        claims: [
          {
            type: "Seamstress",
            name: "A",
            timing: "night_1",
            among: ["B", "C"],
            aligned: false,
            possibleActualRoles: ["Seamstress"],
          },
          {
            type: "Artist",
            name: "A",
            timing: "day_2",
            info: [{ timing: "day_2", expression: "B.role == Clockmaker" }],
            possibleActualRoles: ["Seamstress"],
          },
          { type: "Clockmaker", name: "B", possibleActualRoles: ["Clockmaker"] },
          { type: "Cerenovus", name: "C", possibleActualRoles: ["Cerenovus", "Pit-Hag"] },
          { type: "Artist", name: "D", possibleActualRoles: ["Artist"] },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(worlds.every((world) => world.actualRole("C") === "Cerenovus")).toBe(true);
  });
  test("evil changed-role claims can be ordinary lies", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Cerenovus", "Pit-Hag", "Seamstress", "Artist", "Clockmaker", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        claims: [
          {
            type: "Seamstress",
            name: "A",
            timing: "night_1",
            among: ["B", "C"],
            aligned: false,
            possibleActualRoles: ["Imp"],
          },
          {
            type: "Artist",
            name: "A",
            timing: "day_2",
            info: [{ timing: "day_2", expression: "B.role == Clockmaker" }],
            possibleActualRoles: ["Imp"],
          },
          { type: "Clockmaker", name: "B", possibleActualRoles: ["Clockmaker"] },
          { type: "Cerenovus", name: "C", possibleActualRoles: ["Cerenovus", "Pit-Hag"] },
          { type: "Artist", name: "D", possibleActualRoles: ["Artist"] },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(worlds.some((world) => world.actualRole("C") === "Pit-Hag")).toBe(true);
  });
  test("Sweetheart death makes one persistent target drunk after the death timing", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Sweetheart", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Sweetheart"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["A"] }],
        claims: [
          {
            type: "Chef",
            name: "B",
            info: [
              { timing: "day_1", expression: "C.role == Imp" },
              { timing: "day_2", expression: "A.role == Imp" },
            ],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isDrunk("B", "day_1")).toBe(false);
    expect(worlds[0]?.isDrunk("B", "day_2")).toBe(true);
    expect(worlds[0]?.drunkByTiming.get("day_2")).toEqual(new Set(["B"]));
  });
  test("top-level constraints apply as hard truths", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        constraints: [{ expression: "#{p : players | p.role == Imp} == 1" }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(3);
    expect(
      worlds.every((world) => ["A", "B", "C"].filter((player) => world.actualRole(player) === "Imp").length === 1),
    ).toBe(true);
  });
  test("Clockmaker uses the puzzle seating order", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["Demon", "Minion", "Clockmaker", "A", "B", "C"],
        script: ["Imp", "Baron", "Clockmaker", "Chef", "Empath", "Investigator"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "Demon", roles: ["Imp"] },
            { name: "Minion", roles: ["Baron"] },
            { name: "Clockmaker", roles: ["Clockmaker"] },
            { name: "A", roles: ["Chef"] },
            { name: "B", roles: ["Empath"] },
            { name: "C", roles: ["Investigator"] },
          ],
        }),
        claims: [
          {
            type: "Clockmaker",
            name: "Clockmaker",
            distance: 1,
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("Chambermaid counts players who woke due to their ability", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E", "F", "G"],
        script: ["Chambermaid", "Clockmaker", "Oracle", "Exorcist", "Scarlet Woman", "Imp", "Butler"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chambermaid"] },
            { name: "B", roles: ["Clockmaker"] },
            { name: "C", roles: ["Oracle"] },
            { name: "D", roles: ["Exorcist"] },
            { name: "E", roles: ["Scarlet Woman"] },
            { name: "F", roles: ["Imp"] },
            { name: "G", roles: ["Butler"] },
          ],
        }),
        claims: [
          {
            type: "Chambermaid",
            name: "A",
            checks: [
              { left: "B", right: "C", timing: "night_1", count: 1 },
              { left: "C", right: "E", timing: "night_1", count: 0 },
              { left: "C", right: "D", timing: "night_2", count: 2 },
              { left: "E", right: "G", timing: "night_2", count: 1 },
            ],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("Princess nominations block Demon night kills unless poisoned", async () => {
    const blockedWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Princess", "Imp", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Princess"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Empath"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["D"] },
          { timing: "night_2", type: "nightDeath", players: ["C"] },
        ],
        claims: [{ type: "Princess", name: "A", nominations: [{ timing: "day_1", player: "D" }] }],
      },
      backend,
    ).solveAll();
    const poisonedWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Princess", "Poisoner", "Imp", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Princess"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Poisoner"] },
            { name: "D", roles: ["Chef"] },
            { name: "E", roles: ["Empath"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["D"] },
          { timing: "night_2", type: "nightDeath", players: ["E"] },
        ],
        claims: [{ type: "Princess", name: "A", nominations: [{ timing: "day_1", player: "D" }] }],
      },
      backend,
    ).solveAll();
    expect(blockedWorlds).toEqual([]);
    expect(poisonedWorlds).toHaveLength(1);
    expect(poisonedWorlds[0]?.poisonedByTiming.get("night_2")).toEqual(new Set(["A"]));
  });
  test("Exorcist choices block Demon night kills", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Exorcist", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Exorcist"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["C"] }],
        claims: [{ type: "Exorcist", name: "A", choices: [{ timing: "night_2", player: "B" }] }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Gossip death sources use following-night poisoning", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Gossip", "Poisoner", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Gossip"] },
            { name: "B", roles: ["Poisoner"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Empath"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["D"] }],
        claims: [
          {
            type: "Gossip",
            name: "A",
            statements: [{ timing: "day_1", expression: "C.role == Chef" }],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(worlds.every((world) => !world.isPoisoned("A", "night_2"))).toBe(true);
  });
  test("same-night Poisoner death removes poison before night information", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Chambermaid", "Poisoner", "Imp", "Exorcist", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chambermaid"] },
            { name: "B", roles: ["Poisoner"] },
            { name: "C", roles: ["Imp"] },
            { name: "D", roles: ["Exorcist"] },
            { name: "E", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [
          {
            type: "Chambermaid",
            name: "A",
            checks: [{ left: "D", right: "E", timing: "night_2", count: 2 }],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Gossip-killed Imp does not create an Imp starpass", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Gossip", "Imp", "Poisoner", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Gossip"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Poisoner"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [
          {
            type: "Gossip",
            name: "A",
            statements: [{ timing: "day_1", expression: "B.role == Imp" }],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Gossip-killed Poisoner does not poison later night information", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Chambermaid", "Gossip", "Poisoner", "Exorcist", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chambermaid"] },
            { name: "B", roles: ["Gossip"] },
            { name: "C", roles: ["Poisoner"] },
            { name: "D", roles: ["Exorcist"] },
            { name: "E", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["C"] }],
        claims: [
          {
            type: "Chambermaid",
            name: "A",
            checks: [{ left: "D", right: "E", timing: "night_2", count: 2 }],
          },
          {
            type: "Gossip",
            name: "B",
            statements: [{ timing: "day_1", expression: "D.role == Exorcist" }],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Oracle counts evil dead players", async () => {
    const validWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Oracle", "Baron", "Imp", "Clockmaker"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Oracle"] },
            { name: "B", roles: ["Baron"] },
            { name: "C", roles: ["Clockmaker"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["B"] },
          { timing: "day_1", type: "doomsayerDeath", players: ["C"] },
        ],
        claims: [{ type: "Oracle", name: "A", timing: "night_2", count: 1 }],
      },
      backend,
    ).solveAll();
    const invalidWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Oracle", "Baron", "Imp", "Clockmaker"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Oracle"] },
            { name: "B", roles: ["Baron"] },
            { name: "C", roles: ["Clockmaker"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["B"] },
          { timing: "day_1", type: "doomsayerDeath", players: ["C"] },
        ],
        claims: [{ type: "Oracle", name: "A", timing: "night_2", count: 0 }],
      },
      backend,
    ).solveAll();
    expect(validWorlds).toHaveLength(1);
    expect(invalidWorlds).toEqual([]);
  });
  test("night deaths without a catch exclude actual Imp deaths", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Imp", "Sage"],
        setup: "none",
        uniqueCharacters: true,
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(new Set(worlds.map((world) => world.actualRole("B")))).not.toContain("Imp");
  });
  test("Demon-sourced night deaths cannot kill sober healthy Soldiers", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Soldier", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Soldier"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Demon-sourced night deaths can kill poisoned Soldiers", async () => {
    const game = buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Soldier", "Imp", "Poisoner"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Soldier"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Poisoner"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    );
    game.fixPoisoned("A", true, "night_2");
    const worlds = await game.solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.poisonedByTiming.get("night_2")).toEqual(new Set(["A"]));
  });
  test("Tea Lady protection can explain a survived execution", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Tea Lady", "Imp", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chef"] },
            { name: "B", roles: ["Tea Lady"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "survivedExecution", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("Tea Lady protected players cannot die unless the Tea Lady is poisoned", async () => {
    const blockedWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Tea Lady", "Imp", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chef"] },
            { name: "B", roles: ["Tea Lady"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const poisonedWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Tea Lady", "Poisoner", "Imp", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chef"] },
            { name: "B", roles: ["Tea Lady"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Imp"] },
            { name: "E", roles: ["Poisoner"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(blockedWorlds).toEqual([]);
    expect(poisonedWorlds).toHaveLength(1);
    expect(poisonedWorlds[0]?.poisonedByTiming.get("night_1")).toEqual(new Set(["B"]));
  });
  test("Devil's Advocate can explain a survived execution", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Devil's Advocate", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chef"] },
            { name: "B", roles: ["Devil's Advocate"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "survivedExecution", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("Vigormortis-killed Poisoners keep poisoning after death", async () => {
    const withoutVigormortisWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Tea Lady", "Poisoner", "Imp", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chef"] },
            { name: "B", roles: ["Tea Lady"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Imp"] },
            { name: "E", roles: ["Poisoner"] },
          ],
        }),
        timeline: [
          { timing: "night_2", type: "nightDeath", players: ["E"] },
          { timing: "night_3", type: "nightDeath", players: ["A"] },
        ],
        claims: [],
      },
      backend,
    ).solveAll();
    const withVigormortisWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Tea Lady", "Poisoner", "Vigormortis", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chef"] },
            { name: "B", roles: ["Tea Lady"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Vigormortis"] },
            { name: "E", roles: ["Poisoner"] },
          ],
        }),
        timeline: [
          { timing: "night_2", type: "nightDeath", players: ["E"] },
          { timing: "night_3", type: "nightDeath", players: ["A"] },
        ],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(withoutVigormortisWorlds).toEqual([]);
    expect(withVigormortisWorlds).toHaveLength(1);
    expect(withVigormortisWorlds[0]?.poisonedByTiming.get("night_3")).toEqual(new Set(["B"]));
  });
  test("Doomsayer deaths do not exclude players from script demon roles", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Imp", "Sage"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Sage"] },
            { name: "B", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "doomsayerDeath", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("B")).toBe("Imp");
  });
  test("executions in continuing puzzle docs exclude Hermit", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Hermit", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        timeline: [{ timing: "day_1", type: "execution", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(new Set(worlds.map((world) => world.actualRole("A")))).not.toContain("Hermit");
  });
  test("Doomsayer deaths with callers require the same registered alignment", async () => {
    const validWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Sage", "Mayor"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Sage"] },
            { name: "B", roles: ["Mayor"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "doomsayerDeath", caller: "A", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const invalidWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Sage", "Mayor"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Sage"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Mayor"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "doomsayerDeath", caller: "A", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const spyWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Spy", "Sage"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Spy"] },
            { name: "B", roles: ["Sage"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "doomsayerDeath", caller: "A", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(validWorlds).toHaveLength(1);
    expect(invalidWorlds).toEqual([]);
    expect(spyWorlds).toHaveLength(1);
  });
  test("night deaths require a living catch when they kill an actual demon", async () => {
    const impWithoutMinionWorlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const impWithMinionWorlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Imp", "Goblin"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Goblin"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const dyingMinionWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Goblin", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Goblin"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A", "B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const poWithScarletWomanWorlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Po", "Scarlet Woman"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Po"] },
            { name: "B", roles: ["Scarlet Woman"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(impWithoutMinionWorlds).toEqual([]);
    expect(impWithMinionWorlds).toHaveLength(1);
    expect(dyingMinionWorlds).toEqual([]);
    expect(poWithScarletWomanWorlds).toHaveLength(1);
  });
  test("Slayer shots and Witch curses require a living catch when they kill an actual demon", async () => {
    const slayerShotWithoutCatchWorlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "slayerShot", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const slayerShotWithCatchWorlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Imp", "Scarlet Woman"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Scarlet Woman"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "slayerShot", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const witchCurseWithCatchWorlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Imp", "Scarlet Woman", "Witch"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Scarlet Woman"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "witchCurse", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(slayerShotWithoutCatchWorlds).toEqual([]);
    expect(slayerShotWithCatchWorlds).toHaveLength(1);
    expect(witchCurseWithCatchWorlds).toHaveLength(1);
  });
  test("Witch curse deaths with callers require a living healthy Witch source", async () => {
    const selfCurseWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Witch", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Witch"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "witchCurse", players: ["A"], caller: "A" }],
        claims: [],
      },
      backend,
    ).solveAll();
    const deadWitchSourceWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Witch", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Witch"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["A"] },
          { timing: "day_2", type: "witchCurse", players: ["C"], caller: "C" },
        ],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(selfCurseWorlds).toHaveLength(1);
    expect(deadWitchSourceWorlds).toEqual([]);
  });
  test("Snake Charmer checks use timed Demon roles after Scarlet Woman catches", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "D", "B", "E", "C"],
        script: ["Snake Charmer", "Chef", "Scarlet Woman", "Mathematician", "No Dashii"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Snake Charmer"] },
            { name: "B", roles: ["Scarlet Woman"] },
            { name: "C", roles: ["No Dashii"] },
            { name: "D", roles: ["Chef"] },
            { name: "E", roles: ["Mathematician"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["C"] }],
        claims: [{ type: "Snake Charmer", name: "A", checks: [{ timing: "night_3", player: "B", demon: false }] }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Snake Charmer checks same-night Fang Gu before the jump", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["SC", "Demon", "Outsider", "Witch"],
        script: ["Snake Charmer", "Fang Gu", "Mutant", "Witch"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "SC", roles: ["Snake Charmer"] },
            { name: "Demon", roles: ["Fang Gu"] },
            { name: "Outsider", roles: ["Mutant"] },
            { name: "Witch", roles: ["Witch"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["Demon"] }],
        claims: [{ type: "Snake Charmer", name: "SC", checks: [{ timing: "night_2", player: "Demon", demon: false }] }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("standard puzzle docs require the final observed state to have a living demon path", async () => {
    const baseDoc = {
      players: ["A", "B", "C", "D", "E"],
      script: ["Imp", "Goblin", "Chef", "Empath", "Ravenkeeper"],
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Imp"] },
          { name: "B", roles: ["Goblin"] },
          { name: "C", roles: ["Chef"] },
          { name: "D", roles: ["Empath"] },
          { name: "E", roles: ["Ravenkeeper"] },
        ],
      }),
      claims: [],
    } as const;
    const ongoingWorlds = await buildFromDoc(
      {
        ...baseDoc,
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
      },
      backend,
    ).solveAll();
    const endedWorlds = await buildFromDoc(
      {
        ...baseDoc,
        timeline: [
          { timing: "night_2", type: "nightDeath", players: ["A"] },
          { timing: "night_3", type: "nightDeath", players: ["B"] },
        ],
      },
      backend,
    ).solveAll();
    expect(ongoingWorlds).toHaveLength(1);
    expect(endedWorlds).toEqual([]);
  });
  test("standard puzzle docs allow a final observed Fang Gu jump", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["Demon", "Outsider", "Witch", "A", "B", "C", "D", "E"],
        script: ["Fang Gu", "Witch", "Mutant", "Klutz", "Chef", "Empath", "Artist", "Juggler", "Dreamer"],
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "Demon", roles: ["Fang Gu"] },
            { name: "Outsider", roles: ["Mutant"] },
            { name: "Witch", roles: ["Witch"] },
            { name: "A", roles: ["Chef"] },
            { name: "B", roles: ["Empath"] },
            { name: "C", roles: ["Artist"] },
            { name: "D", roles: ["Juggler"] },
            { name: "E", roles: ["Klutz"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["Demon"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("executed Legion players can leave an ongoing Legion game", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Legion", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Legion"] },
            { name: "B", roles: ["Legion"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("night-killed Legion players can leave an ongoing Legion game", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Legion", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Legion"] },
            { name: "B", roles: ["Legion"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("Riot nominations can kill the starting Riot while a Minion becomes Riot", async () => {
    const game = buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E", "F", "G"],
        script: ["Riot", "Baron", "Drunk", "Recluse", "Chef", "Empath", "Ravenkeeper"],
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Riot"] },
            { name: "B", roles: ["Baron"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Empath"] },
            { name: "E", roles: ["Ravenkeeper"] },
            { name: "F", roles: ["Drunk"] },
            { name: "G", roles: ["Recluse"] },
          ],
        }),
        timeline: [{ timing: "day_3", type: "nominationDeath", players: ["A"], caller: "C" }],
        claims: [],
      },
      backend,
    );
    game.addTruth(game.hasRoleAt("B", "Riot", "day_3"));
    const worlds = await game.solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Riot")).toBe("A");
    expect(worlds[0]?.holder("Baron")).toBe("B");
  });
  test("Fang Gu night deaths can jump to a living Outsider", async () => {
    const game = buildFromDoc(
      {
        players: ["Fang Gu", "Mutant", "Artist"],
        script: ["Fang Gu", "Witch", "Mutant", "Artist"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "Fang Gu", roles: ["Fang Gu"] },
            { name: "Mutant", roles: ["Mutant"] },
            { name: "Artist", roles: ["Artist"] },
          ],
        }),
        timeline: [
          { timing: "night_2", type: "nightDeath", players: ["Fang Gu"] },
          { timing: "night_3", type: "nightDeath", players: ["Artist"] },
        ],
        claims: [],
      },
      backend,
    );
    const worlds = await game.solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("Fang Gu")).toBe("Fang Gu");
    expect(worlds[0]?.actualRole("Mutant")).toBe("Mutant");
  });
  test("Fang Gu demon kills cannot show an unjumped Outsider death", async () => {
    const fangGuWorlds = await buildFromDoc(
      {
        players: ["Fang Gu", "Mutant", "Artist"],
        script: ["Fang Gu", "Mutant", "Artist"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "Fang Gu", roles: ["Fang Gu"] },
            { name: "Mutant", roles: ["Mutant"] },
            { name: "Artist", roles: ["Artist"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["Mutant"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const ordinaryDemonWorlds = await buildFromDoc(
      {
        players: ["Demon", "Mutant", "Artist"],
        script: ["Fang Gu", "Vortox", "Mutant", "Artist"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "Demon", roles: ["Vortox"] },
            { name: "Mutant", roles: ["Mutant"] },
            { name: "Artist", roles: ["Artist"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["Mutant"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(fangGuWorlds).toEqual([]);
    expect(ordinaryDemonWorlds).toHaveLength(1);
  });
  test("non-Demon Fang Gu night deaths do not jump", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Gossip", "Fang Gu", "Mutant", "Exorcist", "Artist"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Gossip"] },
            { name: "B", roles: ["Fang Gu"] },
            { name: "C", roles: ["Mutant"] },
            { name: "D", roles: ["Exorcist"] },
            { name: "E", roles: ["Artist"] },
          ],
        }),
        timeline: [
          { timing: "night_2", type: "nightDeath", players: ["B"] },
          { timing: "night_3", type: "nightDeath", players: ["E"] },
        ],
        claims: [
          {
            type: "Gossip",
            name: "A",
            statements: [{ timing: "day_1", expression: "B.role == `Fang Gu`" }],
          },
          {
            type: "Exorcist",
            name: "D",
            choices: [{ timing: "night_2", player: "B" }],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Xaan poisons Townsfolk on the night matching the Outsider count", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Imp", "Xaan", "Drunk", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Xaan"] },
            { name: "C", roles: ["Drunk"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("A", "night_1")).toBe(false);
    expect(worlds[0]?.isPoisoned("B", "night_1")).toBe(false);
    expect(worlds[0]?.isPoisoned("C", "night_1")).toBe(false);
    expect(worlds[0]?.isPoisoned("D", "night_1")).toBe(true);
  });
  test("dead Xaan does not poison on the night matching the Outsider count", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Imp", "Xaan", "Drunk", "Puzzlemaster", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Xaan"] },
            { name: "C", roles: ["Drunk"] },
            { name: "D", roles: ["Puzzlemaster"] },
            { name: "E", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("E", "night_2")).toBe(false);
  });
  test("Atheist setup has no evil team and arbitrary information", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Spy", "Atheist", "Artist", "Clockmaker"],
        setup: "atheist",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Atheist"] },
            { name: "B", roles: ["Artist"] },
            { name: "C", roles: ["Clockmaker"] },
          ],
        }),
        claims: [
          {
            type: "Artist",
            name: "B",
            timing: "day_1",
            info: [{ timing: "day_1", expression: "A.role == Imp" }],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBeUndefined();
    expect(worlds[0]?.holder("Spy")).toBeUndefined();
    expect(worlds[0]?.holder("Atheist")).toBe("A");
  });
  test("timeline deaths stop later Poisoner effects", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Poisoner", "Investigator"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Poisoner"] },
            { name: "B", roles: ["Investigator"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["A"] }],
        claims: [
          {
            type: "Investigator",
            name: "B",
            timing: "night_2",
            role: "Poisoner",
            among: ["A", "C"],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("A", "night_2")).toBe(false);
    expect(worlds[0]?.isPoisoned("B", "night_2")).toBe(false);
    expect(worlds[0]?.isPoisoned("C", "night_2")).toBe(false);
  });
  test("nightDeath does not encode whether the killed player acted first", async () => {
    const game = buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Poisoner", "Investigator"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Poisoner"] },
            { name: "B", roles: ["Investigator"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    );
    game.fixPoisoned("B", true, "night_2");
    const worlds = await game.solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("A", "night_2")).toBe(false);
    expect(worlds[0]?.isPoisoned("B", "night_2")).toBe(true);
    expect(worlds[0]?.isPoisoned("C", "night_2")).toBe(false);
  });
  test("Demon-sourced night deaths affect same-night Empath neighbors", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Empath", "Chef", "Imp", "Scarlet Woman"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Empath"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Imp"] },
            { name: "D", roles: ["Scarlet Woman"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [{ type: "Empath", name: "A", timing: "night_2", count: 2 }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("timed Empath claims use living neighbors from the timeline", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Empath", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Empath"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Imp"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["B"] }],
        claims: [{ type: "Empath", name: "A", timing: "night_2", count: 1 }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("C")).toBe("Imp");
  });
  test("Nightwatchman learned result constrains sober healthy claims", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Nightwatchman", "Drunk", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [{ name: "A", roles: ["Nightwatchman", "Drunk"] }],
          excluded: [{ name: "B", roles: ["Nightwatchman", "Drunk"] }],
        }),
        claims: [{ type: "Nightwatchman", name: "A", timing: "night_1", chosen: "B", learned: false }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Drunk");
  });
  test("Nightwatchman confirmation from a good chosen player requires an active source", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Nightwatchman", "Drunk", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Nightwatchman", "Drunk"] },
            { name: "B", roles: ["Chef"] },
          ],
        }),
        claims: [
          {
            type: "Nightwatchman",
            name: "A",
            timing: "night_1",
            chosen: "B",
            learned: true,
            confirmedByChosen: true,
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Nightwatchman");
  });
  test("Ravenkeeper learned role constrains sober healthy claims", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Ravenkeeper", "Scarlet Woman", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Ravenkeeper"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Ravenkeeper", name: "A", timing: "night_2", player: "B", role: "Scarlet Woman" }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("B")).toBe("Scarlet Woman");
  });
  test("Ravenkeeper learned role allows Spy registration", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Ravenkeeper", "Spy", "Imp", "Saint"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Ravenkeeper"] },
            { name: "B", roles: ["Spy"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Ravenkeeper", name: "A", timing: "night_2", player: "B", role: "Saint" }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("Undertaker learned role allows Spy registration", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Imp", "Spy", "Undertaker", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Undertaker"] },
            { name: "B", roles: ["Spy"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["B"] }],
        claims: [{ type: "Undertaker", name: "A", timing: "night_2", player: "B", role: "Empath" }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("Courtier drunking disables Vortox false information", async () => {
    const validWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Courtier", "Vortox", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Courtier"] },
            { name: "B", roles: ["Vortox"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        claims: [
          { type: "Courtier", name: "A", timing: "night_1", role: "Vortox", drunkTimings: ["night_1"] },
          { type: "Chef", name: "C", timing: "night_1", count: 0 },
        ],
      },
      backend,
    ).solveAll();
    const invalidWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Courtier", "Vortox", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Courtier"] },
            { name: "B", roles: ["Vortox"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        claims: [
          { type: "Courtier", name: "A" },
          { type: "Chef", name: "C", timing: "night_1", count: 0 },
        ],
      },
      backend,
    ).solveAll();
    expect(validWorlds).toHaveLength(1);
    expect(validWorlds[0]?.isDrunk("B", "night_1")).toBe(true);
    expect(invalidWorlds).toEqual([]);
  });
  test("Philosopher choice can satisfy chosen role information", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Philosopher", "Snake Charmer", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Philosopher"] },
            { name: "B", roles: ["Snake Charmer"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [
          { type: "Philosopher", name: "A", timing: "night_1", role: "Snake Charmer" },
          {
            type: "Snake Charmer",
            name: "A",
            checks: [{ player: "C", demon: true, timing: "night_1" }],
            possibleActualRoles: ["Philosopher"],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Philosopher");
  });
  test("Philosopher choice drunkens the chosen role while the Philosopher is alive", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Philosopher", "Empath", "Imp", "Saint"],
        setup: "none",
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Philosopher"] },
            { name: "B", roles: ["Empath"] },
            { name: "C", roles: ["Imp"] },
            { name: "D", roles: ["Saint"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["A"] }],
        claims: [
          { type: "Philosopher", name: "A", timing: "night_1", role: "Empath" },
          { type: "Empath", name: "A", timing: "night_1", count: 0, possibleActualRoles: ["Philosopher"] },
          { type: "Empath", name: "B", timing: "night_1", count: 0 },
          { type: "Empath", name: "B", timing: "night_2", count: 1 },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isDrunk("B", "night_1")).toBe(true);
    expect(worlds[0]?.isDrunk("B", "night_2")).toBe(false);
  });
  test("custom info statements can use an explicit active role", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Philosopher", "Snake Charmer", "Seamstress", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Philosopher"] },
            { name: "B", roles: ["Snake Charmer"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [
          {
            type: "Philosopher",
            name: "A",
            timing: "night_1",
            role: "Snake Charmer",
            info: [{ timing: "night_1", role: "Seamstress", expression: "false" }],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("death-causing Acrobat and Gambler claims require the active healthy role", async () => {
    const acrobatWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Acrobat", "Drunk", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Drunk"] },
            { name: "B", roles: ["Acrobat"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Acrobat", name: "A", choices: [{ timing: "night_2", player: "B", died: true }] }],
      },
      backend,
    ).solveAll();
    const gamblerWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Gambler", "Drunk", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Drunk"] },
            { name: "B", roles: ["Gambler"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [
          { type: "Gambler", name: "A", guesses: [{ timing: "night_2", player: "B", role: "Imp", survived: false }] },
        ],
      },
      backend,
    ).solveAll();
    expect(acrobatWorlds).toEqual([]);
    expect(gamblerWorlds).toEqual([]);
  });
  test("Slayer no-kill claims exclude actual demon targets", async () => {
    const killedDemonWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Slayer", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Slayer"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: false }],
      },
      backend,
    ).solveAll();
    const livingTownsfolkWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Slayer", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Slayer"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "C", killed: false }],
      },
      backend,
    ).solveAll();
    expect(killedDemonWorlds).toEqual([]);
    expect(livingTownsfolkWorlds).toHaveLength(1);
  });
  test("Slayer kill claims allow Recluse demon registration", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Slayer", "Recluse", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Slayer"] },
            { name: "B", roles: ["Recluse"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("Slayer kill claims require an active healthy Slayer", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Slayer", "Drunk", "Recluse", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Drunk"] },
            { name: "B", roles: ["Recluse"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Slayer kill claims require Scarlet Woman for actual demon targets in ongoing games", async () => {
    const noCatchWorlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Slayer", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Slayer"] },
            { name: "B", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true }],
      },
      backend,
    ).solveAll();
    const catchWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Slayer", "Imp", "Scarlet Woman"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Slayer"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Scarlet Woman"] },
          ],
        }),
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true }],
      },
      backend,
    ).solveAll();
    expect(noCatchWorlds).toEqual([]);
    expect(catchWorlds).toHaveLength(1);
  });
  test("Klutz no-loss claims require a healthy Klutz to choose good", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Klutz", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Klutz"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        claims: [{ type: "Klutz", name: "A", timing: "night_2", chosen: "B", lost: false }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Klutz no-loss claims can be disabled by poisoning", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Klutz", "Imp", "Poisoner"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Klutz"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Poisoner"] },
          ],
        }),
        claims: [{ type: "Klutz", name: "A", timing: "night_2", chosen: "B", lost: false }],
      },
      backend,
    ).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
    expect(worlds.every((world) => world.poisonedByTiming.get("night_2")?.has("A"))).toBe(true);
  });
  test("day Slayer shots use the corresponding night poison state", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Slayer", "Imp", "Poisoner", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Slayer"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Poisoner"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        claims: [
          { type: "Chef", name: "D", timing: "night_1", count: 0 },
          { type: "Slayer", name: "A", timing: "day_1", target: "B", killed: false },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Virgin no-proc claims exclude Townsfolk nominators", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Virgin", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Virgin"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Virgin", name: "A", timing: "day_1", nominator: "B", executed: false }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Virgin execution can be triggered by Spy registration", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Virgin", "Spy", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Virgin"] },
            { name: "B", roles: ["Spy"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Virgin", name: "A", timing: "day_1", nominator: "B", executed: true }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("multiple Village Idiots make one real Village Idiot drunk", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Village Idiot", "Imp"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Village Idiot"] },
            { name: "B", roles: ["Village Idiot"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(2);
    expect(new Set(worlds.map((world) => (world.isDrunk("A") ? "A" : "B")))).toEqual(new Set(["A", "B"]));
  });
  test("Puzzlemaster drunking can coexist with a single Village Idiot", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Puzzlemaster", "Village Idiot", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Puzzlemaster"] },
            { name: "B", roles: ["Village Idiot"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        claims: [
          { type: "Puzzlemaster", name: "A" },
          { type: "Chef", name: "C", count: 1 },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isDrunk("C")).toBe(true);
  });
  test("Puzzlemaster guesses constrain learned Demon information", async () => {
    const baseDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Puzzlemaster", "Chef", "Empath", "Imp"],
      setup: "none" as const,
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Puzzlemaster"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Imp"] },
          { name: "D", roles: ["Empath"] },
        ],
      }),
    };
    const validWorlds = await buildFromDoc(
      {
        ...baseDoc,
        claims: [
          { type: "Puzzlemaster", name: "A", guesses: [{ timing: "day_1", player: "B", learnedDemon: "C" }] },
          { type: "Chef", name: "B", count: 1 },
        ],
      },
      backend,
    ).solveAll();
    const invalidWorlds = await buildFromDoc(
      {
        ...baseDoc,
        claims: [
          { type: "Puzzlemaster", name: "A", guesses: [{ timing: "day_1", player: "D", learnedDemon: "C" }] },
          { type: "Chef", name: "B", count: 1 },
        ],
      },
      backend,
    ).solveAll();
    expect(validWorlds).toHaveLength(1);
    expect(validWorlds[0]?.isDrunk("B")).toBe(true);
    expect(invalidWorlds).toEqual([]);
  });
  test("Legionary counts living evil players before the next living Legionary", async () => {
    const validWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Legionary", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Legionary"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Legionary"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        claims: [{ type: "Legionary", name: "A", counts: [{ count: 1 }] }],
      },
      backend,
    ).solveAll();
    const invalidWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Legionary", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Legionary"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Legionary"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        claims: [{ type: "Legionary", name: "A", counts: [{ count: 0 }] }],
      },
      backend,
    ).solveAll();
    expect(validWorlds).toHaveLength(1);
    expect(invalidWorlds).toEqual([]);
  });
  test("puzzle-34-the-vortox-conjecture.json parses and solves", async () => {
    const doc = loadDoc("puzzle-34-the-vortox-conjecture.json");
    const worlds = await buildFromDoc(doc, backend).solveAll();
    expect(worlds.length).toBeGreaterThan(0);
  });
});
