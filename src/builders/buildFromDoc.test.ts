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
  test("Innkeeper choices make exactly one protected player drunk until dusk", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Innkeeper", "Chef", "Gambler", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Innkeeper"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Gambler"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Innkeeper", name: "A", choices: [{ players: ["B", "C"], timing: "night_2" }] }],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    const world = worlds[0];
    expect([world?.isDrunk("B", "night_2"), world?.isDrunk("C", "night_2")].filter(Boolean)).toHaveLength(1);
    expect(world?.isDrunk("B", "day_2")).toBe(world?.isDrunk("B", "night_2"));
    expect(world?.isDrunk("C", "day_2")).toBe(world?.isDrunk("C", "night_2"));
    expect(world?.isDrunk("B", "night_3")).toBe(false);
    expect(world?.isDrunk("C", "night_3")).toBe(false);
  });
  test("a sober Innkeeper choice protects both players from the Demon", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Innkeeper", "Chef", "Gambler", "Imp"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Innkeeper"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Gambler"] },
          { name: "D", roles: ["Imp"] },
        ],
      }),
      timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
      claims: [],
    };

    expect(await buildFromDoc(baseDoc, backend).solveAll()).toHaveLength(1);
    expect(
      await buildFromDoc(
        {
          ...baseDoc,
          claims: [{ type: "Innkeeper", name: "A", choices: [{ players: ["B", "C"], timing: "night_2" }] }],
        },
        backend,
      ).solveAll(),
    ).toEqual([]);
  });
  test("a drunk Demon cannot produce a night death", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Courtier", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Courtier"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["C"] }],
        claims: [{ type: "Courtier", name: "A", timing: "night_1", role: "Imp", drunkTimings: ["night_2"] }],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });
  test("a healthy Fool survives their first death but not a later one", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C"],
      script: ["Fool", "Chef", "Imp"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Fool"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Imp"] },
        ],
      }),
      claims: [],
    };

    expect(
      await buildFromDoc(
        { ...baseDoc, timeline: [{ timing: "day_1", type: "execution", players: ["A"] }] },
        backend,
      ).solveAll(),
    ).toEqual([]);
    expect(
      await buildFromDoc(
        {
          ...baseDoc,
          timeline: [
            { timing: "day_1", type: "survivedExecution", players: ["A"] },
            { timing: "day_2", type: "execution", players: ["A"] },
          ],
        },
        backend,
      ).solveAll(),
    ).toHaveLength(1);
  });
  test("another role's protection does not consume the Fool ability", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Fool", "Tea Lady", "Chef", "Empath", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Fool"] },
            { name: "B", roles: ["Tea Lady"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Empath"] },
            { name: "E", roles: ["Imp"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "survivedExecution", players: ["A"] },
          { timing: "night_2", type: "nightDeath", players: ["B"] },
          { timing: "day_2", type: "execution", players: ["A"] },
        ],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });
  test("a healthy Pacifist can explain a good player's survived execution", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Pacifist", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Pacifist"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "survivedExecution", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });
  test("an executed Minion makes everyone except the Minstrel drunk through the following day", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Minstrel", "Devil's Advocate", "Imp", "Chef"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Minstrel"] },
          { name: "B", roles: ["Devil's Advocate"] },
          { name: "C", roles: ["Imp"] },
          { name: "D", roles: ["Chef"] },
        ],
      }),
      timeline: [{ timing: "day_1", type: "execution", players: ["B"] }],
      claims: [],
    };

    const worlds = await buildFromDoc(baseDoc, backend).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isDrunk("A", "night_2")).toBe(false);
    expect(worlds[0]?.isDrunk("C", "night_2")).toBe(true);
    expect(worlds[0]?.isDrunk("C", "day_2")).toBe(true);
    expect(worlds[0]?.isDrunk("C", "night_3")).toBe(false);

    expect(
      await buildFromDoc(
        {
          ...baseDoc,
          timeline: [...(baseDoc.timeline ?? []), { timing: "night_2", type: "nightDeath", players: ["D"] }],
        },
        backend,
      ).solveAll(),
    ).toEqual([]);
  });
  test("an Assassin kill bypasses Fool protection and consumes the ability", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Assassin", "Fool", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Assassin"] },
            { name: "B", roles: ["Fool"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [
          {
            type: "Assassin",
            name: "A",
            target: "B",
            timing: "night_2",
            possibleActualRoles: ["Assassin"],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });
  test("the Assassin still kills the Goon before becoming drunk", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Assassin", "Goon", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Assassin"] },
            { name: "B", roles: ["Goon"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [{ type: "Assassin", name: "A", target: "B", timing: "night_2", possibleActualRoles: ["Assassin"] }],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isDrunk("A", "night_2")).toBe(true);
  });
  test("the Assassin cannot use their ability more than once", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Assassin", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Assassin"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Empath"] },
          ],
        }),
        timeline: [
          { timing: "night_2", type: "nightDeath", players: ["B"] },
          { timing: "night_3", type: "nightDeath", players: ["C"] },
        ],
        claims: [
          { type: "Assassin", name: "A", target: "B", timing: "night_2", possibleActualRoles: ["Assassin"] },
          { type: "Assassin", name: "A", target: "C", timing: "night_3", possibleActualRoles: ["Assassin"] },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });
  test("Sailor choice drunks exactly one participant and only a drunk Sailor can die", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Sailor", "Chef", "Empath", "Imp"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Sailor"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Empath"] },
          { name: "D", roles: ["Imp"] },
        ],
      }),
      claims: [{ type: "Sailor", name: "A", choices: [{ player: "B", timing: "night_1" }] }],
    };
    const worlds = await buildFromDoc(baseDoc, backend).solveAll();
    expect(worlds).toHaveLength(1);
    expect([worlds[0]?.isDrunk("A", "night_1"), worlds[0]?.isDrunk("B", "night_1")].filter(Boolean)).toHaveLength(1);

    const deathWorlds = await buildFromDoc(
      { ...baseDoc, timeline: [{ timing: "night_1", type: "nightDeath", players: ["A"] }] },
      backend,
    ).solveAll();
    expect(deathWorlds).toHaveLength(1);
    expect(deathWorlds[0]?.isDrunk("A", "night_1")).toBe(true);
  });
  test("a Sailor cannot choose a dead player", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Sailor", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Sailor"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["B"] }],
        claims: [
          {
            type: "Sailor",
            name: "A",
            choices: [{ player: "B", timing: "night_2" }],
            possibleActualRoles: ["Sailor"],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });
  test("Grandmother dies when the Demon kills their grandchild", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Grandmother", "Chef", "Empath", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Grandmother"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A", "B"] }],
        claims: [{ type: "Grandmother", name: "A", grandchild: "B", role: "Chef", timing: "night_1" }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("Moonchild and Godfather choices provide conditional night-death sources", async () => {
    const moonchildWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Moonchild", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Moonchild"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Empath"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["A"] },
          { timing: "night_2", type: "nightDeath", players: ["B"] },
        ],
        claims: [{ type: "Moonchild", name: "A", chosen: "B", timing: "day_1" }],
      },
      backend,
    ).solveAll();
    expect(moonchildWorlds).toHaveLength(1);

    const godfatherWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Godfather", "Moonchild", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Godfather"] },
            { name: "B", roles: ["Moonchild"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["B"] },
          { timing: "night_2", type: "nightDeath", players: ["C"] },
        ],
        claims: [
          {
            type: "Godfather",
            name: "A",
            choices: [{ player: "C", timing: "night_2" }],
            possibleActualRoles: ["Godfather"],
          },
          { type: "Moonchild", name: "B" },
        ],
      },
      backend,
    ).solveAll();
    expect(godfatherWorlds).toHaveLength(1);
  });
  test("the Godfather wakes and must choose a victim after an Outsider dies during the day", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D", "E"],
      script: ["Godfather", "Moonchild", "Chambermaid", "Empath", "Chef"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Godfather"] },
          { name: "B", roles: ["Moonchild"] },
          { name: "C", roles: ["Chambermaid"] },
          { name: "D", roles: ["Empath"] },
          { name: "E", roles: ["Chef"] },
        ],
      }),
      claims: [
        {
          type: "Chambermaid",
          name: "C",
          checks: [{ left: "A", right: "D", timing: "night_2", count: 1 }],
        },
      ],
    };

    expect(await buildFromDoc(baseDoc, backend).solveAll()).toHaveLength(1);

    const revengeDoc: TestPuzzleDoc = {
      ...baseDoc,
      timeline: [
        { timing: "day_1", type: "execution", players: ["B"] },
        { timing: "night_2", type: "nightDeath", players: ["E"] },
      ],
      claims: [
        {
          type: "Godfather",
          name: "A",
          choices: [{ player: "E", timing: "night_2" }],
          possibleActualRoles: ["Godfather"],
        },
        {
          type: "Chambermaid",
          name: "C",
          checks: [{ left: "A", right: "D", timing: "night_2", count: 2 }],
        },
      ],
    };
    expect(await buildFromDoc(revengeDoc, backend).solveAll()).toHaveLength(1);
    expect(
      await buildFromDoc(
        { ...revengeDoc, timeline: revengeDoc.timeline?.filter((event) => event.type !== "nightDeath") },
        backend,
      ).solveAll(),
    ).toEqual([]);
  });
  test("a Godfather kill can fail against a protected target", async () => {
    const game = buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Godfather", "Moonchild", "Sailor", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Godfather"] },
            { name: "B", roles: ["Moonchild"] },
            { name: "C", roles: ["Sailor"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["B"] },
          { timing: "night_2", type: "nightDeath", players: [] },
        ],
        claims: [
          {
            type: "Godfather",
            name: "A",
            choices: [{ player: "C", timing: "night_2" }],
            possibleActualRoles: ["Godfather"],
          },
          {
            type: "Sailor",
            name: "C",
            choices: [{ player: "D", timing: "night_2" }],
          },
        ],
      },
      backend,
    );
    game.addTruth(game.soberAndHealthy("C", "night_2"));

    expect(await game.solveAll()).toHaveLength(1);
  });
  test("a healthy Tinker can die at night without another death source", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Tinker", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Tinker"] },
            { name: "B", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
  });
  test("an explicit Tinker death can happen by day only while the Tinker is healthy", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C"],
      script: ["Tinker", "Courtier", "Chef"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Tinker"] },
          { name: "B", roles: ["Courtier"] },
          { name: "C", roles: ["Chef"] },
        ],
      }),
      timeline: [{ timing: "day_1", type: "tinkerDeath", players: ["A"] }],
      claims: [],
    };

    expect(await buildFromDoc(baseDoc, backend).solveAll()).toHaveLength(1);
    expect(
      await buildFromDoc(
        {
          ...baseDoc,
          claims: [{ type: "Courtier", name: "B", timing: "night_1", role: "Tinker", drunkTimings: ["night_1"] }],
        },
        backend,
      ).solveAll(),
    ).toEqual([]);
  });
  test("Pukka poisons on the first night and kills the previous target later", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Pukka", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Pukka"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Empath"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("B", "night_1")).toBe(true);
    expect(worlds[0]?.isPoisoned("B", "day_1")).toBe(true);
  });
  test("Pukka may poison itself without suppressing the choice that caused the poison", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A"],
        script: ["Pukka"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({ possible: [{ name: "A", roles: ["Pukka"] }] }),
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("A", "night_1")).toBe(true);
    expect(worlds[0]?.isPoisoned("A", "day_1")).toBe(true);
  });
  test("Pukka can choose the Goon even though the resulting drunkenness prevents poison", async () => {
    const game = buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Pukka", "Goon"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Pukka"] },
            { name: "B", roles: ["Goon"] },
          ],
        }),
        claims: [],
      },
      backend,
    );
    game.addTruth(game.drunk("A", "night_1"));
    const worlds = await game.solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isDrunk("A", "night_1")).toBe(true);
    expect(worlds[0]?.isPoisoned("B", "night_1")).toBe(false);
  });
  test("Pukka poison persists while the Pukka is drunk and kills after they recover", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Pukka", "Chef", "Courtier", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Pukka"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Courtier"] },
            { name: "D", roles: ["Empath"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["D"] },
          { timing: "night_4", type: "nightDeath", players: ["B"] },
        ],
        claims: [
          {
            type: "Courtier",
            name: "C",
            role: "Pukka",
            timing: "night_1",
            drunkTimings: ["night_3"],
            possibleActualRoles: ["Courtier"],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("B", "night_2")).toBe(true);
    expect(worlds[0]?.isPoisoned("B", "night_3")).toBe(true);
    expect(worlds[0]?.isPoisoned("B", "night_4")).toBe(true);
  });
  test("an Exorcist blocks the Pukka's new choice but not the prior poisoned player's death", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Pukka", "Chef", "Exorcist"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Pukka"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Exorcist"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [
          {
            type: "Exorcist",
            name: "C",
            choices: [{ player: "A", timing: "night_2" }],
            possibleActualRoles: ["Exorcist"],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("B", "night_1")).toBe(true);
    expect(worlds[0]?.isPoisoned("C", "night_2")).toBe(false);
  });
  test("a resurrection requires a matching Professor action claim when no Shabaloth is in play", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C"],
      script: ["Professor", "Chef", "Imp"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Professor"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Imp"] },
        ],
      }),
      timeline: [
        { timing: "day_1", type: "execution", players: ["B"] },
        { timing: "night_2", type: "resurrection", players: ["B"] },
      ],
      claims: [],
    };

    expect(await buildFromDoc(baseDoc, backend).solveAll()).toEqual([]);

    const worlds = await buildFromDoc(
      {
        ...baseDoc,
        claims: [{ type: "Professor", name: "A", timing: "night_2", target: "B" }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Professor");
  });
  test("an evil Professor bluff does not replace the Shabaloth as a resurrection source", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Professor", "Mastermind", "Chef", "Shabaloth"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Mastermind"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Shabaloth"] },
          ],
        }),
        timeline: [
          { timing: "night_2", type: "nightDeath", players: ["B"] },
          { timing: "night_3", type: "resurrection", players: ["B"] },
        ],
        claims: [
          {
            type: "Professor",
            name: "A",
            timing: "night_3",
            target: "B",
            possibleActualRoles: ["Mastermind"],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Mastermind");
    expect(worlds[0]?.actualRole("C")).toBe("Shabaloth");
  });
  test("a healthy Shabaloth can regurgitate a player who was already dead when chosen", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Shabaloth", "Chef", "Courtier", "Empath"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Shabaloth"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Courtier"] },
          { name: "D", roles: ["Empath"] },
        ],
      }),
      timeline: [
        { timing: "day_1", type: "execution", players: ["B"] },
        { timing: "night_3", type: "resurrection", players: ["B"] },
      ],
      claims: [],
    };

    expect(await buildFromDoc(baseDoc, backend).solveAll()).toHaveLength(1);
    expect(
      await buildFromDoc(
        {
          ...baseDoc,
          claims: [{ type: "Courtier", name: "C", timing: "night_2", role: "Shabaloth", drunkTimings: ["night_3"] }],
        },
        backend,
      ).solveAll(),
    ).toEqual([]);
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
  test("Evil Twin in play requires a good player to claim knowledge", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Evil Twin", "Imp", "Soldier"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Evil Twin"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Soldier"] },
          ],
        }),
        claims: [{ type: "Soldier", name: "C" }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("any good claimant can claim knowledge of an Evil Twin", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Evil Twin", "Imp", "Soldier"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Evil Twin"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Soldier"] },
          ],
        }),
        claims: [{ type: "Soldier", name: "C", knownEvilTwin: "A" }],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
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

  test("Chambermaid counts a Gambler waking on the second night", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Chambermaid", "Gambler", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chambermaid"] },
            { name: "B", roles: ["Gambler"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        claims: [
          {
            type: "Chambermaid",
            name: "A",
            checks: [{ left: "B", right: "C", timing: "night_2", count: 1 }],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });
  test("the first player to choose the Goon becomes drunk until dusk", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Chambermaid", "Goon", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chambermaid"] },
            { name: "B", roles: ["Goon"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        claims: [
          {
            type: "Chambermaid",
            name: "A",
            checks: [{ left: "B", right: "C", timing: "night_1", count: 0 }],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isDrunk("A", "night_1")).toBe(true);
    expect(worlds[0]?.isDrunk("A", "day_1")).toBe(true);
    expect(worlds[0]?.isDrunk("A", "night_2")).toBe(false);
  });
  test("a Demon cannot kill the Goon unless another ability chose the Goon first", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Sailor", "Goon", "Shabaloth", "Chef"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Sailor"] },
          { name: "B", roles: ["Goon"] },
          { name: "C", roles: ["Shabaloth"] },
          { name: "D", roles: ["Chef"] },
        ],
      }),
      timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
      claims: [],
    };

    expect(await buildFromDoc(baseDoc, backend).solveAll()).toEqual([]);

    const worlds = await buildFromDoc(
      {
        ...baseDoc,
        claims: [
          {
            type: "Sailor",
            name: "A",
            choices: [{ player: "B", timing: "night_2" }],
            possibleActualRoles: ["Sailor"],
          },
        ],
      },
      backend,
    ).solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isDrunk("A", "night_2")).toBe(true);
  });
  test("only the first nightly choice of the Goon makes its chooser drunk", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Chambermaid", "Goon", "Devil's Advocate", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chambermaid"] },
            { name: "B", roles: ["Goon"] },
            { name: "C", roles: ["Devil's Advocate"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        claims: [
          {
            type: "Chambermaid",
            name: "A",
            checks: [{ left: "B", right: "D", timing: "night_2", count: 1 }],
          },
          {
            type: "Devil's Advocate",
            name: "C",
            choices: [{ player: "B", timing: "night_2" }],
            possibleActualRoles: ["Devil's Advocate"],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isDrunk("C", "night_2")).toBe(true);
    expect(worlds[0]?.isDrunk("A", "night_2")).toBe(false);
  });
  test("an evil chooser turns the Goon evil for later alignment checks", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Moonchild", "Goon", "Devil's Advocate", "Chef"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Moonchild"] },
          { name: "B", roles: ["Goon"] },
          { name: "C", roles: ["Devil's Advocate"] },
          { name: "D", roles: ["Chef"] },
        ],
      }),
      timeline: [
        { timing: "day_1", type: "execution", players: ["A"] },
        { timing: "night_2", type: "nightDeath", players: ["B"] },
      ],
      claims: [
        { type: "Moonchild", name: "A", chosen: "B", timing: "day_1" },
        {
          type: "Devil's Advocate",
          name: "C",
          choices: [{ player: "D", timing: "night_1" }],
          possibleActualRoles: ["Devil's Advocate"],
        },
      ],
    };

    expect(await buildFromDoc(baseDoc, backend).solveAll()).toHaveLength(1);
    expect(
      await buildFromDoc(
        {
          ...baseDoc,
          claims: baseDoc.claims.map((claim) =>
            claim.type === "Devil's Advocate" ? { ...claim, choices: [{ player: "B", timing: "night_1" }] } : claim,
          ),
        },
        backend,
      ).solveAll(),
    ).toEqual([]);
  });
  test("an evil Goon may lie in later claims", async () => {
    const game = buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Devil's Advocate", "Goon", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Devil's Advocate"] },
            { name: "B", roles: ["Goon"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        claims: [
          {
            type: "Devil's Advocate",
            name: "A",
            choices: [{ player: "B", timing: "night_1" }],
            possibleActualRoles: ["Devil's Advocate"],
          },
          { type: "Chef", name: "B", count: 0 },
        ],
      },
      backend,
    );
    game.addInfoClaim({
      player: "B",
      role: "Goon",
      timing: "day_1",
      learned: game.constantBool(false, "evil_goon_lie"),
    });

    const worlds = await game.solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("B")).toBe("Goon");
    expect(worlds[0]?.apparent.get("B")).toBe("Chef");
    expect(worlds[0]?.isDrunk("A", "night_1")).toBe(true);
  });
  test("only an evil Goon can make an ordinary changed-role claim", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Devil's Advocate", "Goon", "Artist", "Imp"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Devil's Advocate"] },
          { name: "B", roles: ["Goon"] },
          { name: "C", roles: ["Artist"] },
          { name: "D", roles: ["Imp"] },
        ],
      }),
      claims: [
        { type: "Goon", name: "B", timing: "night_1", possibleActualRoles: ["Goon"] },
        {
          type: "Artist",
          name: "B",
          timing: "day_1",
          possibleActualRoles: ["Goon"],
        },
      ],
    };

    const goodGoonWorlds = await buildFromDoc(
      {
        ...baseDoc,
        claims: [
          {
            type: "Devil's Advocate",
            name: "A",
            choices: [{ player: "C", timing: "night_1" }],
            possibleActualRoles: ["Devil's Advocate"],
          },
          ...baseDoc.claims,
        ],
      },
      backend,
    ).solveAll();
    expect(goodGoonWorlds).toEqual([]);

    const evilGoonWorlds = await buildFromDoc(
      {
        ...baseDoc,
        claims: [
          {
            type: "Devil's Advocate",
            name: "A",
            choices: [{ player: "B", timing: "night_1" }],
            possibleActualRoles: ["Devil's Advocate"],
          },
          ...baseDoc.claims,
        ],
      },
      backend,
    ).solveAll();

    expect(evilGoonWorlds).toHaveLength(1);
  });
  test("a good Goon stays honest while the good chooser is drunk", async () => {
    const doc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Chambermaid", "Goon", "Chef", "Imp"],
      setup: "none",
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Chambermaid"] },
          { name: "B", roles: ["Goon"] },
          { name: "C", roles: ["Chef"] },
          { name: "D", roles: ["Imp"] },
        ],
      }),
      claims: [
        {
          type: "Chambermaid",
          name: "A",
          checks: [{ left: "B", right: "C", timing: "night_1", count: 0 }],
          possibleActualRoles: ["Chambermaid"],
        },
        { type: "Chef", name: "B", count: 0 },
      ],
    };
    const lyingGame = buildFromDoc(doc, backend);
    lyingGame.addInfoClaim({
      player: "B",
      role: "Goon",
      timing: "day_1",
      learned: lyingGame.constantBool(false, "good_goon_lie"),
    });
    expect(await lyingGame.solveAll()).toEqual([]);

    const honestGame = buildFromDoc(doc, backend);
    honestGame.addInfoClaim({
      player: "B",
      role: "Goon",
      timing: "day_1",
      learned: honestGame.constantBool(true, "good_goon_truth"),
    });
    const worlds = await honestGame.solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("B")).toBe("Goon");
    expect(worlds[0]?.apparent.get("B")).toBe("Chef");
    expect(worlds[0]?.isDrunk("A", "night_1")).toBe(true);
    expect(worlds[0]?.isDrunk("A", "day_1")).toBe(true);
  });
  test("Chambermaid stops counting a Seamstress after they use their ability", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Chambermaid", "Seamstress", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chambermaid"] },
            { name: "B", roles: ["Seamstress"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        claims: [
          {
            type: "Chambermaid",
            name: "A",
            checks: [
              { left: "B", right: "C", timing: "night_2", count: 1 },
              { left: "B", right: "C", timing: "night_3", count: 0 },
            ],
          },
          {
            type: "Seamstress",
            name: "B",
            timing: "night_2",
            among: ["C", "D"],
            aligned: false,
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });
  test("Chambermaid does not count a Demon chosen by the Exorcist", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Chambermaid", "Exorcist", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Chambermaid"] },
            { name: "B", roles: ["Exorcist"] },
            { name: "C", roles: ["Imp"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        claims: [
          {
            type: "Chambermaid",
            name: "A",
            checks: [{ left: "B", right: "C", timing: "night_2", count: 1 }],
          },
          { type: "Exorcist", name: "B", choices: [{ timing: "night_2", player: "C" }] },
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
  test("an executed Gossip has no ability when the statement would resolve", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B"],
        script: ["Gossip", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Gossip"] },
            { name: "B", roles: ["Chef"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["A"] },
          { timing: "night_2", type: "nightDeath", players: [] },
        ],
        claims: [
          {
            type: "Gossip",
            name: "A",
            statements: [{ timing: "day_1", expression: "B.role == Chef" }],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });
  test("a Professor resurrection occurs after the Gossip ability would resolve", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Gossip", "Professor", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Gossip"] },
            { name: "B", roles: ["Professor"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["A"] },
          { timing: "night_2", type: "nightDeath", players: [] },
          { timing: "night_2", type: "resurrection", players: ["A"] },
        ],
        claims: [
          {
            type: "Gossip",
            name: "A",
            statements: [{ timing: "day_1", expression: "C.role == Chef" }],
          },
          { type: "Professor", name: "B", timing: "night_2", target: "A" },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });
  test("a Gossip killed before their night-order position does not cause another death", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Gossip", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Gossip"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
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

    expect(worlds).toHaveLength(1);
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
  test("Flowergirl remembers a Demon vote across same-night succession", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Flowergirl", "Imp", "Scarlet Woman", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Flowergirl"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Scarlet Woman"] },
            { name: "D", roles: ["Chef"] },
            { name: "E", roles: ["Empath"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [
          {
            type: "Flowergirl",
            name: "A",
            votes: [{ timing: "night_2", voters: ["B"], demonVoted: false }],
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

  test("night death sources distinguish Leviathan from a charged Po", async () => {
    const leviathanWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Leviathan", "Chef", "Empath", "Steward", "Knight"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Leviathan"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Steward"] },
            { name: "E", roles: ["Knight"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const poWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Po", "Chef", "Empath", "Steward", "Knight"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Po"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Steward"] },
            { name: "E", roles: ["Knight"] },
          ],
        }),
        timeline: [{ timing: "night_3", type: "nightDeath", players: ["B", "C", "D"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const unchargedPoWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Po", "Chef", "Empath", "Steward"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Po"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Steward"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["B", "C"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(leviathanWorlds).toEqual([]);
    expect(poWorlds).toHaveLength(1);
    expect(unchargedPoWorlds).toEqual([]);
  });
  test("a charged Po may target a player who died earlier that night", async () => {
    const base = {
      players: ["A", "B", "C", "D", "E"],
      script: ["Po", "Chef", "Empath", "Gambler", "Steward"],
      setup: "none" as const,
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Po"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Empath"] },
          { name: "D", roles: ["Gambler"] },
          { name: "E", roles: ["Steward"] },
        ],
      }),
      timeline: [
        { timing: "night_2", type: "nightDeath" as const, players: [] },
        { timing: "night_3", type: "nightDeath" as const, players: ["B", "C", "D"] },
      ],
      claims: [
        {
          type: "Gambler" as const,
          name: "D",
          guesses: [{ timing: "night_3", player: "B", role: "Empath" }],
        },
      ],
    };
    const shortPoWorlds = await buildFromDoc(base, backend).solveAll();
    const protectedThirdTargetWorlds = await buildFromDoc(
      {
        ...base,
        script: [...base.script, "Soldier"],
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Po"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Gambler"] },
            { name: "E", roles: ["Soldier"] },
          ],
        }),
      },
      backend,
    ).solveAll();

    expect(shortPoWorlds).toHaveLength(1);
    expect(protectedThirdTargetWorlds).toHaveLength(1);
  });
  test("a Po can target an already-dead player without charging", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Po", "Chef", "Empath", "Steward"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Po"] },
            { name: "B", roles: ["Chef"] },
            { name: "C", roles: ["Empath"] },
            { name: "D", roles: ["Steward"] },
          ],
        }),
        timeline: [
          { timing: "day_1", type: "execution", players: ["B"] },
          { timing: "night_2", type: "nightDeath", players: [] },
          { timing: "night_3", type: "nightDeath", players: ["C"] },
        ],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });
  test("a Demon may sink a kill into a dead player, but not an unprotected living player", async () => {
    const base = {
      players: ["A", "B", "C"],
      script: ["Imp", "Chef", "Empath"],
      setup: "none" as const,
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Imp"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Empath"] },
        ],
      }),
      claims: [],
    };
    const deadTargetWorlds = await buildFromDoc(
      {
        ...base,
        timeline: [
          { timing: "day_1", type: "execution" as const, players: ["B"] },
          { timing: "night_2", type: "nightDeath" as const, players: [] },
        ],
      },
      backend,
    ).solveAll();
    const noTargetWorlds = await buildFromDoc(
      {
        ...base,
        timeline: [{ timing: "night_2", type: "nightDeath" as const, players: [] }],
      },
      backend,
    ).solveAll();

    expect(deadTargetWorlds).toHaveLength(1);
    expect(noTargetWorlds).toEqual([]);
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
        claims: [
          {
            type: "Devil's Advocate",
            name: "B",
            choices: [{ player: "A", timing: "night_1" }],
            possibleActualRoles: ["Devil's Advocate"],
          },
        ],
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
        players: ["A", "B", "C", "D", "E"],
        script: ["Po", "Scarlet Woman", "Chef", "Empath", "Steward"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Po"] },
            { name: "B", roles: ["Scarlet Woman"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Empath"] },
            { name: "E", roles: ["Steward"] },
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
        players: ["A", "B", "C", "D", "E"],
        script: ["Imp", "Scarlet Woman", "Chef", "Empath", "Steward"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Scarlet Woman"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Empath"] },
            { name: "E", roles: ["Steward"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "slayerShot", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const witchCurseWithCatchWorlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Imp", "Scarlet Woman", "Witch", "Chef", "Empath", "Steward"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Imp"] },
            { name: "B", roles: ["Scarlet Woman"] },
            { name: "C", roles: ["Witch"] },
            { name: "D", roles: ["Chef"] },
            { name: "E", roles: ["Empath"] },
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
  test("a healthy Mastermind keeps the game going for the extra night and day after an executed Demon", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D", "E"],
      script: ["Chambermaid", "Mastermind", "Imp", "Chef", "Empath"],
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Chambermaid"] },
          { name: "B", roles: ["Mastermind"] },
          { name: "C", roles: ["Imp"] },
          { name: "D", roles: ["Chef"] },
          { name: "E", roles: ["Empath"] },
        ],
      }),
      timeline: [{ timing: "day_1", type: "execution", players: ["C"] }],
      claims: [
        {
          type: "Chambermaid",
          name: "A",
          checks: [{ left: "D", right: "E", count: 1, timing: "night_2" }],
        },
      ],
    };

    expect(await buildFromDoc(baseDoc, backend).solveAll()).toHaveLength(1);
    expect(
      await buildFromDoc(
        {
          ...baseDoc,
          timeline: [...(baseDoc.timeline ?? []), { timing: "day_2", type: "survivedExecution", players: ["D"] }],
        },
        backend,
      ).solveAll(),
    ).toEqual([]);
  });
  test("a drunk Mastermind cannot extend the game after the Demon is executed", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D", "E"],
        script: ["Courtier", "Mastermind", "Imp", "Chef", "Empath"],
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Courtier"] },
            { name: "B", roles: ["Mastermind"] },
            { name: "C", roles: ["Imp"] },
            { name: "D", roles: ["Chef"] },
            { name: "E", roles: ["Empath"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "execution", players: ["C"] }],
        claims: [{ type: "Courtier", name: "A", timing: "night_1", role: "Mastermind", drunkTimings: ["night_1"] }],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });
  test("a drunk Zombuul dies for real on its first apparent death", async () => {
    const baseDoc: TestPuzzleDoc = {
      players: ["A", "B", "C", "D", "E"],
      script: ["Zombuul", "Courtier", "Goblin", "Chef", "Empath"],
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Zombuul"] },
          { name: "B", roles: ["Courtier"] },
          { name: "C", roles: ["Goblin"] },
          { name: "D", roles: ["Chef"] },
          { name: "E", roles: ["Empath"] },
        ],
      }),
      timeline: [{ timing: "day_1", type: "execution", players: ["A"] }],
      claims: [],
    };

    expect(await buildFromDoc(baseDoc, backend).solveAll()).toHaveLength(1);
    expect(
      await buildFromDoc(
        {
          ...baseDoc,
          claims: [{ type: "Courtier", name: "B", timing: "night_1", role: "Zombuul", drunkTimings: ["night_1"] }],
        },
        backend,
      ).solveAll(),
    ).toEqual([]);
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
  test("Sage information allows a Recluse to register as the Demon", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Sage", "Recluse", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Sage"] },
            { name: "B", roles: ["Recluse"] },
            { name: "C", roles: ["Chef"] },
            { name: "D", roles: ["Imp"] },
          ],
        }),
        claims: [{ type: "Sage", name: "A", timing: "night_2", demonAmong: ["B", "C"] }],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
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
        script: ["Gambler", "Drunk", "Chef", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Drunk"] },
            { name: "B", roles: ["Gambler"] },
            { name: "C", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [{ type: "Gambler", name: "A", guesses: [{ timing: "night_2", player: "B", role: "Imp" }] }],
      },
      backend,
    ).solveAll();
    expect(acrobatWorlds).toEqual([]);
    expect(gamblerWorlds).toEqual([]);
  });
  test("Gambler outcomes are inferred from observed night deaths", async () => {
    const base = {
      players: ["A", "B"],
      script: ["Gambler", "Chef", "Empath"],
      setup: "none" as const,
      uniqueCharacters: true,
      roleConstraints: roleConstraints({
        possible: [
          { name: "A", roles: ["Gambler"] },
          { name: "B", roles: ["Chef"] },
        ],
      }),
      timeline: [{ timing: "night_2", type: "nightDeath" as const, players: [] }],
    };
    const correctGuessWorlds = await buildFromDoc(
      {
        ...base,
        claims: [{ type: "Gambler", name: "A", guesses: [{ timing: "night_2", player: "B", role: "Chef" }] }],
      },
      backend,
    ).solveAll();
    const wrongGuessWorlds = await buildFromDoc(
      {
        ...base,
        claims: [{ type: "Gambler", name: "A", guesses: [{ timing: "night_2", player: "B", role: "Empath" }] }],
      },
      backend,
    ).solveAll();

    expect(correctGuessWorlds).toHaveLength(1);
    expect(wrongGuessWorlds).toEqual([]);
  });
  test("a correct Gambler may die to a later Po attack", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C"],
        script: ["Gambler", "Professor", "Po"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Gambler"] },
            { name: "B", roles: ["Professor"] },
            { name: "C", roles: ["Po"] },
          ],
        }),
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [{ type: "Gambler", name: "A", guesses: [{ timing: "night_2", player: "B", role: "Professor" }] }],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
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
        players: ["A", "B", "C", "D", "E"],
        script: ["Slayer", "Imp", "Scarlet Woman", "Chef", "Empath"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Slayer"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Scarlet Woman"] },
            { name: "D", roles: ["Chef"] },
            { name: "E", roles: ["Empath"] },
          ],
        }),
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true }],
      },
      backend,
    ).solveAll();
    expect(noCatchWorlds).toEqual([]);
    expect(catchWorlds).toHaveLength(1);
  });
  test("Scarlet Woman cannot catch a slain Demon below five alive players", async () => {
    const worlds = await buildFromDoc(
      {
        players: ["A", "B", "C", "D"],
        script: ["Slayer", "Imp", "Scarlet Woman", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        roleConstraints: roleConstraints({
          possible: [
            { name: "A", roles: ["Slayer"] },
            { name: "B", roles: ["Imp"] },
            { name: "C", roles: ["Scarlet Woman"] },
            { name: "D", roles: ["Chef"] },
          ],
        }),
        timeline: [{ timing: "day_1", type: "slayerShot", caller: "A", players: ["B"] }],
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true }],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });
  test("Klutz claims require a healthy Klutz to choose good", async () => {
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
        claims: [{ type: "Klutz", name: "A", timing: "night_2", chosen: "B" }],
      },
      backend,
    ).solveAll();
    expect(worlds).toEqual([]);
  });
  test("Klutz claims can be disabled by poisoning", async () => {
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
        claims: [{ type: "Klutz", name: "A", timing: "night_2", chosen: "B" }],
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
  test("multiple Village Idiot worlds are deduplicated by actual roles", async () => {
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
    expect(worlds).toHaveLength(1);
    expect([worlds[0]?.isDrunk("A"), worlds[0]?.isDrunk("B")].filter(Boolean)).toHaveLength(1);
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
  test("a-clean-sweep uses Chambermaid info without asserting a Gambler outcome", async () => {
    const doc = loadDoc("a-clean-sweep.json");
    const bmrEvilRoles = ["Godfather", "Zombuul", "Pukka", "Shabaloth", "Po"];
    expect(doc.script).toEqual(expect.arrayContaining(bmrEvilRoles));
    expect(doc.claims.filter((claim) => bmrEvilRoles.includes(claim.type))).toEqual([]);
    expect(doc.script).not.toContain("Seamstress");
    expect(doc.script).not.toContain("Washerwoman");
    expect(doc.players).toHaveLength(9);
    expect(doc.setup).toBe("standard");
    expect(doc.constraints ?? []).toEqual([]);
    expect(doc.claims).toHaveLength(9);
    expect(doc.claims.some((claim) => claim.type === "Pacifist")).toBe(false);
    expect(doc.claims.some((claim) => ["Goon", "Lunatic", "Tinker", "Moonchild"].includes(claim.type))).toBe(true);
    expect(doc.timeline).toEqual([
      { timing: "day_1", type: "execution", players: ["Gia"] },
      { timing: "night_2", type: "nightDeath", players: [] },
      { timing: "day_2", type: "survivedExecution", players: ["Drew"] },
      { timing: "night_3", type: "nightDeath", players: ["Cora", "Finn", "Eve"] },
      { timing: "day_3", type: "execution", players: ["Iris"] },
      { timing: "night_4", type: "nightDeath", players: [] },
    ]);

    const worlds = await buildFromDoc(doc, backend).solveAll();

    expect(worlds).toHaveLength(1);
    const expectedRoles: Record<string, string> = {
      Ada: "Godfather",
      Cora: "Moonchild",
      Drew: "Sailor",
      Eve: "Gambler",
      Finn: "Gossip",
      Gia: "Tinker",
      Hugo: "Pukka",
      Iris: "Goon",
      You: "Chambermaid",
    };
    for (const [player, role] of Object.entries(expectedRoles)) expect(worlds[0]?.actualRole(player)).toBe(role);
    expect(worlds[0]?.apparent.get("Ada")).toBe("Exorcist");
    expect(worlds[0]?.apparent.get("Iris")).toBe("Minstrel");
    expect(new Set(doc.claims.map((claim) => claim.type)).size).toBe(doc.claims.length);
    expect(doc.claims.filter((claim) => claim.type === "Sailor")).toEqual([
      {
        type: "Sailor",
        name: "Drew",
        choices: [
          { player: "Ada", timing: "night_1" },
          { player: "Eve", timing: "night_2" },
          { player: "Hugo", timing: "night_3" },
          { player: "Hugo", timing: "night_4" },
        ],
      },
    ]);
    expect(doc.claims.filter((claim) => claim.type === "Exorcist")).toEqual([
      {
        type: "Exorcist",
        name: "Ada",
        choices: [
          { player: "Drew", timing: "night_2" },
          { player: "Hugo", timing: "night_3" },
          { player: "Drew", timing: "night_4" },
        ],
      },
    ]);
    expect(doc.claims.filter((claim) => claim.type === "Chambermaid")).toEqual([
      {
        type: "Chambermaid",
        name: "You",
        possibleActualRoles: ["Chambermaid"],
        checks: [
          { left: "Ada", right: "Hugo", count: 2, timing: "night_1" },
          { left: "Cora", right: "Hugo", count: 1, timing: "night_2" },
          { left: "Hugo", right: "Finn", count: 1, timing: "night_3" },
          { left: "Hugo", right: "Ada", count: 2, timing: "night_4" },
        ],
      },
    ]);
    expect(doc.claims).toContainEqual({
      type: "Gambler",
      name: "Eve",
      guesses: [
        { player: "Hugo", role: "Professor", timing: "night_2" },
        { player: "Hugo", role: "Professor", timing: "night_3" },
      ],
    });
    expect(doc.claims).toContainEqual({ type: "Minstrel", name: "Iris" });
    expect(doc.claims).toContainEqual({
      type: "Gossip",
      name: "Finn",
      statements: [
        { expression: "some Pukka.~role" },
        { timing: "day_2", expression: "some Pukka.~role" },
        { timing: "day_3", expression: "some Pukka.~role" },
      ],
    });

    expect(doc.claims.filter((claim) => claim.possibleActualRoles !== undefined)).toEqual([
      expect.objectContaining({ name: "You", possibleActualRoles: ["Chambermaid"] }),
    ]);
  }, 60_000);
});
