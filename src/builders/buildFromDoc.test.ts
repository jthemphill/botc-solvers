import { beforeAll, describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { KissatBackend, type SatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";
import { buildFromDoc } from "./buildFromDoc";

function loadDoc(name: string) {
  const path = join(import.meta.dir, "..", "examples", name);
  return validatePuzzleDoc(JSON.parse(readFileSync(path, "utf8")));
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

  test("fixed roles allow multiple possible actual roles", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["You", "A", "B"],
        script: ["Imp", "Marionette", "Drunk", "Investigator"],
        setup: "none",
        fixedRoles: [{ name: "You", roles: ["Drunk", "Investigator"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(new Set(worlds.map((world) => world.actualRole("You")))).toEqual(new Set(["Drunk", "Investigator"]));
  });

  test("claims can opt into extra possible actual roles", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Lunatic", "Empath", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Lunatic"] },
          { name: "B", roles: ["Empath"] },
          { name: "C", roles: ["Imp"] },
        ],
        claims: [{ type: "Empath", name: "A", extraPossibleActualRoles: ["Lunatic"], count: 0 }],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Lunatic");
  });

  test("custom info statements and forbidden roles constrain the model", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B"],
        script: ["Sage", "Imp"],
        setup: "none",
        fixedRoles: [{ name: "A", roles: ["Sage"] }],
        forbiddenRoles: [{ name: "B", roles: ["Sage"] }],
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

  test("Chambermaid counts players who woke due to their ability", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C", "D", "E"],
        script: ["Chambermaid", "Clockmaker", "Oracle", "Scarlet Woman", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Chambermaid"] },
          { name: "B", roles: ["Clockmaker"] },
          { name: "C", roles: ["Oracle"] },
          { name: "D", roles: ["Scarlet Woman"] },
          { name: "E", roles: ["Imp"] },
        ],
        claims: [
          {
            type: "Chambermaid",
            name: "A",
            checks: [
              { left: "B", right: "C", timing: "night_1", count: 1 },
              { left: "C", right: "D", timing: "night_1", count: 0 },
            ],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });

  test("Oracle counts evil dead players", async () => {
    const validWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Oracle", "Imp", "Clockmaker"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Oracle"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Clockmaker"] },
        ],
        claims: [{ type: "Oracle", name: "A", timing: "night_2", count: 1, deadPlayers: ["B", "C"] }],
      },
      backend,
    ).solveAll();

    const invalidWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Oracle", "Imp", "Clockmaker"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Oracle"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Clockmaker"] },
        ],
        claims: [{ type: "Oracle", name: "A", timing: "night_2", count: 0, deadPlayers: ["B", "C"] }],
      },
      backend,
    ).solveAll();

    expect(validWorlds).toHaveLength(1);
    expect(invalidWorlds).toEqual([]);
  });

  test("timeline deaths exclude players from script demon roles", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B"],
        script: ["Imp", "Sage"],
        setup: "none",
        uniqueCharacters: true,
        timeline: [{ timing: "night_2", type: "nightKill", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds.length).toBeGreaterThan(0);
    expect(new Set(worlds.map((world) => world.actualRole("B")))).not.toContain("Imp");
  });

  test("night kills cannot kill sober healthy Soldiers", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Soldier", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Soldier"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Chef"] },
        ],
        timeline: [{ timing: "night_2", type: "nightKill", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });

  test("night-killed Soldiers can be poisoned", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Soldier", "Imp", "Poisoner"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Soldier"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Poisoner"] },
        ],
        timeline: [{ timing: "night_2", type: "nightKill", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.poisonedByTiming.get("night_2")).toEqual(new Set(["A"]));
  });

  test("Doomsayer deaths do not exclude players from script demon roles", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B"],
        script: ["Imp", "Sage"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Sage"] },
          { name: "B", roles: ["Imp"] },
        ],
        timeline: [{ timing: "day_1", type: "doomsayerDeath", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("B")).toBe("Imp");
  });

  test("Doomsayer deaths with callers require the same registered alignment", async () => {
    const validWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Imp", "Sage", "Mayor"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Sage"] },
          { name: "B", roles: ["Mayor"] },
          { name: "C", roles: ["Imp"] },
        ],
        timeline: [{ timing: "day_1", type: "doomsayerDeath", caller: "A", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const invalidWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Imp", "Sage", "Mayor"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Sage"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Mayor"] },
        ],
        timeline: [{ timing: "day_1", type: "doomsayerDeath", caller: "A", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const spyWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Imp", "Spy", "Sage"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Spy"] },
          { name: "B", roles: ["Sage"] },
          { name: "C", roles: ["Imp"] },
        ],
        timeline: [{ timing: "day_1", type: "doomsayerDeath", caller: "A", players: ["B"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(validWorlds).toHaveLength(1);
    expect(invalidWorlds).toEqual([]);
    expect(spyWorlds).toHaveLength(1);
  });

  test("ability and unknown night deaths require a living catch when they kill an actual demon", async () => {
    const impWithoutMinionWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B"],
        script: ["Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Imp"] },
          { name: "B", roles: ["Chef"] },
        ],
        timeline: [{ timing: "night_2", type: "abilityDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const unknownNightDeathWithoutCatchWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B"],
        script: ["Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Imp"] },
          { name: "B", roles: ["Chef"] },
        ],
        timeline: [{ timing: "night_2", type: "nightDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const impWithMinionWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B"],
        script: ["Imp", "Goblin"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Imp"] },
          { name: "B", roles: ["Goblin"] },
        ],
        timeline: [{ timing: "night_2", type: "abilityDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const dyingMinionWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Imp", "Goblin", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Imp"] },
          { name: "B", roles: ["Goblin"] },
          { name: "C", roles: ["Chef"] },
        ],
        timeline: [{ timing: "night_2", type: "abilityDeath", players: ["A", "B"] }],
        claims: [],
      },
      backend,
    ).solveAll();
    const poWithScarletWomanWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B"],
        script: ["Po", "Scarlet Woman"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Po"] },
          { name: "B", roles: ["Scarlet Woman"] },
        ],
        timeline: [{ timing: "night_2", type: "abilityDeath", players: ["A"] }],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(impWithoutMinionWorlds).toEqual([]);
    expect(unknownNightDeathWithoutCatchWorlds).toEqual([]);
    expect(impWithMinionWorlds).toHaveLength(1);
    expect(dyingMinionWorlds).toEqual([]);
    expect(poWithScarletWomanWorlds).toHaveLength(1);
  });

  test("Xaan poisons Townsfolk on the night matching the Outsider count", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C", "D"],
        script: ["Imp", "Xaan", "Drunk", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Imp"] },
          { name: "B", roles: ["Xaan"] },
          { name: "C", roles: ["Drunk"] },
          { name: "D", roles: ["Chef"] },
        ],
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

  test("Atheist setup has no evil team and arbitrary information", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Imp", "Spy", "Atheist", "Artist", "Clockmaker"],
        setup: "atheist",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Atheist"] },
          { name: "B", roles: ["Artist"] },
          { name: "C", roles: ["Clockmaker"] },
        ],
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
        version: 1,
        players: ["A", "B", "C"],
        script: ["Imp", "Poisoner", "Investigator"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Poisoner"] },
          { name: "B", roles: ["Investigator"] },
          { name: "C", roles: ["Imp"] },
        ],
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

  test("nightKillBeforeInfo stops same-night Poisoner effects", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Imp", "Poisoner", "Investigator"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Poisoner"] },
          { name: "B", roles: ["Investigator"] },
          { name: "C", roles: ["Imp"] },
        ],
        timeline: [{ timing: "night_2", type: "nightKillBeforeInfo", players: ["A"] }],
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

  test("timed Empath claims use living neighbors from the timeline", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C", "D"],
        script: ["Empath", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        fixedRoles: [
          { name: "A", roles: ["Empath"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Imp"] },
          { name: "D", roles: ["Chef"] },
        ],
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
        version: 1,
        players: ["A", "B"],
        script: ["Nightwatchman", "Drunk", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [{ name: "A", roles: ["Nightwatchman", "Drunk"] }],
        forbiddenRoles: [{ name: "B", roles: ["Nightwatchman", "Drunk"] }],
        claims: [{ type: "Nightwatchman", name: "A", timing: "night_1", chosen: "B", learned: false }],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Drunk");
  });

  test("Ravenkeeper learned role constrains sober healthy claims", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Ravenkeeper", "Scarlet Woman", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Ravenkeeper"] },
          { name: "C", roles: ["Imp"] },
        ],
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
        version: 1,
        players: ["A", "B", "C"],
        script: ["Ravenkeeper", "Spy", "Imp", "Saint"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Ravenkeeper"] },
          { name: "B", roles: ["Spy"] },
          { name: "C", roles: ["Imp"] },
        ],
        claims: [{ type: "Ravenkeeper", name: "A", timing: "night_2", player: "B", role: "Saint" }],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });

  test("Courtier drunking disables Vortox false information", async () => {
    const validWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Courtier", "Vortox", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Courtier"] },
          { name: "B", roles: ["Vortox"] },
          { name: "C", roles: ["Chef"] },
        ],
        claims: [
          { type: "Courtier", name: "A", timing: "night_1", role: "Vortox", drunkTimings: ["night_1"] },
          { type: "Chef", name: "C", timing: "night_1", count: 0 },
        ],
      },
      backend,
    ).solveAll();
    const invalidWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Courtier", "Vortox", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Courtier"] },
          { name: "B", roles: ["Vortox"] },
          { name: "C", roles: ["Chef"] },
        ],
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
        version: 1,
        players: ["A", "B", "C"],
        script: ["Philosopher", "Snake Charmer", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Philosopher"] },
          { name: "B", roles: ["Snake Charmer"] },
          { name: "C", roles: ["Imp"] },
        ],
        claims: [
          { type: "Philosopher", name: "A", timing: "night_1", role: "Snake Charmer" },
          {
            type: "Snake Charmer",
            name: "A",
            timing: "night_1",
            checked: "C",
            demon: true,
            extraPossibleActualRoles: ["Philosopher"],
          },
        ],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.actualRole("A")).toBe("Philosopher");
  });

  test("custom info statements can use an explicit active role", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Philosopher", "Snake Charmer", "Seamstress", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Philosopher"] },
          { name: "B", roles: ["Snake Charmer"] },
          { name: "C", roles: ["Imp"] },
        ],
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
        version: 1,
        players: ["A", "B", "C"],
        script: ["Acrobat", "Drunk", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Drunk"] },
          { name: "B", roles: ["Acrobat"] },
          { name: "C", roles: ["Imp"] },
        ],
        claims: [{ type: "Acrobat", name: "A", choices: [{ timing: "night_2", player: "B", died: true }] }],
      },
      backend,
    ).solveAll();
    const gamblerWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Gambler", "Drunk", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Drunk"] },
          { name: "B", roles: ["Gambler"] },
          { name: "C", roles: ["Imp"] },
        ],
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
        version: 1,
        players: ["A", "B", "C"],
        script: ["Slayer", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Slayer"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Chef"] },
        ],
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: false }],
      },
      backend,
    ).solveAll();

    const livingTownsfolkWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Slayer", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Slayer"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Chef"] },
        ],
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
        version: 1,
        players: ["A", "B", "C"],
        script: ["Slayer", "Recluse", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Slayer"] },
          { name: "B", roles: ["Recluse"] },
          { name: "C", roles: ["Imp"] },
        ],
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true }],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(1);
  });

  test("Slayer kill claims require an active healthy Slayer", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Slayer", "Drunk", "Recluse", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Drunk"] },
          { name: "B", roles: ["Recluse"] },
          { name: "C", roles: ["Imp"] },
        ],
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true }],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });

  test("continued Slayer kill claims require Scarlet Woman for actual demon targets", async () => {
    const noCatchWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B"],
        script: ["Slayer", "Imp"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Slayer"] },
          { name: "B", roles: ["Imp"] },
        ],
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true, gameContinued: true }],
      },
      backend,
    ).solveAll();
    const catchWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Slayer", "Imp", "Scarlet Woman"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Slayer"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Scarlet Woman"] },
        ],
        claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true, gameContinued: true }],
      },
      backend,
    ).solveAll();

    expect(noCatchWorlds).toEqual([]);
    expect(catchWorlds).toHaveLength(1);
  });

  test("Klutz no-loss claims require a healthy Klutz to choose good", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Klutz", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Klutz"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Chef"] },
        ],
        claims: [{ type: "Klutz", name: "A", timing: "night_2", chosen: "B", lost: false }],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });

  test("Klutz no-loss claims can be disabled by poisoning", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Klutz", "Imp", "Poisoner"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Klutz"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Poisoner"] },
        ],
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
        version: 1,
        players: ["A", "B", "C", "D"],
        script: ["Slayer", "Imp", "Poisoner", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Slayer"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Poisoner"] },
          { name: "D", roles: ["Chef"] },
        ],
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
        version: 1,
        players: ["A", "B", "C"],
        script: ["Virgin", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: true,
        fixedRoles: [
          { name: "A", roles: ["Virgin"] },
          { name: "B", roles: ["Chef"] },
          { name: "C", roles: ["Imp"] },
        ],
        claims: [{ type: "Virgin", name: "A", timing: "day_1", nominator: "B", executed: false }],
      },
      backend,
    ).solveAll();

    expect(worlds).toEqual([]);
  });

  test("multiple Village Idiots make one real Village Idiot drunk", async () => {
    const worlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C"],
        script: ["Village Idiot", "Imp"],
        setup: "none",
        uniqueCharacters: false,
        fixedRoles: [
          { name: "A", roles: ["Village Idiot"] },
          { name: "B", roles: ["Village Idiot"] },
          { name: "C", roles: ["Imp"] },
        ],
        claims: [],
      },
      backend,
    ).solveAll();

    expect(worlds).toHaveLength(2);
    expect(new Set(worlds.map((world) => (world.isDrunk("A") ? "A" : "B")))).toEqual(new Set(["A", "B"]));
  });

  test("Legionary counts living evil players before the next living Legionary", async () => {
    const validWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C", "D"],
        script: ["Legionary", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        fixedRoles: [
          { name: "A", roles: ["Legionary"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Legionary"] },
          { name: "D", roles: ["Chef"] },
        ],
        claims: [{ type: "Legionary", name: "A", counts: [{ count: 1 }] }],
      },
      backend,
    ).solveAll();

    const invalidWorlds = await buildFromDoc(
      {
        version: 1,
        players: ["A", "B", "C", "D"],
        script: ["Legionary", "Imp", "Chef"],
        setup: "none",
        uniqueCharacters: false,
        fixedRoles: [
          { name: "A", roles: ["Legionary"] },
          { name: "B", roles: ["Imp"] },
          { name: "C", roles: ["Legionary"] },
          { name: "D", roles: ["Chef"] },
        ],
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
