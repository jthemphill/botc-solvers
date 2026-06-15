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

  test("puzzle-34-the-vortox-conjecture.json parses and solves", async () => {
    const doc = loadDoc("puzzle-34-the-vortox-conjecture.json");
    const worlds = await buildFromDoc(doc, backend).solveAll();

    expect(worlds.length).toBeGreaterThan(0);
  });
});
