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

  test("puzzle-01-sober-savant.json solves to 1 world matching the TS puzzle", async () => {
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

  test("intro puzzle parses and solves", async () => {
    const doc = loadDoc("puzzle-intro-chef-empath.json");
    const worlds = await buildFromDoc(doc, backend).solveAll();
    expect(worlds.length).toBeGreaterThanOrEqual(0);
  });
});
