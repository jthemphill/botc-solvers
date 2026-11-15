import { beforeAll, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

// A game with the Atheist has no evil characters.
// https://wiki.bloodontheclocktower.com/Atheist
function scenario(roles: readonly string[], names = ["A", "B", "C"]) {
  return {
    players: names,
    script: ["Imp", "Spy", "Atheist", "Chef", "Mayor"],
    setup: "none",
    claims: roles.map((type, index) => ({ type, name: names[index], possibleActualRoles: [type] })),
  };
}

async function worldCount(doc: unknown): Promise<number> {
  return (await buildFromDoc(validatePuzzleDoc(doc), backend).solveAll()).length;
}

test("the Atheist is not in play with an evil character", async () => {
  expect(await worldCount(scenario(["Atheist", "Chef", "Mayor"]))).toBe(1);
  expect(await worldCount(scenario(["Atheist", "Chef", "Imp"]))).toBe(0);
  expect(await worldCount(scenario(["Mayor", "Chef", "Imp"]))).toBe(1);
  expect(await worldCount(scenario(["Atheist", "Chef", "Imp"], ["Uma", "Vic", "Wes"]))).toBe(0);
});

test("an Atheist claimant in a standard game is evil or the Drunk", async () => {
  const doc = {
    players: ["A", "B", "C", "D", "E", "F"],
    script: ["Imp", "Spy", "Drunk", "Atheist", "Chef", "Mayor", "Soldier", "Slayer"],
    claims: ["Atheist", "Chef", "Mayor", "Soldier", "Slayer", "Chef"].map((type, index) => ({
      type,
      name: "ABCDEF"[index],
    })),
  };
  const worlds = await buildFromDoc(validatePuzzleDoc(doc), backend).solveAll();
  expect(worlds.length).toBeGreaterThan(0);
  expect(new Set(worlds.map((world) => world.actualRole("A")))).toEqual(new Set(["Imp", "Spy", "Drunk"]));
});

// Puzzle 30 has two games. One, and only one, has a genuine Atheist.
test("only the right game of puzzle 30 can be a game without the Atheist", async () => {
  const load = (side: string) =>
    JSON.parse(
      readFileSync(
        join(import.meta.dir, "..", "examples", `puzzle-30-the-babel-fish-is-a-dead-giveaway-${side}.json`),
        "utf8",
      ),
    );
  expect(await worldCount({ ...load("left"), setup: "standard" })).toBe(0);
  expect(await worldCount({ ...load("right"), setup: "standard" })).toBe(1);
});
