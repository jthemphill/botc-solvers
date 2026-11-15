import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

// Shared claim convention for the Mutant, from the puzzle images:
// a Mutant that is alive at the last phase claims a Townsfolk character with any information,
// and a dead Mutant claims the Mutant.
// The names keep this seating: Chef claimant, Imp, Empath, Juggler.
function scenario(chefCount: number, options: { dead?: boolean; names?: string[]; roles?: string[] } = {}) {
  const [chef, imp, empath, juggler] = options.names ?? ["A", "B", "C", "D"];
  return {
    players: [chef, imp, empath, juggler],
    script: ["Chef", "Imp", "Mutant", "Empath", "Juggler"],
    setup: "none",
    timeline: options.dead === true ? [{ type: "execution", timing: "day_1", players: [chef] }] : [],
    claims: [
      { type: "Chef", name: chef, count: chefCount, ...(options.roles ? { possibleActualRoles: options.roles } : {}) },
      { type: "Imp", name: imp, possibleActualRoles: ["Imp"] },
      { type: "Empath", name: empath, possibleActualRoles: ["Empath"] },
      { type: "Juggler", name: juggler, guesses: {}, possibleActualRoles: ["Juggler"] },
    ],
  };
}

async function chefClaimantRoles(doc: ReturnType<typeof scenario>): Promise<string[]> {
  const worlds = await buildFromDoc(validatePuzzleDoc(doc), backend).solveAll();
  return worlds.map((world) => world.actualRole(doc.players[0] as string)).sort();
}

test("a living Mutant can claim a Townsfolk character with false information", async () => {
  // No evil players sit together, so the correct Chef number is 0.
  expect(await chefClaimantRoles(scenario(1))).toEqual(["Mutant"]);
  expect(await chefClaimantRoles(scenario(0))).toEqual(["Chef", "Mutant"]);
});

test("a dead player that claims a Townsfolk character is not the Mutant", async () => {
  expect(await chefClaimantRoles(scenario(1, { dead: true }))).toEqual([]);
  expect(await chefClaimantRoles(scenario(0, { dead: true }))).toEqual(["Chef"]);
});

test("a list of possible characters replaces the Mutant convention", async () => {
  expect(await chefClaimantRoles(scenario(1, { dead: true, roles: ["Chef", "Mutant"] }))).toEqual(["Mutant"]);
  expect(await chefClaimantRoles(scenario(1, { roles: ["Chef", "Imp"] }))).toEqual([]);
});

test("the Mutant convention does not change with new names or a duplicate death report", async () => {
  const names = ["Uma", "Vic", "Wes", "Xena"];
  expect(await chefClaimantRoles(scenario(1, { names }))).toEqual(["Mutant"]);
  const dead = scenario(1, { names, dead: true });
  dead.timeline.push({ ...dead.timeline[0]! });
  expect(await chefClaimantRoles(dead)).toEqual([]);
});

// A Lunatic believes that it is the Demon. It claims a different character with any information.
test("a Lunatic can claim a different character with false information, alive or dead", async () => {
  for (const dead of [false, true]) {
    const doc = scenario(1, { dead });
    doc.script[2] = "Lunatic";
    expect(await chefClaimantRoles(doc)).toEqual(["Lunatic"]);
    const listed = scenario(1, { dead, roles: ["Chef", "Imp"] });
    listed.script[2] = "Lunatic";
    expect(await chefClaimantRoles(listed)).toEqual([]);
  }
});
