import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

// On night X, the Xaan poisons all Townsfolk until dusk. X is the Outsider count.
// The poison stops when the Xaan loses the Xaan ability.
// https://wiki.bloodontheclocktower.com/index.php?title=Xaan&oldid=3082
// The names keep this seating: Imp, Xaan, Saint, Butler, Empath, Chef.
function scenario(victim: number, empathCount: number, names = ["A", "B", "C", "D", "E", "F"]) {
  const [imp, xaan, saint, butler, empath, chef] = names as [string, string, string, string, string, string];
  return {
    players: names,
    script: ["Imp", "Xaan", "Saint", "Butler", "Empath", "Chef"],
    setup: "none",
    timeline: [{ type: "nightDeath", timing: "night_2", players: [names[victim] as string] }],
    claims: [
      { type: "Imp", name: imp, possibleActualRoles: ["Imp"] },
      { type: "Xaan", name: xaan, possibleActualRoles: ["Xaan"] },
      { type: "Saint", name: saint, possibleActualRoles: ["Saint"] },
      { type: "Butler", name: butler, possibleActualRoles: ["Butler"] },
      { type: "Empath", name: empath, possibleActualRoles: ["Empath"], timing: "night_2", count: empathCount },
      { type: "Chef", name: chef, possibleActualRoles: ["Chef"] },
    ],
  };
}

async function worldCount(doc: unknown): Promise<number> {
  return (await buildFromDoc(validatePuzzleDoc(doc), backend).solveAll()).length;
}

const CHEF = 5;
const XAAN = 1;
const IMP = 0;

test("a living Xaan lets a Townsfolk get false information on night X", async () => {
  // The Chef dies. The living neighbors of the Empath are the Butler and the Imp.
  expect(await worldCount(scenario(CHEF, 1))).toBe(1);
  expect(await worldCount(scenario(CHEF, 0))).toBe(1);
});

test("the Xaan poison stops when the Demon kills the Xaan on night X", async () => {
  // The Xaan dies. The living neighbors of the Empath are the Butler and the Chef.
  expect(await worldCount(scenario(XAAN, 0))).toBe(1);
  expect(await worldCount(scenario(XAAN, 1))).toBe(0);
});

test("the Xaan poison stops when the Xaan becomes the Imp on night X", async () => {
  // The Imp kills itself. The Xaan becomes the Imp and is not a neighbor of the Empath.
  expect(await worldCount(scenario(IMP, 0))).toBe(1);
  expect(await worldCount(scenario(IMP, 1))).toBe(0);
});

test("the Xaan death timing does not change with new names, duplicate reports, or redundant facts", async () => {
  const names = ["Uma", "Vic", "Wes", "Xena", "Yan", "Zoe"];
  expect(await worldCount(scenario(XAAN, 0, names))).toBe(1);
  expect(await worldCount(scenario(XAAN, 1, names))).toBe(0);

  for (const count of [0, 1]) {
    const doc = scenario(XAAN, count);
    doc.timeline.push({ ...doc.timeline[0]! });
    const facts = [{ kind: "fact", expression: "B.initial_role == Xaan && #Outsider.~initial_type = 2" }];
    expect(await worldCount({ ...doc, constraints: facts })).toBe(count === 0 ? 1 : 0);
  }
});
