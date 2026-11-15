import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

// With a Vortox, a Dreamer learns two characters that the chosen player does not have.
// https://wiki.bloodontheclocktower.com/index.php?title=Vortox&oldid=3017
// The names keep this seating: Dreamer, Spy, Demon, Chef.
function scenario(demon: string, shown: readonly string[], names = ["A", "B", "C", "D"]) {
  const [dreamer, spy, demonPlayer, chef] = names as [string, string, string, string];
  return {
    players: names,
    script: ["Dreamer", "Spy", "Vortox", "Imp", "Chef", "Mayor"],
    setup: "none",
    claims: [
      {
        type: "Dreamer",
        name: dreamer,
        timing: "night_1",
        player: spy,
        roles: shown,
        possibleActualRoles: ["Dreamer"],
      },
      { type: "Spy", name: spy, possibleActualRoles: ["Spy"] },
      { type: demon, name: demonPlayer, possibleActualRoles: [demon] },
      { type: "Chef", name: chef, possibleActualRoles: ["Chef"] },
    ],
  };
}

async function worldCount(doc: ReturnType<typeof scenario>): Promise<number> {
  return (await buildFromDoc(validatePuzzleDoc(doc), backend).solveAll()).length;
}

test("a Dreamer with a Vortox does not learn the character of the chosen player", async () => {
  expect(await worldCount(scenario("Vortox", ["Mayor", "Imp"]))).toBe(1);
  expect(await worldCount(scenario("Vortox", ["Mayor", "Spy"]))).toBe(0);
});

test("a Dreamer without a Vortox can learn the Spy or a character that the Spy registers as", async () => {
  expect(await worldCount(scenario("Imp", ["Mayor", "Spy"]))).toBe(1);
  expect(await worldCount(scenario("Imp", ["Mayor", "Vortox"]))).toBe(1);
});

test("the Vortox Dreamer rule does not change with new names or a duplicate report", async () => {
  const names = ["Uma", "Vic", "Wes", "Xena"];
  expect(await worldCount(scenario("Vortox", ["Mayor", "Imp"], names))).toBe(1);
  const doc = scenario("Vortox", ["Mayor", "Spy"], names);
  doc.claims.push({ ...doc.claims[0]! });
  expect(await worldCount(doc)).toBe(0);
});
