import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});
function scenario(noKillSinking = false, protectedTarget = false) {
  const roles = { A: "Po", B: "Chef", C: "Empath", D: "Gambler", E: protectedTarget ? "Soldier" : "Steward" };
  return {
    players: Object.keys(roles),
    script: [...Object.values(roles)],
    setup: "none",
    noKillSinking,
    constraints: Object.entries(roles).map(([p, r]) => ({ expression: `${p}.initial_role == ${r}` })),
    timeline: [
      { timing: "night_2", type: "nightDeath", players: [] },
      { timing: "night_3", type: "nightDeath", players: ["B", "C", "D"] },
    ],
    claims: [{ type: "Gambler", name: "D", guesses: [{ timing: "night_3", player: "B", role: "Empath" }] }],
  };
}
const solve = (doc: unknown) => buildFromDoc(validatePuzzleDoc(doc), backend).solveAll();

test("a charged Po can target a player killed earlier unless the puzzle forbids it", async () => {
  expect(await solve(scenario())).toHaveLength(1);
  expect(await solve(scenario(true))).toHaveLength(0);
  expect(await solve(scenario(true, true))).toHaveLength(1);
});

test("target assumptions survive renaming, duplicate reports, and redundant facts", async () => {
  for (const protectedTarget of [false, true]) {
    const doc = scenario(true, protectedTarget);
    const redundant = {
      ...doc,
      claims: [...doc.claims, ...doc.claims],
      constraints: [...doc.constraints, ...doc.constraints],
    };
    expect(await solve(JSON.parse(JSON.stringify(redundant).replace(/\b([A-E])\b/g, "Player$1")))).toHaveLength(
      protectedTarget ? 1 : 0,
    );
  }
});

// An Exorcist prevents a choice. This does not charge the Po.
// https://wiki.bloodontheclocktower.com/index.php?title=Po&oldid=3104
test("an exorcised Po cannot charge from the blocked night", async () => {
  const doc = scenario();
  const changed = {
    ...doc,
    script: ["Po", "Chef", "Empath", "Gambler", "Exorcist"],
    constraints: doc.constraints.map((c) =>
      c.expression.startsWith("E.") ? { expression: "E.initial_role == Exorcist" } : c,
    ),
    claims: [{ type: "Exorcist", name: "E", choices: [{ timing: "night_2", player: "A" }] }],
  };
  expect(await solve(changed)).toHaveLength(0);
  expect(
    await solve({
      ...changed,
      timeline: [changed.timeline[0], { timing: "night_3", type: "nightDeath", players: ["B"] }],
    }),
  ).toHaveLength(1);
});

test("an Exorcist preserves a charge from an earlier choice", async () => {
  const roles = { A: "Po", B: "Chef", C: "Empath", D: "Steward", E: "Exorcist", F: "Soldier", G: "Noble" };
  expect(
    await solve({
      players: Object.keys(roles),
      script: Object.values(roles),
      setup: "none",
      constraints: Object.entries(roles).map(([p, r]) => ({ expression: `${p}.initial_role == ${r}` })),
      claims: [{ type: "Exorcist", name: "E", choices: [{ timing: "night_3", player: "A" }] }],
      timeline: [
        { timing: "night_2", type: "nightDeath", players: [] },
        { timing: "night_3", type: "nightDeath", players: [] },
        { timing: "night_4", type: "nightDeath", players: ["B", "C", "D"] },
      ],
    }),
  ).toHaveLength(1);
});

test("a kill cannot sink into a previous day's corpse under the puzzle assumption", async () => {
  const roles = { A: "Imp", B: "Chef", C: "Empath", D: "Steward", E: "Noble" };
  for (const noKillSinking of [false, true]) {
    expect(
      await solve({
        players: Object.keys(roles),
        script: Object.values(roles),
        setup: "none",
        noKillSinking,
        constraints: Object.entries(roles).map(([p, r]) => ({ expression: `${p}.initial_role == ${r}` })),
        claims: [],
        timeline: [
          { timing: "day_1", type: "execution", players: ["B"] },
          { timing: "night_2", type: "nightDeath", players: [] },
        ],
      }),
    ).toHaveLength(noKillSinking ? 0 : 1);
  }
});

test("the no kill sinking assumption requires a boolean", () => {
  expect(() => validatePuzzleDoc({ ...scenario(), noKillSinking: "true" })).toThrow("$.noKillSinking");
  expect(validatePuzzleDoc(scenario(true)).noKillSinking).toBe(true);
});
