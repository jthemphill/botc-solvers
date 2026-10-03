import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

// The chosen player learns the source of the Nightwatchman ability.
// A Vortox makes this player learn a different source.
// https://wiki.bloodontheclocktower.com/index.php?title=Nightwatchman&oldid=2827
function scenario(demon = "Imp", shown = "A", philosopher = false) {
  const roles = { A: philosopher ? "Philosopher" : "Nightwatchman", B: "Chef", C: "Soldier", D: demon };
  return {
    players: Object.keys(roles),
    script: [...new Set([...Object.values(roles), "Nightwatchman"])],
    setup: "none",
    constraints: Object.entries(roles).map(([player, role]) => ({ expression: `${player}.initial_role == ${role}` })),
    claims: [
      philosopher
        ? { type: "Philosopher", name: "A", role: "Nightwatchman", timing: "night_1", nightwatchman: { chosen: "B" } }
        : { type: "Nightwatchman", name: "A", timing: "night_1", chosen: "B" },
      { type: "Chef", name: "B", nightwatchmanPings: [{ player: shown, timing: "night_1" }] },
    ],
  };
}
const build = (doc: unknown) => buildFromDoc(validatePuzzleDoc(doc), backend);

test("a Nightwatchman recipient learns the actual source without a Vortox", async () => {
  expect(await build(scenario()).solveAll()).toHaveLength(1);
  expect(await build(scenario("Imp", "C")).solveAll()).toHaveLength(0);
});

test("a Vortox requires a different Nightwatchman source", async () => {
  expect(await build(scenario("Vortox", "C")).solveAll()).toHaveLength(1);
  expect(await build(scenario("Vortox", "A")).solveAll()).toHaveLength(0);
});

test("a Philosopher can send a Nightwatchman signal affected by Vortox", async () => {
  expect(await build(scenario("Vortox", "C", true)).solveAll()).toHaveLength(1);
  expect(await build(scenario("Vortox", "A", true)).solveAll()).toHaveLength(0);
});

test("poison on the source prevents a signal, but poison on the recipient does not", async () => {
  for (const player of ["A", "B"]) {
    const game = build(scenario());
    game.fixPoisoned(player, true, "night_1");
    expect(await game.solveAll()).toHaveLength(player === "A" ? 0 : 1);
  }
});

test("an unreported Nightwatchman choice can explain a received signal", async () => {
  const doc = scenario();
  expect(await build({ ...doc, claims: doc.claims.slice(1) }).solveAll()).toHaveLength(1);
});

test("a signal needs a source that chose its recipient", async () => {
  const doc = scenario();
  expect(await build({ ...doc, claims: [{ ...doc.claims[0], chosen: "C" }, doc.claims[1]] }).solveAll()).toHaveLength(
    0,
  );
  expect(
    await build({
      ...doc,
      script: [...doc.script, "Saint"],
      constraints: doc.constraints.map((c) =>
        c.expression.startsWith("A.") ? { expression: "A.initial_role == Saint" } : c,
      ),
      claims: doc.claims.slice(1),
    }).solveAll(),
  ).toHaveLength(0);
});

test("one Nightwatchman cannot act on two nights", async () => {
  const doc = scenario();
  expect(
    await build({ ...doc, claims: [...doc.claims, { ...doc.claims[0], timing: "night_2" }] }).solveAll(),
  ).toHaveLength(0);
});

test("a Philosopher can use Nightwatchman after gaining it, but not before", async () => {
  const doc = scenario("Imp", "A", true);
  for (const timing of ["night_1", "night_2", "night_3"]) {
    const game = build({
      ...doc,
      claims: [{ ...doc.claims[0], timing: "night_2", nightwatchman: { chosen: "B", timing } }],
    });
    expect(await game.solveAll()).toHaveLength(timing === "night_1" ? 0 : 1);
  }
});

test("a Nightwatchman cannot send a signal after dying on the previous day", async () => {
  const doc = scenario();
  const game = build({
    ...doc,
    timeline: [{ type: "execution", timing: "day_1", players: ["A"] }],
    claims: [
      { ...doc.claims[0], timing: "night_2" },
      { ...doc.claims[1], nightwatchmanPings: [{ player: "A", timing: "night_2" }] },
    ],
  });
  expect(await game.solveAll()).toHaveLength(0);
});

test("poison on the Vortox restores correct Nightwatchman information", async () => {
  for (const shown of ["A", "C"]) {
    const game = build(scenario("Vortox", shown));
    game.fixPoisoned("D", true, "night_1");
    expect(await game.solveAll()).toHaveLength(shown === "A" ? 1 : 0);
  }
});

test("a Philosopher signal names the Philosopher and the original Nightwatchman is drunk", async () => {
  const doc = scenario("Imp", "A", true);
  const constraints = doc.constraints.map((c) =>
    c.expression.startsWith("C.") ? { expression: "C.initial_role == Nightwatchman" } : c,
  );
  const game = build({
    ...doc,
    constraints,
    claims: [...doc.claims, { type: "Nightwatchman", name: "C", chosen: "B", timing: "night_1" }],
  });
  const worlds = await game.solveAll();
  expect(worlds).toHaveLength(1);
  expect(worlds[0]!.drunkByTiming.get("night_1")?.has("C")).toBe(true);
  expect(
    await build({
      ...doc,
      constraints,
      claims: [doc.claims[0], { ...doc.claims[1], nightwatchmanPings: [{ player: "C", timing: "night_1" }] }],
    }).solveAll(),
  ).toHaveLength(0);
});

test("renaming, duplicate reports, and redundant facts preserve Nightwatchman results", async () => {
  for (const shown of ["A", "C"]) {
    const doc = scenario("Vortox", shown, true);
    const duplicated = {
      ...doc,
      claims: [...doc.claims, ...doc.claims],
      constraints: [...doc.constraints, ...doc.constraints],
    };
    const renamed = JSON.parse(JSON.stringify(duplicated).replace(/\b([A-D])\b/g, "Player$1"));
    expect(await build(renamed).solveAll()).toHaveLength(shown === "C" ? 1 : 0);
  }
});
