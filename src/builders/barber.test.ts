import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

// The Demon may swap two characters after a healthy Barber dies.
// The swap keeps alignment and can include dead players or the acting Demon.
// https://wiki.bloodontheclocktower.com/index.php?title=Barber&oldid=1757
const roles = { A: "Artist", B: "Barber", C: "No Dashii", D: "Witch", E: "Town Crier", F: "Juggler" };
function scenario(timeline: unknown[] = [{ type: "nightDeath", timing: "night_2", players: ["B"] }]) {
  return {
    players: Object.keys(roles),
    script: Object.values(roles),
    setup: "none",
    timeline,
    claims: Object.entries(roles).map(([name, type]) => ({
      name,
      type,
      checks: [],
      guesses: {},
      possibleActualRoles: [type],
    })),
  };
}
const build = (doc: unknown = scenario()) => buildFromDoc(validatePuzzleDoc(doc), backend);

test("a Barber swap is optional and preserves both characters and alignment", async () => {
  for (const swap of [false, true]) {
    const game = build();
    game.addTruth(game.characterAt("C", swap ? "Witch" : "No Dashii", "night_2"));
    game.addTruth(game.characterAt("D", swap ? "No Dashii" : "Witch", "day_3"));
    game.addTruth(game.isEvilAt("C", "day_3"));
    game.addTruth(game.isEvilAt("D", "day_3"));
    expect(await game.solveAll()).toHaveLength(1);
  }
});

test("a Barber swap cannot occur without a death or after a poisoned Barber dies", async () => {
  for (const died of [false, true]) {
    const game = build(scenario(died ? undefined : [{ type: "nightDeath", timing: "night_2", players: [] }]));
    if (died) game.fixPoisoned("B", true, "night_2");
    game.addTruth(game.characterAt("D", "No Dashii", "night_2"));
    expect(await game.solveAll()).toHaveLength(0);
  }
});

test("a Barber swap can exchange a living character with the dead Barber", async () => {
  const game = build();
  game.addTruth(game.characterAt("A", "Barber", "night_2"));
  game.addTruth(game.characterAt("B", "Artist", "night_2"));
  game.addTruth(game.isGoodAt("A", "night_2"));
  expect(await game.solveAll()).toHaveLength(1);
});

test("one Barber death cannot swap two pairs or repeat on a later night", async () => {
  for (const secondTiming of ["night_2", "night_3"] as const) {
    const game = build();
    game.addTruth(game.characterAt("C", "Witch", "night_2"));
    game.addTruth(game.characterAt("D", "No Dashii", "night_2"));
    game.addTruth(game.characterAt("A", "Juggler", secondTiming));
    game.addTruth(game.characterAt("F", "Artist", secondTiming));
    expect(await game.solveAll()).toHaveLength(0);
  }
});

test("a Barber swap moves No Dashii poison before later information", async () => {
  const game = build();
  game.addTruth(game.characterAt("D", "No Dashii", "night_2"));
  game.addTruth(game.noDashiiPoisonedAt("A", "night_1"));
  game.addFalse(game.noDashiiPoisonedAt("F", "night_1"));
  game.addTruth(game.noDashiiPoisonedAt("A", "night_2"));
  game.addTruth(game.noDashiiPoisonedAt("E", "night_2"));
  expect(await game.solveAll()).toHaveLength(1);
});

test("No Dashii poison follows Townsfolk characters moved by the Barber", async () => {
  const game = build();
  game.addTruth(game.characterAt("A", "Barber", "night_2"));
  game.addTruth(game.characterAt("B", "Artist", "night_2"));
  game.addFalse(game.noDashiiPoisonedAt("A", "night_2"));
  game.addTruth(game.noDashiiPoisonedAt("B", "night_2"));
  expect(await game.solveAll()).toHaveLength(1);
});

test("the former Demon can be executed after a Barber swap", async () => {
  for (const executed of ["C", "D"]) {
    const game = build(
      scenario([
        { type: "nightDeath", timing: "night_2", players: ["B"] },
        { type: "execution", timing: "day_2", players: [executed] },
      ]),
    );
    game.addTruth(game.characterAt("C", "Witch", "night_2"));
    game.addTruth(game.characterAt("D", "No Dashii", "night_2"));
    expect(await game.solveAll()).toHaveLength(executed === "C" ? 1 : 0);
  }
});

test("a good player's later role report must describe the Barber swap", async () => {
  for (const type of ["Barber", "Artist"]) {
    const doc = scenario();
    const game = build({ ...doc, claims: [...doc.claims, { name: "A", type, roleTiming: "day_2" }] });
    game.addTruth(game.characterAt("A", "Barber", "night_2"));
    expect(await game.solveAll()).toHaveLength(type === "Barber" ? 1 : 0);
  }
});

test("a living starting Mutant can repeat its permitted Townsfolk bluff after a Barber death", async () => {
  const doc = scenario();
  doc.script.push("Mutant");
  const game = build({
    ...doc,
    claims: [
      { name: "A", type: "Artist", possibleActualRoles: ["Artist", "Mutant"] },
      ...doc.claims.slice(1),
      { name: "A", type: "Artist", roleTiming: "day_2" },
    ],
  });
  game.fixActual("A", "Mutant");
  game.addTruth(game.characterAt("A", "Mutant", "day_2"));
  expect(await game.solveAll()).toHaveLength(1);
});

test("a daytime Barber death uses health at death and permits the next night's swap", async () => {
  for (const poisoned of [false, true]) {
    const game = build(
      scenario([
        { type: "execution", timing: "day_1", players: ["B"] },
        { type: "nightDeath", timing: "night_2", players: [] },
      ]),
    );
    game.fixPoisoned("B", poisoned, "day_1");
    game.fixPoisoned("B", false, "night_2");
    game.addTruth(game.characterAt("D", "No Dashii", "night_2"));
    expect(await game.solveAll()).toHaveLength(poisoned ? 0 : 1);
  }
});

test("Barber swaps preserve alignment when good and evil players exchange characters", async () => {
  const game = build();
  game.addTruth(game.characterAt("A", "Witch", "night_2"));
  game.addTruth(game.characterAt("D", "Artist", "night_2"));
  game.addTruth(game.isGoodAt("A", "night_2"));
  game.addTruth(game.isEvilAt("D", "night_2"));
  expect(await game.solveAll()).toHaveLength(1);
});

test("renaming players and duplicating a death report preserve a Barber swap", async () => {
  const doc = scenario();
  doc.timeline.push(...doc.timeline);
  const renamed = JSON.parse(JSON.stringify(doc).replace(/"([A-F])"/g, '"Player $1"'));
  const game = build(renamed);
  game.addTruth(game.characterAt("Player C", "Witch", "night_2"));
  game.addTruth(game.characterAt("Player D", "No Dashii", "night_2"));
  const worlds = await game.solveAll();
  expect(worlds).toHaveLength(1);
  expect(worlds[0]!.trace!.transitions.filter((change) => change.rule === "Barber")).toHaveLength(2);
});
