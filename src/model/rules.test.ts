import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "../builders/buildFromDoc";
import { compile } from "../dsl/compile";
import { validatePuzzleDoc } from "../schema/validate";
import { BOTCModel } from "./model";
import { roleByName } from "./roleRegistry";
import { KissatBackend } from "./sat";
import { validateTraceWitness } from "./trace";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});
const claim = (name: string, type: string, timing?: string) => ({ name, type, timing, possibleActualRoles: [type] });
const build = (doc: unknown) => buildFromDoc(validatePuzzleDoc(doc), backend);

// The Pit-Hag selects one player and one character each night after the first night.
// The character change keeps the player's alignment.
// https://wiki.bloodontheclocktower.com/Pit-Hag (oldid=2998)
const pitHag = () => ({
  players: ["A", "B", "C", "D", "E"],
  script: ["Slayer", "Chef", "Steward", "Pit-Hag", "Imp", "Artist", "Sage"],
  setup: "none",
  claims: [
    claim("A", "Slayer", "night_1"),
    claim("B", "Chef", "night_1"),
    claim("C", "Steward", "day_2"),
    claim("D", "Pit-Hag"),
    claim("E", "Imp"),
  ],
});

test("one Pit-Hag cannot transform two players in the same night", async () => {
  const game = build(pitHag());
  game.addTruth(game.characterAt("A", "Artist", "night_2"));
  game.addTruth(game.characterAt("B", "Sage", "night_2"));
  expect(await game.solveAll()).toHaveLength(0);
});

test("a changed-role report constrains a legal transition without starting-role overrides", async () => {
  const doc = pitHag();
  const game = build({ ...doc, claims: [...doc.claims, { name: "A", type: "Artist", roleTiming: "day_2" }] });
  game.addTruth(game.characterAt("A", "Artist", "day_2"));
  game.addFalse(game.characterAt("A", "Slayer", "day_2"));
  game.addTruth(
    compile("A.role == Artist && A.type == Townsfolk", game, { ...doc, nameRoot: "changed", timing: "day_2" }),
  );
  const worlds = await game.solveAll({ limit: 1 });
  expect(worlds).toHaveLength(1);
  expect(worlds[0]!.trace!.transitions.some((change) => change.player === "A" && change.character === "Artist")).toBe(
    true,
  );
});

test("character transitions persist and acquired abilities do not replace characters", async () => {
  const game = new BOTCModel(["A"], { characters: ["Philosopher", "Artist", "Chef"].map(roleByName), backend });
  game.fixActual("A", "Philosopher");
  game.gainAbility("A", "Artist", "night_1", game.constantBool(true, "chosen"), "Philosopher");
  game.addTruth(game.hasRoleAt("A", "Artist", "day_1"));
  game.addTruth(game.characterAt("A", "Philosopher", "day_1"));
  game.addRoleAt("A", "Chef", "night_2");
  game.addTruth(game.characterAt("A", "Chef", "day_3"));
  game.addFalse(game.hasRoleAt("A", "Artist", "day_3"));
  const world = (await game.solveAll())[0]!;
  expect(validateTraceWitness(world.trace!)).toEqual([]);
  const bad = { ...world.trace!, snapshots: [{ timing: "day_3" as const, characters: { A: "Philosopher" } }] };
  expect(validateTraceWitness(bad).length).toBeGreaterThan(0);
});

// The Shabaloth selects two players each night after the first night.
// Each target can be alive or dead.
// https://wiki.bloodontheclocktower.com/Shabaloth (oldid=1790)
const shabaloth = () => ({
  players: ["A", "B", "C", "D", "E"],
  script: ["Shabaloth", "Baron", "Slayer", "Steward", "Chef"],
  setup: "none",
  claims: [
    claim("A", "Shabaloth"),
    claim("B", "Baron"),
    claim("C", "Slayer"),
    claim("D", "Steward"),
    claim("E", "Chef"),
  ],
});
test("redundant first-night observations cannot change Shabaloth mechanics", async () => {
  for (const firstNight of [[], [{ type: "nightDeath", timing: "night_1", players: [] }]]) {
    const game = build({
      ...shabaloth(),
      timeline: [...firstNight, { type: "nightDeath", timing: "night_2", players: ["B"] }],
    });
    expect(await game.solveAll()).toHaveLength(0);
  }
});
test("Shabaloth can attack two dead players without causing a death", async () => {
  const game = build({
    ...shabaloth(),
    timeline: [
      { type: "nightDeath", timing: "night_2", players: ["B", "C"] },
      { type: "nightDeath", timing: "night_3", players: [] },
    ],
  });
  expect(await game.solveAll()).toHaveLength(1);
});

// Drunkenness or poison disables the ability.
// https://wiki.bloodontheclocktower.com/States
test("Spy registration varies between interactions only while healthy", async () => {
  for (const poisoned of [false, true]) {
    const game = new BOTCModel(["A"], { characters: ["Spy", "Chef"].map(roleByName), backend });
    game.fixActual("A", "Spy");
    game.fixPoisoned("A", poisoned, "night_2");
    game.addTruth(game.registersAsRoleAt("A", "Chef", "night_2", "washerwoman"));
    game.addTruth(game.registersAsRoleAt("A", "Spy", "night_2", "undertaker"));
    expect((await game.solveAll()).length).toBe(poisoned ? 0 : 1);
  }
});

// The Mathematician counts each other player at most once.
// The count uses ability malfunctions since the previous dawn.
// https://wiki.bloodontheclocktower.com/Mathematician
test("Mathematician counts distinct players across day and night, independent of report order or duplication", async () => {
  for (const copies of [1, 2]) {
    const game = new BOTCModel(["A"], { characters: [roleByName("Chef")], backend });
    game.addTruth(game.malfunctionCountAt("night_2", 1, "math_before_reports"));
    game.fixPoisoned("A", true, "night_2");
    for (let i = 0; i < copies; i++)
      game.addInfoClaim({ player: "A", role: "Chef", timing: "night_2", learned: game.constantBool(false, "wrong") });
    game.recordAbilityMalfunction("A", "day_1", game.constantBool(true, "day_ability_failed"));
    game.addTruth(game.malfunctionCountAt("night_2", 0, "exclude_self", "A"));
    expect(await game.solveAll()).toHaveLength(1);
  }
});

test("puzzles continue after the final recorded event", async () => {
  const doc = {
    ...shabaloth(),
    script: ["Imp", "Baron", "Slayer", "Steward", "Chef"],
    claims: [{ name: "A", type: "Slayer" }, ...shabaloth().claims.slice(1)],
  };
  for (const executed of ["C", "A"]) {
    const game = build({ ...doc, timeline: [{ type: "execution", timing: "day_1", players: [executed] }] });
    game.fixActual("A", "Imp");
    // Execution of the only Demon ends the game.
    expect(await game.solveAll()).toHaveLength(executed === "A" ? 0 : 1);
  }
});

test("names and titles have no effect on the modeled horizon", async () => {
  for (const title of ["a title", "night_9000"]) {
    const game = build({ ...pitHag(), title });
    expect((await game.solveAll({ limit: 1 }))[0]!.actions.every((action) => action.timing === "night_2")).toBe(true);
  }
});

// For each report, use the ability state at the time of the report.
test("a truthful reporter cannot continue using a lost ability", async () => {
  for (const reportAfterChange of [false, true]) {
    const game = new BOTCModel(["A"], { characters: ["Chef", "Artist"].map(roleByName), backend });
    game.fixActual("A", "Chef");
    game.addRoleAt("A", "Artist", "night_2");
    game.addInfoClaim({
      player: "A",
      role: "Chef",
      timing: reportAfterChange ? "night_3" : "night_1",
      learned: game.constantBool(true, "truth"),
    });
    expect((await game.solveAll()).length).toBe(reportAfterChange ? 0 : 1);
  }
});

test("Philosopher can duplicate an ability without duplicate starting characters", async () => {
  const game = new BOTCModel(["A", "B"], { characters: ["Philosopher", "Artist"].map(roleByName), backend });
  game.fixActual("A", "Philosopher");
  game.fixActual("B", "Artist");
  game.gainAbility("A", "Artist", "night_2", game.constantBool(true, "choice"), "Philosopher");
  game.addTruth(game.hasRoleAt("A", "Artist", "day_2"));
  game.addTruth(game.hasRoleAt("B", "Artist", "day_2"));
  expect(await game.solveAll()).toHaveLength(1);
  const duplicate = new BOTCModel(["A", "B"], { characters: ["Philosopher", "Artist"].map(roleByName), backend });
  duplicate.fixActual("A", "Artist");
  duplicate.fixActual("B", "Artist");
  expect(await duplicate.solveAll()).toHaveLength(0);
});

test("renaming and rotating seats preserves role projections; removing a fact cannot remove worlds", async () => {
  const players = ["A", "B", "C"];
  const roles = ["Chef", "Imp", "Baron"];
  const solve = async (seats: string[], names: string[], constrain: boolean) => {
    const game = new BOTCModel(seats, { characters: roles.map(roleByName), backend });
    if (constrain) game.addFalse(game.actualIs(names[0]!, "Imp"));
    game.addTruth(
      compile(`one p: players | p.alignment == Good`, game, { players: seats, script: roles, nameRoot: "good" }),
    );
    return new Set((await game.solveAll()).map((world) => names.map((name) => world.actualRole(name)).join(",")));
  };
  const base = await solve(players, players, true);
  const renamed = ["Nora", "night_20", "Iris"];
  expect(await solve([renamed[1]!, renamed[2]!, renamed[0]!], renamed, true)).toEqual(base);
  const relaxed = await solve(players, players, false);
  for (const world of base) expect(relaxed.has(world)).toBe(true);
  expect(relaxed.size).toBeGreaterThan(base.size);
});

test("small independently generated character histories remain possible after hiding the initial token", async () => {
  const roles = ["Chef", "Artist", "Slayer"];
  for (const start of roles)
    for (const finish of roles) {
      const game = new BOTCModel(["A"], { characters: roles.map(roleByName), backend });
      const origin = {
        initial: { A: start },
        transitions: [{ player: "A", character: finish, timing: "night_2" as const, rule: "generated" }],
        snapshots: [{ timing: "day_3" as const, characters: { A: finish } }],
      };
      expect(validateTraceWitness(origin)).toEqual([]);
      game.addRoleAt("A", finish, "night_2");
      game.addTruth(game.characterAt("A", finish, "day_3"));
      expect((await game.solveAll()).some((world) => world.actualRole("A") === start)).toBe(true);
    }
});

test("information reports follow the shared honesty rule", async () => {
  for (const poisoned of [false, true]) {
    const game = new BOTCModel(["A"], { characters: [roleByName("Chef")], backend });
    game.fixPoisoned("A", poisoned, "night_1");
    game.addInfoClaim({ player: "A", role: "Chef", timing: "night_1", learned: game.constantBool(false, "wrong") });
    expect(await game.solveAll()).toHaveLength(poisoned ? 1 : 0);
  }
});

test("the independent choice checker rejects changing a rule's required count", async () => {
  const { validateChoiceWitness } = await import("./actions");
  expect(
    validateChoiceWitness({
      rule: "Shabaloth:targets",
      actor: "A",
      timing: "night_2",
      active: true,
      count: 1,
      candidates: ["A", "B"],
      selected: ["B"],
    }),
  ).not.toEqual([]);
});

test("intrinsic Drunk state follows character replacement instead of the starting token", async () => {
  const game = new BOTCModel(["A"], { characters: ["Chef", "Drunk"].map(roleByName), backend });
  game.fixActual("A", "Chef");
  game.addRoleAt("A", "Drunk", "night_2");
  game.addTruth(game.soberAndHealthy("A", "night_1"));
  game.addFalse(game.soberAndHealthy("A", "day_2"));
  game.addInfoClaim({
    player: "A",
    role: "Chef",
    timing: "night_2",
    learned: game.constantBool(false, "false_belief"),
  });
  game.addRoleAt("A", "Chef", "night_3");
  game.addTruth(game.soberAndHealthy("A", "day_3"));
  expect(await game.solveAll()).toHaveLength(1);
});

test("returning to Philosopher does not restore an ability lost with that character", async () => {
  const game = new BOTCModel(["A"], { characters: ["Philosopher", "Chef", "Artist"].map(roleByName), backend });
  game.fixActual("A", "Philosopher");
  game.gainAbility("A", "Chef", "night_1", game.constantBool(true, "choice"), "Philosopher");
  game.addRoleAt("A", "Artist", "night_2");
  game.addRoleAt("A", "Philosopher", "night_3");
  game.addFalse(game.hasRoleAt("A", "Chef", "day_3"));
  expect(await game.solveAll()).toHaveLength(1);
});

test("information report times set the final modeled phase", async () => {
  const doc = pitHag();
  const game = build({
    ...doc,
    claims: [...doc.claims, { type: "Artist", name: "D", info: [{ timing: "day_3", expression: "false" }] }],
  });
  const worlds = await game.solveAll({ limit: 1 });
  expect(worlds[0]!.actions.some((action) => action.timing === "night_3" && action.active)).toBe(true);
});

test("initial role claims and explicit later role claims share a trace", async () => {
  const doc = {
    players: ["A"],
    script: ["Chef", "Artist"],
    setup: "none",
    claims: [claim("A", "Chef", "night_2"), { type: "Artist", name: "A", roleTiming: "day_2" }],
  };
  expect(await build(doc).solveAll()).toHaveLength(0);
  const changed = build(doc);
  changed.addRoleAt("A", "Artist", "night_2");
  expect(await changed.solveAll()).toHaveLength(1);
});

test("a simple supplied fact retains its source on the assertion clause", () => {
  const game = build({
    players: ["A"],
    script: ["Chef", "Artist"],
    setup: "none",
    claims: [],
    constraints: [{ expression: "A.initial_role == Chef", source: "setup record" }],
  });
  expect(
    game
      .finalize()
      .origins?.some(
        (origin) => origin.kind === "fact" && origin.id === "constraints[0]" && origin.source === "setup record",
      ),
  ).toBe(true);
});
