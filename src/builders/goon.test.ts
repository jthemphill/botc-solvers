import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";
import { nightActionOrder } from "../model/nightOrder";
import { ROLE_CLASSES } from "../model/roleRegistry";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

// Each night, the first player to choose the Goon with their ability is drunk until dusk.
// The Goon becomes the alignment of that player.
// https://wiki.bloodontheclocktower.com/Goon
interface Options {
  readonly names?: readonly string[];
  readonly claims?: (names: readonly string[]) => readonly Record<string, unknown>[];
  readonly constraints?: readonly string[];
  /** The alignments of the player in the second seat, such as "Evil night_1". */
  readonly goon?: readonly string[];
  readonly timeline?: (names: readonly string[]) => readonly Record<string, unknown>[];
}

/** Returns a claim without reports. The Monk has no claim type, so a Mayor claim holds its place. */
function bareClaim(role: string): Record<string, unknown> {
  if (role === "Fortune Teller") return { type: "FortuneTeller", checks: [] };
  if (role === "Village Idiot") return { type: "VillageIdiot", checks: [] };
  if (role === "Snake Charmer") return { type: role, checks: [] };
  if (role === "Monk") return { type: "Mayor" };
  return { type: role };
}

function scenario(roles: readonly string[], options: Options = {}) {
  const names = options.names ?? roles.map((_, index) => "ABCDEF"[index] as string);
  const extraClaims = options.claims?.(names) ?? [];
  const described = new Set(extraClaims.map((claim) => claim["name"]));
  return {
    players: names,
    script: [...new Set([...roles, ...(roles.includes("Monk") ? ["Mayor"] : [])])],
    setup: "none",
    timeline: options.timeline?.(names) ?? [],
    constraints: (options.constraints ?? []).map((expression) => ({ kind: "fact", expression })),
    goon: (options.goon ?? []).map((entry) => [names[1] as string, ...entry.split(" ")] as const),
    claims: [
      ...roles.flatMap((role, index) =>
        described.has(names[index]) ? [] : [{ ...bareClaim(role), name: names[index], possibleActualRoles: [role] }],
      ),
      ...extraClaims,
    ],
  };
}

type Scenario = ReturnType<typeof scenario>;

function build({ goon, ...doc }: Scenario) {
  const game = buildFromDoc(validatePuzzleDoc(doc), backend);
  for (const [player, alignment, timing] of goon) {
    const good = game.isGoodAt(player, timing as "night_1");
    game.addTruth(alignment === "Good" ? good : game.not(good));
  }
  return game;
}

async function worldCount(doc: Scenario): Promise<number> {
  return (await build(doc).solveAll()).length;
}

const POISONER_TABLE = ["Poisoner", "Goon", "Imp", "Chef", "Empath"];

function empathClaim(count: number) {
  return (names: readonly string[]) => [
    { type: "Empath", name: names[4], possibleActualRoles: ["Empath"], timing: "night_1", count },
  ];
}

test("a Poisoner that chooses the Goon first makes the Goon evil and poisons no player", async () => {
  // The neighbors of the Empath are the Chef and the Poisoner. The correct number is 1.
  const evilGoon = ["Evil night_1"];
  expect(await worldCount(scenario(POISONER_TABLE, { claims: empathClaim(1), goon: evilGoon }))).toBe(1);
  expect(await worldCount(scenario(POISONER_TABLE, { claims: empathClaim(0), goon: evilGoon }))).toBe(0);
  // A Poisoner that chooses the Empath can give the Empath a false number. The Goon stays good.
  expect(await worldCount(scenario(POISONER_TABLE, { claims: empathClaim(0) }))).toBe(1);
  expect(await worldCount(scenario(POISONER_TABLE, { claims: empathClaim(0), goon: ["Good night_1"] }))).toBe(1);
});

test("a Chef counts a Goon that the Poisoner made evil", async () => {
  const chefClaim = (count: number) => (names: readonly string[]) => [
    { type: "Chef", name: names[3], possibleActualRoles: ["Chef"], count },
  ];
  const evilGoon = ["Evil night_1"];
  // The evil pairs are Poisoner and Goon, and Goon and Imp.
  expect(await worldCount(scenario(POISONER_TABLE, { claims: chefClaim(2), goon: evilGoon }))).toBe(1);
  expect(await worldCount(scenario(POISONER_TABLE, { claims: chefClaim(0), goon: evilGoon }))).toBe(0);
});

const IMP_TABLE = ["Imp", "Goon", "Chef", "Empath"];
const noDeathOnNight2 = () => [{ type: "nightDeath", timing: "night_2", players: [] }];

test("a Demon that chooses the Goon first is drunk and kills no player", async () => {
  expect(await worldCount(scenario(IMP_TABLE, { timeline: noDeathOnNight2 }))).toBe(1);
  // All players are alive. An Imp must kill unless it chooses the Goon.
  expect(await worldCount(scenario(["Imp", "Saint", "Chef", "Empath"], { timeline: noDeathOnNight2 }))).toBe(0);
  // The Demon is evil, so the Goon becomes evil.
  expect(await worldCount(scenario(IMP_TABLE, { timeline: noDeathOnNight2, goon: ["Good night_2"] }))).toBe(0);
});

test("a Demon cannot choose the Goon first and also kill another player", async () => {
  const chefDies = (names: readonly string[]) => [{ type: "nightDeath", timing: "night_2", players: [names[2]] }];
  expect(await worldCount(scenario(IMP_TABLE, { timeline: chefDies }))).toBe(1);
  expect(await worldCount(scenario(IMP_TABLE, { timeline: chefDies, goon: ["Evil night_2"] }))).toBe(0);
});

const IDIOT_TABLE = ["Imp", "Goon", "Village Idiot", "Chef"];

function idiotClaim(target: number, good: boolean, timing = "night_1") {
  return (names: readonly string[]) => [
    {
      type: "VillageIdiot",
      name: names[2],
      possibleActualRoles: ["Village Idiot"],
      checks: [{ timing, player: names[target], good }],
    },
  ];
}

test("a Village Idiot that chooses the Goon first is drunk", async () => {
  // The Goon is good. Only a drunk Village Idiot can learn that the Goon is evil.
  expect(await worldCount(scenario(IDIOT_TABLE, { claims: idiotClaim(1, false) }))).toBe(1);
  // The Chef is not the Goon. No drunkenness explains a false result.
  expect(await worldCount(scenario(IDIOT_TABLE, { claims: idiotClaim(3, false) }))).toBe(0);
  expect(await worldCount(scenario(IDIOT_TABLE, { claims: idiotClaim(3, true) }))).toBe(1);
});

test("a good Village Idiot makes an evil Goon good again", async () => {
  const table = ["Imp", "Goon", "Village Idiot", "Chef", "Empath"];
  const options = (finalAlignment: string): Options => ({
    claims: idiotClaim(1, true, "night_3"),
    timeline: (names) => [
      { type: "nightDeath", timing: "night_2", players: [] },
      { type: "nightDeath", timing: "night_3", players: [names[4]] },
    ],
    goon: ["Evil night_2", `${finalAlignment} night_3`],
  });
  expect(await worldCount(scenario(table, options("Good")))).toBe(1);
  expect(await worldCount(scenario(table, options("Evil")))).toBe(0);
});

test("a Village Idiot is not drunk when the Poisoner chose the Goon first", async () => {
  const table = ["Poisoner", "Goon", "Village Idiot", "Chef", "Imp"];
  const evilGoon = ["Evil night_1"];
  expect(await worldCount(scenario(table, { claims: idiotClaim(1, false), goon: evilGoon }))).toBe(1);
  expect(await worldCount(scenario(table, { claims: idiotClaim(1, true), goon: evilGoon }))).toBe(0);
});

function seamstressClaim(left: number, right: number, aligned: boolean) {
  return (names: readonly string[]) => [
    {
      type: "Seamstress",
      name: names[2],
      possibleActualRoles: ["Seamstress"],
      timing: "night_1",
      among: [names[left], names[right]],
      aligned,
    },
  ];
}

test("a Seamstress that chooses the Goon first is drunk", async () => {
  const table = ["Imp", "Goon", "Seamstress", "Chef", "Empath"];
  // The Goon and the Chef are good. Only a drunk Seamstress can learn that they differ.
  expect(await worldCount(scenario(table, { claims: seamstressClaim(1, 3, false) }))).toBe(1);
  expect(await worldCount(scenario(table, { claims: seamstressClaim(3, 4, false) }))).toBe(0);
  expect(await worldCount(scenario(table, { claims: seamstressClaim(3, 4, true) }))).toBe(1);
});

test("Goon results do not change with new names, duplicate reports, or redundant facts", async () => {
  const names = ["Uma", "Vic", "Wes", "Xena", "Yan"];
  const evilGoon = ["Evil night_1"];
  expect(await worldCount(scenario(POISONER_TABLE, { names, claims: empathClaim(1), goon: evilGoon }))).toBe(1);
  expect(await worldCount(scenario(POISONER_TABLE, { names, claims: empathClaim(0), goon: evilGoon }))).toBe(0);

  const twice = (names: readonly string[]) => [...idiotClaim(3, false)(names), ...idiotClaim(3, false)(names)];
  expect(await worldCount(scenario(IDIOT_TABLE, { claims: twice }))).toBe(0);
  const redundant = ["B.initial_role == Goon", "one Goon.~initial_role"];
  expect(await worldCount(scenario(IDIOT_TABLE, { claims: idiotClaim(1, false), constraints: redundant }))).toBe(1);
});

// The tests below use the player choices of all characters that choose players at night.
const CHOOSING_ROLES = [...ROLE_CLASSES.values()]
  .filter((role) => role.nightChoice !== undefined)
  .map((role) => role.roleName);

function chooserTable(role: string, outsider = "Goon"): Options & { readonly roles: readonly string[] } {
  // The chooser dies on night 2 when its ability needs that death. If not, the Imp kills the Empath.
  const victim = role === "Ravenkeeper" ? 0 : 4;
  return {
    roles: [role, outsider, "Imp", "Chef", "Empath"],
    timeline: (names) => [{ type: "nightDeath", timing: "night_2", players: [names[victim]] }],
  };
}

async function worldCountWithDrunk(doc: Scenario, player: string, timing: "night_1" | "night_2"): Promise<number> {
  const game = build(doc);
  game.addTruth(game.drunk(player, timing));
  return (await game.solveAll()).length;
}

test("each character with a night choice rule has a position in the night order", () => {
  expect(CHOOSING_ROLES.length).toBeGreaterThan(10);
  for (const role of CHOOSING_ROLES) {
    expect(() => nightActionOrder(role, "night_1"), role).not.toThrow();
    expect(() => nightActionOrder(role, "night_2"), role).not.toThrow();
  }
});

test.each(CHOOSING_ROLES)("an unreported %s choice can make its chooser drunk", async (role) => {
  const withGoon = chooserTable(role);
  expect(await worldCountWithDrunk(scenario(withGoon.roles, withGoon), "A", "night_2"), role).toBe(1);
  // Without a Goon, no ability makes the chooser drunk.
  const withSaint = chooserTable(role, "Saint");
  expect(await worldCountWithDrunk(scenario(withSaint.roles, withSaint), "A", "night_2"), role).toBe(0);
});

test("a reported choice of other players does not make the chooser drunk", async () => {
  const table = ["Fortune Teller", "Goon", "Imp", "Chef", "Empath"];
  const check = (left: number, right: number) => (names: readonly string[]) => [
    {
      type: "FortuneTeller",
      name: names[0],
      possibleActualRoles: ["Fortune Teller"],
      checks: [{ timing: "night_1", left: names[left], right: names[right], yes: true }],
    },
  ];
  // The Fortune Teller chose the Imp and the Chef. The yes is correct.
  expect(await worldCountWithDrunk(scenario(table, { claims: check(2, 3) }), "A", "night_1")).toBe(0);
  expect(await worldCountWithDrunk(scenario(table, { claims: check(1, 2) }), "A", "night_1")).toBe(1);
});

test("a night without a report has an unknown choice", async () => {
  const doc = scenario(IDIOT_TABLE, {
    claims: idiotClaim(3, true),
    timeline: (names) => [{ type: "nightDeath", timing: "night_2", players: [names[3]] }],
  });
  expect(await worldCountWithDrunk(doc, "C", "night_1")).toBe(0);
  expect(await worldCountWithDrunk(doc, "C", "night_2")).toBe(1);
});

test("a player that the Demon kills does not choose after the kill", async () => {
  const killed = (role: string): Options & { readonly roles: readonly string[] } => ({
    roles: [role, "Goon", "Imp", "Chef", "Empath"],
    timeline: (names) => [{ type: "nightDeath", timing: "night_2", players: [names[0]] }],
  });
  // The Village Idiot acts after the Demon. The Sailor acts before the Demon.
  const idiot = killed("Village Idiot");
  expect(await worldCountWithDrunk(scenario(idiot.roles, idiot), "A", "night_2")).toBe(0);
  const sailor = killed("Sailor");
  expect(await worldCountWithDrunk(scenario(sailor.roles, sailor), "A", "night_2")).toBe(1);
});

test("a Seamstress chooses players on one night only", async () => {
  const table = ["Imp", "Goon", "Seamstress", "Chef", "Empath"];
  const timeline = (names: readonly string[]) => [{ type: "nightDeath", timing: "night_2", players: [names[4]] }];
  expect(await worldCountWithDrunk(scenario(table, { timeline }), "C", "night_2")).toBe(1);
  const used = scenario(table, { timeline, claims: seamstressClaim(3, 4, true) });
  expect(await worldCountWithDrunk(used, "C", "night_2")).toBe(0);
});

test("the night order decides the first player that chooses the Goon", async () => {
  const table = ["Fortune Teller", "Goon", "Dreamer", "Imp", "Chef"];
  const doc = scenario(table, {
    claims: (names) => [
      {
        type: "FortuneTeller",
        name: names[0],
        possibleActualRoles: ["Fortune Teller"],
        checks: [{ timing: "night_1", left: names[1], right: names[4], yes: true }],
      },
      {
        type: "Dreamer",
        name: names[2],
        possibleActualRoles: ["Dreamer"],
        timing: "night_1",
        player: names[1],
        roles: ["Goon", "Imp"],
      },
    ],
  });
  // The Fortune Teller acts before the Dreamer.
  expect(await worldCountWithDrunk(doc, "A", "night_1")).toBe(1);
  expect(await worldCountWithDrunk(doc, "C", "night_1")).toBe(0);
});

test("the Butler acts before the Dreamer on the first night only", () => {
  expect(nightActionOrder("Butler", "night_1")).toBeLessThan(nightActionOrder("Dreamer", "night_1"));
  expect(nightActionOrder("Butler", "night_2")).toBeGreaterThan(nightActionOrder("Dreamer", "night_2"));
  expect(() => nightActionOrder("Chef")).toThrow();
});

async function activeActions(doc: Scenario) {
  const worlds = await build(doc).solveAll();
  expect(worlds).toHaveLength(1);
  return worlds[0]!.actions
    .filter((action) => action.active && action.selected.length > 0)
    .map((action) => `${action.timing} ${action.actor} ${action.rule} ${action.selected.join("+")}`);
}

test("a witness shows the choice actions that the Goon rule reads", async () => {
  // The Imp is the only player that can choose the Goon on night 2.
  expect(await activeActions(scenario(IMP_TABLE, { timeline: noDeathOnNight2 }))).toContain("night_2 A Imp:targets B");
  // A Demon kill and a reported choice are choice actions also.
  const doc = scenario(IDIOT_TABLE, {
    claims: idiotClaim(3, true),
    timeline: (names) => [{ type: "nightDeath", timing: "night_2", players: [names[3]] }],
  });
  const actions = await activeActions(doc);
  expect(actions).toContain("night_1 C Village Idiot:players D");
  expect(actions).toContain("night_2 A Imp:targets D");
});

test("a Goon that is good at the last phase reports its character and its alignments correctly", async () => {
  const table = ["Poisoner", "Goon", "Imp", "Chef", "Empath"];
  const claims = (claim: Record<string, unknown>) => (names: readonly string[]) => [
    { ...claim, name: names[1], possibleActualRoles: ["Goon"] },
  ];
  // The Poisoner makes the Goon evil on night 1, and the Goon stays evil. An evil Goon can claim the Mayor.
  const mayor = { roles: [...table, "Mayor"], claims: claims({ type: "Mayor" }) };
  expect(await worldCount(scenario(mayor.roles, { ...mayor, goon: ["Evil night_1"] }))).toBe(1);
  expect(await worldCount(scenario(mayor.roles, { ...mayor, goon: ["Good night_1"] }))).toBe(0);
  // A good Goon reports its alignment correctly. An evil Goon can report a false alignment.
  const report = (alignment: string) => claims({ type: "Goon", alignments: [{ timing: "night_1", alignment }] });
  expect(await worldCount(scenario(table, { claims: report("good"), goon: ["Good night_1"] }))).toBe(1);
  expect(await worldCount(scenario(table, { claims: report("evil"), goon: ["Good night_1"] }))).toBe(0);
  expect(await worldCount(scenario(table, { claims: report("good"), goon: ["Evil night_1"] }))).toBe(1);
});
