import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";

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
  readonly timeline?: (names: readonly string[]) => readonly Record<string, unknown>[];
}

function scenario(roles: readonly string[], options: Options = {}) {
  const names = options.names ?? roles.map((_, index) => "ABCDEF"[index] as string);
  const extraClaims = options.claims?.(names) ?? [];
  const described = new Set(extraClaims.map((claim) => claim["name"]));
  return {
    players: names,
    script: [...new Set(roles)],
    setup: "none",
    timeline: options.timeline?.(names) ?? [],
    constraints: (options.constraints ?? []).map((expression) => ({ kind: "fact", expression })),
    claims: [
      ...roles.flatMap((role, index) =>
        described.has(names[index]) ? [] : [{ type: role, name: names[index], possibleActualRoles: [role] }],
      ),
      ...extraClaims,
    ],
  };
}

async function worldCount(doc: unknown): Promise<number> {
  return (await buildFromDoc(validatePuzzleDoc(doc), backend).solveAll()).length;
}

const POISONER_TABLE = ["Poisoner", "Goon", "Imp", "Chef", "Empath"];

function empathClaim(count: number) {
  return (names: readonly string[]) => [
    { type: "Empath", name: names[4], possibleActualRoles: ["Empath"], timing: "night_1", count },
  ];
}

test("a Poisoner that chooses the Goon first makes the Goon evil and poisons no player", async () => {
  // The neighbors of the Empath are the Chef and the Poisoner. The correct number is 1.
  const evilGoon = ["alignment_at(B, Evil, night_1)"];
  expect(await worldCount(scenario(POISONER_TABLE, { claims: empathClaim(1), constraints: evilGoon }))).toBe(1);
  expect(await worldCount(scenario(POISONER_TABLE, { claims: empathClaim(0), constraints: evilGoon }))).toBe(0);
  // A Poisoner that chooses the Empath can give the Empath a false number. The Goon stays good.
  expect(await worldCount(scenario(POISONER_TABLE, { claims: empathClaim(0) }))).toBe(1);
  expect(
    await worldCount(
      scenario(POISONER_TABLE, { claims: empathClaim(0), constraints: ["alignment_at(B, Good, night_1)"] }),
    ),
  ).toBe(1);
});

test("a Chef counts a Goon that the Poisoner made evil", async () => {
  const chefClaim = (count: number) => (names: readonly string[]) => [
    { type: "Chef", name: names[3], possibleActualRoles: ["Chef"], count },
  ];
  const evilGoon = ["alignment_at(B, Evil, night_1)"];
  // The evil pairs are Poisoner and Goon, and Goon and Imp.
  expect(await worldCount(scenario(POISONER_TABLE, { claims: chefClaim(2), constraints: evilGoon }))).toBe(1);
  expect(await worldCount(scenario(POISONER_TABLE, { claims: chefClaim(0), constraints: evilGoon }))).toBe(0);
});

const IMP_TABLE = ["Imp", "Goon", "Chef", "Empath"];
const noDeathOnNight2 = () => [{ type: "nightDeath", timing: "night_2", players: [] }];

test("a Demon that chooses the Goon first is drunk and kills no player", async () => {
  expect(await worldCount(scenario(IMP_TABLE, { timeline: noDeathOnNight2 }))).toBe(1);
  // All players are alive. An Imp must kill unless it chooses the Goon.
  expect(await worldCount(scenario(["Imp", "Saint", "Chef", "Empath"], { timeline: noDeathOnNight2 }))).toBe(0);
  // The Demon is evil, so the Goon becomes evil.
  expect(
    await worldCount(
      scenario(IMP_TABLE, { timeline: noDeathOnNight2, constraints: ["alignment_at(B, Good, night_2)"] }),
    ),
  ).toBe(0);
});

test("a Demon cannot choose the Goon first and also kill another player", async () => {
  const chefDies = (names: readonly string[]) => [{ type: "nightDeath", timing: "night_2", players: [names[2]] }];
  expect(await worldCount(scenario(IMP_TABLE, { timeline: chefDies }))).toBe(1);
  expect(
    await worldCount(scenario(IMP_TABLE, { timeline: chefDies, constraints: ["alignment_at(B, Evil, night_2)"] })),
  ).toBe(0);
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
    constraints: [`alignment_at(B, Evil, night_2) && alignment_at(B, ${finalAlignment}, night_3)`],
  });
  expect(await worldCount(scenario(table, options("Good")))).toBe(1);
  expect(await worldCount(scenario(table, options("Evil")))).toBe(0);
});

test("a Village Idiot is not drunk when the Poisoner chose the Goon first", async () => {
  const table = ["Poisoner", "Goon", "Village Idiot", "Chef", "Imp"];
  const evilGoon = ["alignment_at(B, Evil, night_1)"];
  expect(await worldCount(scenario(table, { claims: idiotClaim(1, false), constraints: evilGoon }))).toBe(1);
  expect(await worldCount(scenario(table, { claims: idiotClaim(1, true), constraints: evilGoon }))).toBe(0);
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
  const evilGoon = ["alignment_at(Vic, Evil, night_1)"];
  expect(await worldCount(scenario(POISONER_TABLE, { names, claims: empathClaim(1), constraints: evilGoon }))).toBe(1);
  expect(await worldCount(scenario(POISONER_TABLE, { names, claims: empathClaim(0), constraints: evilGoon }))).toBe(0);

  const twice = (names: readonly string[]) => [...idiotClaim(3, false)(names), ...idiotClaim(3, false)(names)];
  expect(await worldCount(scenario(IDIOT_TABLE, { claims: twice }))).toBe(0);
  const redundant = ["B.initial_role == Goon", "one Goon.~initial_role"];
  expect(await worldCount(scenario(IDIOT_TABLE, { claims: idiotClaim(1, false), constraints: redundant }))).toBe(1);
});
