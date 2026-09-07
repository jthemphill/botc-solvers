import { expect, test } from "@playwright/test";
import type { PuzzleDoc, TimelineEventDoc } from "../../src/schema/puzzleDoc";
import { CLAIM_EDITOR_CASES } from "./claim-editor-cases";
import {
  addAndFillClaims,
  addRoleToList,
  checkPlayers,
  claimsPanel,
  comparableDoc,
  enterPuzzle,
  exportPuzzleDoc,
  fillField,
  fillRoleField,
  selectField,
  selectPlayerClaims,
  setCustomConstraints,
  setTimeline,
} from "./editor-helpers";

for (const { name, script, claims } of CLAIM_EDITOR_CASES) {
  test(`creates and exports ${name}`, async ({ page }) => {
    const doc: PuzzleDoc = { title: name, players: ["Ada", "Ben", "Cara"], setup: "none", script, claims };
    await enterPuzzle(page, doc);
    expect(comparableDoc(await exportPuzzleDoc(page))).toEqual(comparableDoc(doc));
  });
}

for (const [layout, viewport] of [
  ["desktop", { width: 1280, height: 900 }],
  ["mobile", { width: 390, height: 900 }],
] as const) {
  test(`creates, solves, edits, and reimports a puzzle on ${layout}`, async ({ page }) => {
    await page.setViewportSize(viewport);
    const doc: PuzzleDoc = {
      title: "Two evil neighbors",
      players: ["Ada", "Ben", "Cara", "Drew", "Eve"],
      script: ["Chef", "Empath", "Soldier", "Imp", "Scarlet Woman"],
      claims: [
        { type: "Chef", name: "Ada", count: 1, timing: "night_1" },
        { type: "Empath", name: "Ben", count: 0, timing: "night_1" },
        { type: "Soldier", name: "Cara" },
        { type: "Chef", name: "Drew", count: 0, timing: "night_1" },
        { type: "Chef", name: "Eve", count: 0, timing: "night_1" },
      ],
    };
    await enterPuzzle(page, doc);
    const solutions = page.getByRole("region", { name: "Solutions", exact: true });
    const count = solutions.getByText("Satisfying worlds:").locator("strong");
    await expect(count).toHaveText("2");
    await expect(solutions.getByLabel("Ada: Chef")).toHaveCount(2);
    await expect(solutions.getByLabel("Ben: Empath")).toHaveCount(2);
    await expect(solutions.getByLabel("Cara: Soldier")).toHaveCount(2);
    await expect(solutions.getByLabel("Drew: Imp, claimed Chef")).toBeVisible();
    await expect(solutions.getByLabel("Eve: Imp, claimed Chef")).toBeVisible();
    await expect(solutions.getByText("All initial character assignments enumerated.")).toBeVisible();
    expect(comparableDoc(await exportPuzzleDoc(page))).toEqual(comparableDoc(doc));

    const timeline: readonly TimelineEventDoc[] = [
      { timing: "day_1", type: "execution", players: ["Ben"] },
      { timing: "night_2", type: "nightDeath", players: ["Ada"] },
    ];
    await setTimeline(page, timeline, doc.players);
    await selectPlayerClaims(page, "Ada");
    const chef = claimsPanel(page).locator(".claim-block");
    await fillField(chef, "Count", "0");
    await expect(count).toHaveText("0");
    await expect(solutions.getByText("No worlds — the encoded constraints are unsatisfiable.")).toBeVisible();
    await fillField(chef, "Count", "1");
    await expect(count).toHaveText("2");

    const exported = await exportPuzzleDoc(page);
    expect(comparableDoc(exported)).toEqual(comparableDoc({ ...doc, timeline }));
    await page.getByRole("button", { name: "New Puzzle", exact: true }).click();
    await expect(page.getByLabel("Title", { exact: true })).toHaveValue("Untitled puzzle");
    await expect(count).toHaveCount(0);
    await page.locator('input[type="file"]').setInputFiles({
      name: "two-evil-neighbors.json",
      mimeType: "application/json",
      buffer: Buffer.from(JSON.stringify(exported)),
    });
    await expect(page.getByLabel("Title", { exact: true })).toHaveValue(doc.title!);
    await expect(count).toHaveText("2");
    expect(comparableDoc(await exportPuzzleDoc(page))).toEqual(comparableDoc(exported));
  });
}

test("edits and removes repeated reports and whole claims", async ({ page }) => {
  const doc: PuzzleDoc = {
    title: "Editing reports",
    players: ["Ada", "Ben", "Cara"],
    setup: "none",
    script: ["Chambermaid"],
    claims: [
      {
        type: "Chambermaid",
        name: "Ada",
        checks: [
          { left: "Ada", right: "Ben", count: 0, timing: "night_1" },
          { left: "Ben", right: "Cara", count: 2, timing: "night_2" },
        ],
      },
    ],
  };
  await enterPuzzle(page, doc);
  const block = claimsPanel(page).locator(".claim-block");
  await block.getByRole("button", { name: "Remove check", exact: true }).first().click();
  await selectField(block, "Left", "Cara");
  await selectField(block, "Right", "Ben");
  await fillField(block, "Count", "1");
  expect((await exportPuzzleDoc(page)).claims).toEqual([
    { type: "Chambermaid", name: "Ada", checks: [{ left: "Cara", right: "Ben", count: 1, timing: "night_2" }] },
  ]);
  await block.getByRole("button", { name: "Remove", exact: true }).click();
  expect((await exportPuzzleDoc(page)).claims).toEqual([]);
  await addAndFillClaims(page, [{ type: "Chambermaid", name: "Ben", checks: [] }]);
  expect((await exportPuzzleDoc(page)).claims).toEqual([{ type: "Chambermaid", name: "Ben", checks: [] }]);
});

test("enforces player selection limits and lets users replace role choices", async ({ page }) => {
  await enterPuzzle(page, {
    title: "Selections",
    players: ["Ada", "Ben", "Cara"],
    setup: "none",
    script: ["Knight", "Dreamer", "Chef", "Imp", "Soldier"],
    claims: [{ type: "Knight", name: "Ada", noDemonAmong: ["Ben", "Cara"] }],
  });
  let block = claimsPanel(page).locator(".claim-block");
  await expect(block.getByLabel("Ada", { exact: true })).toBeDisabled();
  await block.getByLabel("Ben", { exact: true }).uncheck();
  await checkPlayers(block, "No demon among", ["Ada"]);
  expect((await exportPuzzleDoc(page)).claims[0]).toEqual({
    type: "Knight",
    name: "Ada",
    noDemonAmong: ["Cara", "Ada"],
  });
  await addAndFillClaims(page, [{ type: "Dreamer", name: "Ben", player: "Cara", roles: ["Chef", "Imp"] }]);
  block = claimsPanel(page).locator(".claim-block");
  await block.getByRole("button", { name: /Chef/ }).click();
  await addRoleToList(block, "Dreamer possible roles", "Soldier");
  expect((await exportPuzzleDoc(page)).claims[1]).toEqual({
    type: "Dreamer",
    name: "Ben",
    player: "Cara",
    roles: ["Imp", "Soldier"],
  });
});

test("switches conditional fields and preserves only the selected ability", async ({ page }) => {
  await enterPuzzle(page, {
    title: "Changing a choice",
    players: ["Ada", "Ben", "Cara"],
    setup: "none",
    script: ["Philosopher", "Seamstress", "Chef"],
    claims: [
      {
        type: "Philosopher",
        name: "Ada",
        role: "Seamstress",
        timing: "night_1",
        seamstress: { among: ["Ben", "Cara"], aligned: true },
      },
    ],
  });
  const block = claimsPanel(page).locator(".claim-block");
  await fillRoleField(block, "Chosen role", "Chef");
  await expect(block.getByText("Seamstress left", { exact: true })).toHaveCount(0);
  expect((await exportPuzzleDoc(page)).claims).toEqual([
    { type: "Philosopher", name: "Ada", role: "Chef", timing: "night_1" },
  ]);
});

test("creates timeline events, including nobody dying and multiple deaths", async ({ page }) => {
  const timeline: readonly TimelineEventDoc[] = [
    { type: "execution", timing: "day_1", players: ["Ben"] },
    { type: "nightDeath", timing: "night_2", players: [] },
    { type: "survivedExecution", timing: "day_2", players: ["Cara"] },
    { type: "nightDeath", timing: "night_3", players: ["Ada", "Cara"] },
    { type: "resurrection", timing: "night_4", players: ["Ada"] },
    { type: "slayerShot", timing: "day_4", players: ["Ada"], caller: "Ben" },
    { type: "witchCurse", timing: "day_5", players: ["Ben"], caller: "Cara", sourceActedBeforeDeath: true },
    { type: "nominationDeath", timing: "day_6", players: ["Cara"], caller: "Ada" },
    { type: "tinkerDeath", timing: "day_7", players: ["Ada"] },
    { type: "doomsayerDeath", timing: "day_8", players: ["Ben"], caller: "Cara" },
  ];
  const doc: PuzzleDoc = {
    title: "Timeline controls",
    players: ["Ada", "Ben", "Cara"],
    script: [],
    claims: [],
    timeline,
  };
  await enterPuzzle(page, doc);
  await expect(page.getByLabel("Puzzle timeline").getByText("Nobody", { exact: true })).toBeVisible();
  expect(comparableDoc(await exportPuzzleDoc(page))).toEqual(comparableDoc(doc));
});

test("edits advanced puzzle rules and constraints and recovers from invalid expressions", async ({ page }) => {
  await enterPuzzle(page, {
    title: "Advanced controls",
    players: ["Ada", "Ben", "Cara", "Drew", "Eve"],
    setup: "none",
    uniqueCharacters: false,
    script: ["Artist", "Chef", "Soldier", "Imp", "Scarlet Woman"],
    claims: [{ type: "Artist", name: "Ada" }],
    constraints: [{ expression: "Ben.initial_role == Imp" }],
  });
  const advanced = page.locator("details.advanced-puzzle-rules");
  await advanced.getByLabel("Atheist puzzle rules").check();
  expect((await exportPuzzleDoc(page)).setup).toBe("atheist");
  await advanced.getByLabel("Atheist puzzle rules").uncheck();
  await advanced.getByLabel("Unique actual characters").check();
  const constraint = page.locator("section.panel", { hasText: "Custom constraints" }).locator(".claim-block");
  await fillField(constraint, "Expression", "Ben.initial_role ==");
  await expect(page.locator(".solve-panel").getByRole("alert")).toHaveText("Unexpected eof");
  await fillField(constraint, "Expression", "Ben.initial_role == Imp");
  await expect(page.locator(".solve-panel .error")).toHaveCount(0);
  await constraint.getByRole("button", { name: "Remove", exact: true }).click();
  const exported = await exportPuzzleDoc(page);
  expect(exported.setup).toBeUndefined();
  expect(exported.uniqueCharacters).toBeUndefined();
  expect(exported.constraints).toBeUndefined();
  await setCustomConstraints(page, { ...exported, constraints: [{ expression: "Cara.initial_role == Imp" }] });
  expect((await exportPuzzleDoc(page)).constraints).toEqual([{ expression: "Cara.initial_role == Imp" }]);
});

test("adds and removes hidden roles and protects roles used by puzzle facts", async ({ page }) => {
  await enterPuzzle(page, {
    title: "Script editing",
    players: ["Ada", "Ben", "Cara"],
    setup: "none",
    script: [],
    claims: [{ type: "Chef", name: "Ada", count: 0 }],
  });
  expect((await exportPuzzleDoc(page)).script).toEqual(["Chef"]);
  const hiddenRoles = page.getByLabel("Potential hidden roles", { exact: true });
  await page.getByLabel("Add hidden role").fill("Imp");
  const imp = hiddenRoles.getByRole("button", { name: /Imp/ });
  await expect(imp).toBeEnabled();
  expect((await exportPuzzleDoc(page)).script).toEqual(["Chef", "Imp"]);
  await imp.click();
  expect((await exportPuzzleDoc(page)).script).toEqual(["Chef"]);
  const doc = await exportPuzzleDoc(page);
  await setCustomConstraints(page, { ...doc, constraints: [{ expression: "Ben.initial_role == Imp" }] });
  await expect(imp).toBeDisabled();
  expect((await exportPuzzleDoc(page)).script).toEqual(["Chef", "Imp"]);
});

test("rejects an invalid import without losing edits and accepts a corrected file", async ({ page }) => {
  const doc: PuzzleDoc = {
    title: "Keep my work",
    players: ["Ada", "Ben", "Cara"],
    setup: "none",
    script: ["Chef"],
    claims: [{ type: "Chef", name: "Ada", count: 1 }],
  };
  await enterPuzzle(page, doc);
  const fileInput = page.locator('input[type="file"]');
  await fileInput.setInputFiles({
    name: "puzzle.json",
    mimeType: "application/json",
    buffer: Buffer.from(JSON.stringify({ ...doc, players: "Ada" })),
  });
  await expect(page.locator(".solve-panel .error")).toContainText("players");
  expect(comparableDoc(await exportPuzzleDoc(page))).toEqual(comparableDoc(doc));
  await fileInput.setInputFiles({
    name: "puzzle.json",
    mimeType: "application/json",
    buffer: Buffer.from(JSON.stringify({ ...doc, title: "Corrected import" })),
  });
  await expect(page.getByLabel("Title", { exact: true })).toHaveValue("Corrected import");
  await expect(page.locator(".solve-panel .error")).toHaveCount(0);
  expect(comparableDoc(await exportPuzzleDoc(page))).toEqual(comparableDoc({ ...doc, title: "Corrected import" }));
});
