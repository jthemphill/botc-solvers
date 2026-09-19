import { expect, test, type Page } from "@playwright/test";
import { readFileSync } from "node:fs";
import type { PuzzleDoc } from "../../src/schema/puzzleDoc";

async function exportedDoc(page: Page): Promise<PuzzleDoc> {
  const pending = page.waitForEvent("download");
  await page.getByRole("button", { name: "Export JSON", exact: true }).click();
  const download = await pending;
  const path = await download.path();
  if (!path) throw new Error("The puzzle download is missing.");
  return JSON.parse(readFileSync(path, "utf8"));
}

for (const width of [1440, 820, 390]) {
  for (const view of ["Seating chart", "Roster"]) {
    test(`toggles the same player's card in ${view} at ${width}px`, async ({ page }) => {
      await page.setViewportSize({ width, height: 900 });
      await page.goto("/");
      await page.getByRole("button", { name: view, exact: true }).click();
      await page.getByRole("button", { name: "Paste roster", exact: true }).click();
      await page
        .getByLabel("Players and claimed characters")
        .fill("Ada = Empath\nBen = Chef\nCara = Soldier\nDrew = Recluse\nEve = Slayer");
      await page.getByRole("button", { name: "Use roster", exact: true }).click();

      const card = page.getByLabel("Puzzle workbench", { exact: true });
      const playerButton = (seat: number, name: string) =>
        page.getByRole("button", {
          name:
            view === "Roster"
              ? `Edit claims for ${name}`
              : new RegExp(`^${width <= 760 ? "Player" : "Seat"} ${seat}: ${name}\\.`),
        });
      const ada = playerButton(1, "Ada");
      const ben = playerButton(2, "Ben");
      await expect(card.getByRole("heading", { name: "Ada", exact: true })).toBeVisible();
      await card.getByLabel("Count", { exact: true }).fill("1");
      await ada.click();
      await expect(card).toBeHidden();

      await ada.click();
      await expect(card.getByRole("heading", { name: "Ada", exact: true })).toBeVisible();
      await expect(card.getByLabel("Count", { exact: true })).toHaveValue("1");
      await ben.click();
      await expect(card.getByRole("heading", { name: "Ben", exact: true })).toBeVisible();
      await card.getByRole("button", { name: "Previous player", exact: true }).click();
      await expect(card.getByRole("heading", { name: "Ada", exact: true })).toBeVisible();
      await ada.click();
      await expect(card).toBeHidden();

      await ada.press("Enter");
      await expect(card.getByRole("heading", { name: "Ada", exact: true })).toBeVisible();
      await ada.press("Space");
      await expect(card).toBeHidden();
    });
  }
}

test("creates seven named character claims with one paste and two clicks", async ({ page }) => {
  await page.goto("/");
  await expect(page.getByLabel("Clockwise seating chart")).toBeVisible();
  await expect(page.getByLabel("Puzzle workbench")).toBeHidden();
  await page.getByRole("button", { name: "Paste roster", exact: true }).click();
  const entry = page.getByLabel("Players and claimed characters");
  await expect(entry).toBeFocused();
  await entry.fill(
    "Sula = Investigator\nMatthew = Washerwoman\nOscar = Librarian\nJosh = Empath\nYou = Slayer\nAoife = Chef\nTom = Recluse",
  );
  await expect(page.getByRole("status")).toHaveText("7 players · 7 claims");
  await page.getByRole("button", { name: "Use roster", exact: true }).click();
  const doc = await exportedDoc(page);
  expect(doc.players).toEqual(["Sula", "Matthew", "Oscar", "Josh", "You", "Aoife", "Tom"]);
  expect(doc.claims.map(({ name, type }) => [name, type])).toEqual([
    ["Sula", "Investigator"],
    ["Matthew", "Washerwoman"],
    ["Oscar", "Librarian"],
    ["Josh", "Empath"],
    ["You", "Slayer"],
    ["Aoife", "Chef"],
    ["Tom", "Recluse"],
  ]);
});

test("rejects duplicate names and unknown roles without changing the puzzle", async ({ page }) => {
  await page.goto("/");
  await page.getByRole("button", { name: "Paste roster", exact: true }).click();
  const entry = page.getByLabel("Players and claimed characters");
  await entry.fill("Anna = Empath\nAnna = Chef");
  await expect(page.getByRole("status")).toContainText("different name");
  await expect(page.getByRole("button", { name: "Use roster" })).toBeDisabled();
  await entry.fill("Anna = Not a character");
  await expect(page.getByRole("status")).toContainText("not supported");
  await entry.press("Control+Enter");
  await expect(entry).toBeVisible();
  await entry.fill("Anna = Empath = 1");
  await expect(page.getByRole("status")).toContainText("one character per line");
  await expect(page.getByRole("button", { name: "Use roster" })).toBeDisabled();
  await entry.press("Escape");
  expect((await exportedDoc(page)).claims).toEqual([]);
});

test("enters names and characters from the keyboard without returning to the toolbar", async ({ page }) => {
  await page.goto("/");
  await page.getByRole("button", { name: "Roster", exact: true }).click();
  const name = page.getByLabel("Player 1 name", { exact: true });
  await name.fill("Ada");
  await name.press("Tab");
  const character = page.getByLabel("Claim for Ada", { exact: true });
  await expect(character).toBeFocused();
  await character.fill("Che");
  await character.press("Enter");
  await expect(page.getByLabel("Player 2 name", { exact: true })).toBeFocused();
  expect((await exportedDoc(page)).claims).toContainEqual({ name: "Ada", type: "Chef", count: 0 });
});

test("appends pasted players without losing existing observations", async ({ page }) => {
  await page.goto("/");
  await page.getByLabel("Load example puzzle").selectOption("puzzle-03a-not-throwing-away-my-shot");
  const before = await exportedDoc(page);
  await page.getByRole("button", { name: "Paste roster", exact: true }).click();
  const entry = page.getByLabel("Players and claimed characters");
  await entry.fill("Ada\tKnight\nBen\tChef");
  await entry.press("Control+Enter");
  const after = await exportedDoc(page);
  expect(after.players).toEqual([...before.players, "Ada", "Ben"]);
  expect(after.claims.slice(0, before.claims.length)).toEqual(before.claims);
  expect(after.timeline).toEqual(before.timeline);
  expect(after.constraints).toEqual(before.constraints);
  expect(after.script).toEqual(expect.arrayContaining([...before.script]));
});

test("keeps the reference puzzle visible when opening and closing claim details", async ({ page }) => {
  await page.setViewportSize({ width: 1440, height: 1100 });
  await page.goto("/");
  await page.getByLabel("Load example puzzle").selectOption("puzzle-03a-not-throwing-away-my-shot");
  const chart = page.getByLabel("Clockwise seating chart");
  const before = await chart.boundingBox();
  await page.getByRole("button", { name: /Seat 1: Sula\./ }).click();
  await expect(page.getByLabel("Puzzle workbench")).toBeVisible();
  expect(await chart.boundingBox()).toEqual(before);
  await page.getByRole("button", { name: "Close claim editor", exact: true }).click();
  await expect(page.getByLabel("Puzzle workbench")).toBeHidden();
  await expect(chart.locator(".claim-callout")).toHaveCount(7);
  const overlaps = await chart.evaluate((element) => {
    const boxes = [...element.querySelectorAll(".claim-callout, .seat-button")].map((node) =>
      node.getBoundingClientRect(),
    );
    return boxes.flatMap((box, index) =>
      boxes
        .slice(index + 1)
        .filter(
          (other) =>
            Math.min(box.right, other.right) > Math.max(box.left, other.left) &&
            Math.min(box.bottom, other.bottom) > Math.max(box.top, other.top),
        ),
    );
  });
  expect(overlaps).toEqual([]);
  await expect(page.getByText("The game continues after the last event.", { exact: true })).toBeInViewport();
});

test("creates a roster and edits a report on a phone without horizontal scrolling", async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 844 });
  await page.goto("/");
  await page.getByRole("button", { name: "Paste roster", exact: true }).click();
  await page
    .getByLabel("Players and claimed characters")
    .fill("Anna = Empath\nTim = Chef\nSula = Steward\nMatt = Knight\nOscar = Librarian\nYou = Slayer");
  await page.getByRole("button", { name: "Use roster" }).click();
  await expect(page.getByLabel("Puzzle workbench")).toBeVisible();
  await page.getByRole("button", { name: "Close claim editor" }).click();
  await page.getByRole("button", { name: /Player 2: Tim\./ }).click();
  await expect(page.locator("#claims-panel").getByRole("heading", { name: "Tim", exact: true })).toBeVisible();
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth)).toBe(true);
});
