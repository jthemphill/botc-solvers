import { expect, test, type Page } from "@playwright/test";
import { readFileSync } from "node:fs";
import type { PuzzleDoc } from "../../src/schema/puzzleDoc";

const reference = JSON.parse(
  readFileSync(new URL("../../src/examples/puzzle-03a-not-throwing-away-my-shot.json", import.meta.url), "utf8"),
) as PuzzleDoc;

test.use({ viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true });

async function exportDoc(page: Page): Promise<PuzzleDoc> {
  const pending = page.waitForEvent("download");
  await page.getByRole("button", { name: "Export JSON", exact: true }).click();
  const path = await (await pending).path();
  if (!path) throw new Error("The puzzle download is missing.");
  return JSON.parse(readFileSync(path, "utf8"));
}

async function pasteRoster(page: Page, text: string) {
  await page.getByRole("button", { name: "Paste roster", exact: true }).click();
  await page.getByLabel("Players and claimed characters").fill(text);
  await page.getByRole("button", { name: "Use roster", exact: true }).click();
}

async function expectNoOverflow(page: Page) {
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth)).toBe(true);
}

test("recreates the reference puzzle with inline reports and one hidden-role picker", async ({ page }) => {
  await page.goto("/");
  await page.getByLabel("Title", { exact: true }).fill(reference.title!);
  await pasteRoster(page, reference.claims.map((claim) => `${claim.name} = ${claim.type}`).join("\n"));
  await expect(
    page.locator(".mobile-player-row").first().getByRole("region", { name: "Puzzle workbench" }),
  ).toBeVisible();
  await page.getByRole("button", { name: "Close claim editor" }).click();
  await page.getByRole("button", { name: "Choose hidden roles" }).click();
  const picker = page.getByRole("dialog", { name: "Choose hidden roles" });
  await picker.getByRole("button", { name: "Minions", exact: true }).click();
  for (const role of ["Baron", "Spy", "Poisoner", "Scarlet Woman"]) {
    await picker.getByRole("checkbox", { name: role, exact: true }).check();
    await expect(picker).toBeVisible();
  }
  await picker.getByRole("button", { name: "Demons", exact: true }).click();
  await picker.getByRole("checkbox", { name: "Imp", exact: true }).check();
  await picker.getByRole("button", { name: "Outsiders", exact: true }).click();
  await picker.getByRole("checkbox", { name: "Drunk", exact: true }).check();
  await picker.getByRole("button", { name: "Close hidden role picker" }).click();
  await page.getByRole("button", { name: /Player 1: Sula\./ }).click();
  const panel = page.locator("#claims-panel");
  await panel.getByLabel("Investigator minion role", { exact: true }).fill("Baron");
  await panel.getByRole("checkbox", { name: "You", exact: true }).check();
  await panel.getByRole("checkbox", { name: "Aoife", exact: true }).check();
  await panel.getByRole("button", { name: "Next player" }).click();
  await expect(panel.getByRole("heading", { name: "Matthew", exact: true })).toBeInViewport();
  await panel.getByLabel("Washerwoman townsfolk role", { exact: true }).fill("Librarian");
  await panel.getByRole("checkbox", { name: "Aoife", exact: true }).check();
  await panel.getByRole("checkbox", { name: "Oscar", exact: true }).check();
  for (const name of ["Oscar", "Josh", "You"]) {
    await panel.getByRole("button", { name: "Next player" }).click();
    await expect(panel.getByRole("heading", { name, exact: true })).toBeInViewport();
  }
  await panel.getByLabel("Shot player", { exact: true }).selectOption("Tom");
  await panel.getByLabel("Target died", { exact: true }).selectOption("yes");
  await page.getByRole("button", { name: "Close claim editor" }).click();
  await expect(page.getByRole("button", { name: /Player 5: You\./ })).toBeFocused();
  await expect(page.getByLabel("Puzzle timeline")).toContainText("D1 Slayer Shot");
  await expectNoOverflow(page);
  const actual = await exportDoc(page);
  expect(actual.title).toBe(reference.title);
  expect(actual.players).toEqual(reference.players);
  expect([...actual.script].sort()).toEqual([...reference.script].sort());
  expect(actual.timeline).toEqual(reference.timeline);
  expect(actual.claims).toHaveLength(reference.claims.length);
  for (const [index, claim] of reference.claims.entries()) {
    const actualClaim = actual.claims[index]!;
    expect(
      actualClaim.type === "Librarian" ? { ...actualClaim, among: actualClaim.among ?? [] } : { ...actualClaim },
    ).toMatchObject({ ...claim });
  }
});

test("keeps report controls usable in a short viewport and preserves edits across breakpoints", async ({ page }) => {
  await page.setViewportSize({ width: 320, height: 480 });
  await page.goto("/");
  await pasteRoster(
    page,
    "Anna = Empath\nBen = Chef\nCara = Recluse\nDrew = Slayer\nEve = Librarian\nFinn = Investigator",
  );
  const count = page.locator("#claims-panel").getByLabel("Count", { exact: true });
  await count.fill("1");
  await expect(count).toHaveCSS("font-size", "16px");
  const tooSmall = await page
    .locator("#claims-panel button, #claims-panel input:not([type=checkbox]), #claims-panel select")
    .evaluateAll((controls) =>
      controls
        .filter((element) => element.getBoundingClientRect().height > 0 && element.getBoundingClientRect().height < 44)
        .map((element) => element.textContent),
    );
  expect(tooSmall).toEqual([]);
  await expectNoOverflow(page);
  await page.setViewportSize({ width: 1280, height: 900 });
  await expect(page.getByLabel("Clockwise seating chart")).toBeVisible();
  await expect(count).toHaveValue("1");
  await page.setViewportSize({ width: 390, height: 844 });
  await expect(page.locator(".mobile-player-row").first().getByLabel("Count", { exact: true })).toHaveValue("1");
  await page.getByRole("button", { name: "Close claim editor" }).click();
  await expect(page.getByRole("button", { name: /Player 1: Anna\./ })).toBeFocused();
});

test("adds later reports in the same player card without changing the original report", async ({ page }) => {
  await page.goto("/");
  await page.getByRole("button", { name: "Roster", exact: true }).click();
  await pasteRoster(
    page,
    "Anna = Empath\nBen = Chef\nCara = Recluse\nDrew = Slayer\nEve = Librarian\nFinn = Investigator",
  );
  const row = page.locator(".roster-row").first();
  await row.getByLabel("Count", { exact: true }).fill("1");
  await row.getByText("Add another report", { exact: true }).click();
  await row.getByLabel("Claim type", { exact: true }).fill("Empath");
  await row.getByRole("button", { name: "+ Add claim", exact: true }).click();
  await row.getByLabel("Count", { exact: true }).last().fill("2");
  await row.getByLabel("Timing", { exact: true }).last().selectOption("night_2");
  await row.getByLabel("Selected player name").fill("Ada");
  await row.getByLabel("Selected player name").press("Tab");
  await page.getByRole("button", { name: "Close claim editor" }).click();
  await expect(page.getByRole("button", { name: "Edit claims for Ada", exact: true })).toContainText("2 reports");
  const actual = await exportDoc(page);
  expect(actual.players[0]).toBe("Ada");
  expect(actual.claims.filter((claim) => claim.name === "Ada")).toEqual([
    { name: "Ada", type: "Empath", count: 1 },
    { name: "Ada", type: "Empath", count: 2, timing: "night_2" },
  ]);
});

test("keeps hidden role choices and locked roles safe in a short viewport", async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 480 });
  await page.goto("/");
  await page.getByLabel("Load example puzzle").selectOption("puzzle-03a-not-throwing-away-my-shot");
  await page.getByRole("button", { name: "Choose hidden roles" }).click();
  const picker = page.getByRole("dialog", { name: "Choose hidden roles" });
  await picker.getByLabel("Search hidden roles").fill("Baron");
  await expect(picker.getByRole("checkbox", { name: "Baron", exact: true })).toBeDisabled();
  await picker.getByLabel("Search hidden roles").fill("Poisoner");
  await picker.getByRole("checkbox", { name: "Poisoner", exact: true }).uncheck();
  await expect(picker.getByRole("button", { name: "Close hidden role picker" })).toBeInViewport();
  const box = await picker.boundingBox();
  expect(box!.height).toBeLessThanOrEqual(480);
  await expectNoOverflow(page);
  await picker.getByRole("button", { name: "Close hidden role picker" }).press("Escape");
  await expect(picker).toBeHidden();
  const actual = await exportDoc(page);
  expect(actual.script).toContain("Baron");
  expect(actual.script).not.toContain("Poisoner");
});
