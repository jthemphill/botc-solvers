import { expect, test } from "@playwright/test";
import { claimsPanel, enterPuzzle, exportPuzzleDoc, fillRoleField, selectPlayerClaims } from "./editor-helpers";

test("enters, solves, edits, exports, and imports a Philosopher Nightwatchman signal", async ({ page }) => {
  await enterPuzzle(page, {
    title: "A misleading signal",
    players: ["Ada", "Ben", "Cara", "Drew"],
    setup: "none",
    script: ["Philosopher", "Nightwatchman", "Chef", "Soldier", "Vortox"],
    constraints: [
      "Ada.initial_role == Philosopher",
      "Ben.initial_role == Chef",
      "Cara.initial_role == Soldier",
      "Drew.initial_role == Vortox",
    ].map((expression) => ({ expression })),
    claims: [
      { type: "Philosopher", name: "Ada", role: "Nightwatchman", timing: "night_1" },
      { type: "Chef", name: "Ben", count: 1 },
    ],
  });
  const block = claimsPanel(page).locator(".claim-block");
  const count = page
    .getByRole("region", { name: "Solutions", exact: true })
    .getByText("Satisfying worlds:")
    .locator("strong");
  await selectPlayerClaims(page, "Ada");
  await block.getByLabel("Nightwatchman chosen player", { exact: true }).selectOption("Ben");
  await block.getByLabel("Nightwatchman choice timing", { exact: true }).selectOption("night_1");
  await selectPlayerClaims(page, "Ben");
  await block.getByRole("button", { name: "+ Add received Nightwatchman signal", exact: true }).click();
  await block.getByLabel("Learned Nightwatchman", { exact: true }).selectOption("Cara");
  await expect(count).toHaveText("1");
  await block.getByLabel("Learned Nightwatchman", { exact: true }).selectOption("Ada");
  await expect(count).toHaveText("0");
  await block.getByLabel("Learned Nightwatchman", { exact: true }).selectOption("Cara");
  await block.getByLabel("Signal timing", { exact: true }).selectOption("night_2");
  await expect(count).toHaveText("0");
  await block.getByLabel("Signal timing", { exact: true }).selectOption("night_1");
  await expect(count).toHaveText("1");
  const exported = await exportPuzzleDoc(page);
  expect(exported.claims[0]).toMatchObject({ nightwatchman: { chosen: "Ben", timing: "night_1" } });
  expect(exported.claims[1]?.nightwatchmanPings).toEqual([{ player: "Cara", timing: "night_1" }]);
  await page.getByRole("button", { name: "New Puzzle", exact: true }).click();
  await page.locator('input[type="file"]').setInputFiles({
    name: "signal.json",
    mimeType: "application/json",
    buffer: Buffer.from(JSON.stringify(exported)),
  });
  await expect(count).toHaveText("1");
  expect(await exportPuzzleDoc(page)).toEqual(exported);
  await selectPlayerClaims(page, "Ben");
  await block.getByRole("button", { name: "Remove Nightwatchman signal", exact: true }).click();
  expect((await exportPuzzleDoc(page)).claims[1]?.nightwatchmanPings).toBeUndefined();
  await selectPlayerClaims(page, "Ada");
  await fillRoleField(block, "Chosen role", "Chef");
  await expect(block.getByLabel("Nightwatchman chosen player", { exact: true })).toHaveCount(0);
  expect((await exportPuzzleDoc(page)).claims[0]).not.toHaveProperty("nightwatchman");
});
