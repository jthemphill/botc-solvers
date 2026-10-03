import { expect, test } from "@playwright/test";
import { enterPuzzle, exportPuzzleDoc } from "./editor-helpers";

test("edits, solves, exports, and imports the no kill sinking assumption", async ({ page }) => {
  const roles = { Ada: "Imp", Ben: "Chef", Cara: "Empath", Drew: "Steward", Eve: "Noble" };
  await enterPuzzle(page, {
    title: "A missing night death",
    players: Object.keys(roles),
    script: Object.values(roles),
    setup: "none",
    claims: [],
    constraints: Object.entries(roles).map(([player, role]) => ({ expression: `${player}.initial_role == ${role}` })),
    timeline: [
      { timing: "day_1", type: "execution", players: ["Ben"] },
      { timing: "night_2", type: "nightDeath", players: [] },
    ],
  });
  const count = page
    .getByRole("region", { name: "Solutions", exact: true })
    .getByText("Satisfying worlds:")
    .locator("strong");
  const option = page.getByLabel("Abilities never target dead players to kill");
  await expect(count).toHaveText("1");
  await option.check();
  await expect(count).toHaveText("0");
  const exported = await exportPuzzleDoc(page);
  expect(exported.noKillSinking).toBe(true);
  await page.getByRole("button", { name: "New Puzzle", exact: true }).click();
  await page.locator('input[type="file"]').setInputFiles({
    name: "targets.json",
    mimeType: "application/json",
    buffer: Buffer.from(JSON.stringify(exported)),
  });
  await expect(count).toHaveText("0");
  if (!(await option.isVisible())) await page.locator("details.advanced-puzzle-rules summary").click();
  await expect(option).toBeChecked();
  await option.uncheck();
  await expect(count).toHaveText("1");
  expect((await exportPuzzleDoc(page)).noKillSinking).toBeUndefined();
});
