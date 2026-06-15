import { expect, test } from "@playwright/test";

test("loads puzzle 34 with structured role clues", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-34-the-vortox-conjecture");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 34 - The Vortox Conjecture");
  const setupSummary = page.getByLabel("Puzzle setup summary");
  await expect(setupSummary.getByLabel("5 Townsfolk")).toBeVisible();
  await expect(setupSummary.getByLabel("0 Outsider")).toBeVisible();
  await expect(setupSummary.getByLabel("1 Minion")).toBeVisible();
  await expect(setupSummary.getByLabel("1 Demon")).toBeVisible();
  await expect(setupSummary).toContainText("7 players · 1 demon · 1 minion · 0 outsider");
  await expect(page.getByRole("button", { name: /Demon 3 steps from Minion/ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Steph and Aoife are same/ })).toBeVisible();
  await expect(
    page.getByRole("button", { name: /1 malfunction \(Night 1\); 0 malfunctions \(Night 2\)/ }),
  ).toBeVisible();

  await page.getByRole("button", { name: /Claims/ }).click();

  await expect(page.getByText("Demon-minion distance").first()).toBeVisible();
  await expect(page.getByText("Malfunctions").first()).toBeVisible();
  await expect(page.getByText("Aoife.role == `No Dashii`").first()).toBeVisible();

  await page.getByRole("navigation", { name: "Workbench sections" }).getByRole("button", { name: /Solve/ }).click();
  await page.locator(".solve-panel").getByRole("button", { name: "Solve" }).click();

  await expect(page.getByText("Satisfying worlds:")).toBeVisible();
  await expect(page.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  const sula = page.getByLabel("Sula: Vortox, claimed Clockmaker");
  await expect(sula).toBeVisible();
  await expect(sula).toContainText("Vortox");
  await expect(sula).not.toContainText("Clockmaker");
  await expect(sula).toHaveCSS("border-top-color", "rgb(165, 43, 43)");
});
