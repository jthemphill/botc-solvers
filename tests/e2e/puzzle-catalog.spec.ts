import { expect, test } from "@playwright/test";

test("loads puzzle 34 with its custom clue text", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-34-the-vortox-conjecture");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 34 - The Vortox Conjecture");
  await expect(page.getByRole("button", { name: /Demon is 3 steps from the Witch/ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Steph and Aoife are the same alignment/ })).toBeVisible();
  await expect(page.getByRole("button", { name: /1 ability malfunctioned; 0 abilities malfunctioned/ })).toBeVisible();

  await page.getByRole("button", { name: /Claims/ }).click();

  await expect(page.getByText("Demon is 3 steps from the Witch").first()).toBeVisible();
  await expect(page.getByText("malfunctions(night_1, 1)").first()).toBeVisible();
});
