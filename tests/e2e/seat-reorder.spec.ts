import { expect, test } from "@playwright/test";

test("reorders seats by dragging one player token onto another", async ({ page }) => {
  await page.goto("/");

  const firstSeat = page.getByRole("button", { name: /Seat 1: Player 1\./ });
  const thirdSeat = page.getByRole("button", { name: /Seat 3: Player 3\./ });

  await expect(firstSeat).toBeVisible();
  await expect(thirdSeat).toBeVisible();

  await firstSeat.dragTo(thirdSeat);

  await expect(page.getByRole("button", { name: /Seat 1: Player 2\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Seat 2: Player 3\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Seat 3: Player 1\./ })).toBeVisible();
  await expect(page.getByRole("heading", { name: "Selected: Player 1" })).toBeVisible();
  await expect(page.getByText("Seat 3 · left Player 4 · right Player 3")).toBeVisible();
});
