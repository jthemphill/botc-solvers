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
  await expect(page.locator(".center-timeline").getByText("Player 1")).toBeVisible();
  await expect(page.locator(".selected-player-panel")).toHaveCount(0);
});

test("renames a seat inline after double-clicking it", async ({ page }) => {
  await page.goto("/");

  await page.getByRole("button", { name: /Seat 1: Player 1\./ }).dblclick();

  const nameInput = page.getByLabel("Rename Player 1");
  await expect(nameInput).toHaveValue("Player 1");
  await nameInput.fill("Alice");
  await nameInput.press("Enter");

  await expect(page.getByRole("button", { name: /Seat 1: Alice\./ })).toBeVisible();
  await expect(page.locator(".selected-player-panel")).toHaveCount(0);
});

test("removes a seat by dragging it to the trash zone", async ({ page }) => {
  await page.goto("/");

  const firstSeat = page.getByRole("button", { name: /Seat 1: Player 1\./ });
  const trashZone = page.locator(".seat-trash-zone");

  await expect(firstSeat).toBeVisible();
  await expect(trashZone).toBeVisible();

  await firstSeat.dragTo(trashZone);

  await expect(page.getByRole("button", { name: /Seat 1: Player 2\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Seat 1: Player 1\./ })).toHaveCount(0);
});
