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

test("player count input does not retain a leading zero", async ({ page }) => {
  await page.goto("/");

  const countInput = page.getByLabel("Players");
  await countInput.fill("");
  await countInput.press("0");
  await countInput.press("9");

  await expect(countInput).toHaveValue("9");
  await expect(page.locator(".seat-button")).toHaveCount(9);
});

test("removes a seat by dragging it to the trash zone", async ({ page }) => {
  await page.goto("/");

  const firstSeat = page.getByRole("button", { name: /Seat 1: Player 1\./ });
  const trashZone = page.locator(".seat-trash-zone");

  await expect(firstSeat).toBeVisible();
  await expect(trashZone).toHaveCount(0);

  const dataTransfer = await page.evaluateHandle(() => new DataTransfer());
  await firstSeat.dispatchEvent("dragstart", { dataTransfer });

  await expect(trashZone).toBeVisible();

  await trashZone.dispatchEvent("dragenter", { dataTransfer });
  await trashZone.dispatchEvent("dragover", { dataTransfer });
  await trashZone.dispatchEvent("drop", { dataTransfer });

  await expect(page.getByRole("button", { name: /Seat 1: Player 2\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Seat 1: Player 1\./ })).toHaveCount(0);
  await expect(trashZone).toHaveCount(0);
});

test("adds and refines deaths from the timeline panel", async ({ page }) => {
  await page.goto("/");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toBeVisible();
  await expect(timeline).toContainText("Drag a player to record the first death.");

  const player1 = page.getByRole("button", { name: /Seat 1: Player 1\./ });
  const executionDrop = page.locator(".timeline-drop-zone.execution");
  const executionData = await page.evaluateHandle(() => new DataTransfer());
  await player1.dispatchEvent("dragstart", { dataTransfer: executionData });
  await executionDrop.dispatchEvent("dragenter", { dataTransfer: executionData });
  await executionDrop.dispatchEvent("dragover", { dataTransfer: executionData });
  await executionDrop.dispatchEvent("drop", { dataTransfer: executionData });

  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Player 1");
  await expect(page.getByRole("button", { name: /Seat 1: Player 1, executed/ })).toBeVisible();

  const details = page.locator(".timeline-event-details");
  await details.getByLabel("Cause").selectOption("slayerShot");
  await expect(timeline).toContainText("D1 Slayer Shot");
  await expect(page.getByRole("button", { name: /Seat 1: Player 1, died to a Slayer shot/ })).toBeVisible();

  const player2 = page.getByRole("button", { name: /Seat 2: Player 2\./ });
  const nightDrop = page.locator(".timeline-drop-zone.night-kill");
  const nightData = await page.evaluateHandle(() => new DataTransfer());
  await player2.dispatchEvent("dragstart", { dataTransfer: nightData });
  await nightDrop.dispatchEvent("dragenter", { dataTransfer: nightData });
  await nightDrop.dispatchEvent("dragover", { dataTransfer: nightData });
  await nightDrop.dispatchEvent("drop", { dataTransfer: nightData });

  await details.getByLabel("Player 3").check();

  await expect(timeline).toContainText("N2 Night Deaths");
  await expect(timeline).toContainText("Player 2 or Player 3");
  await expect(page.getByRole("button", { name: /Seat 2: Player 2, killed at night/ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Seat 3: Player 3, killed at night/ })).toBeVisible();
});

test("keeps mobile timeline drop zones on one row", async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 900 });
  await page.goto("/");

  const executionBox = await page.locator(".timeline-drop-zone.execution").boundingBox();
  const nightDeathBox = await page.locator(".timeline-drop-zone.night-kill").boundingBox();
  const timelineBox = await page.locator(".timeline-main").boundingBox();

  expect(executionBox).not.toBeNull();
  expect(nightDeathBox).not.toBeNull();
  expect(timelineBox).not.toBeNull();
  expect(Math.abs((executionBox?.y ?? 0) - (nightDeathBox?.y ?? 0))).toBeLessThan(2);
  expect(executionBox?.x ?? 0).toBeLessThan(nightDeathBox?.x ?? 0);
  expect(timelineBox?.y ?? 0).toBeGreaterThan((executionBox?.y ?? 0) + (executionBox?.height ?? 0) - 1);
});
