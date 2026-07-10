import { expect, test } from "@playwright/test";

test("reorders seats by dragging one player token onto another", async ({ page }) => {
  await page.goto("/");

  const firstSeat = page.getByRole("button", { name: /Seat 1: Player 1\./ });
  const thirdSeat = page.getByRole("button", { name: /Seat 3: Player 3\./ });

  await expect(firstSeat).toBeVisible();
  await expect(thirdSeat).toBeVisible();

  const { start, end } = await page.evaluate(() => {
    const seats = [...document.querySelectorAll<HTMLElement>(".seating-chart .seat-button")].slice(0, 3);
    if (seats.length !== 3) throw new Error("Desktop drag targets must be visible");
    const centers = seats.map((seat) => {
      const rect = seat.getBoundingClientRect();
      return { x: rect.x + rect.width / 2, y: rect.y + rect.height / 2 };
    });
    return { start: centers[0], end: centers[2] };
  });
  if (start === undefined || end === undefined) throw new Error("Desktop drag targets must be visible");

  await page.mouse.move(start.x, start.y);
  await page.mouse.down();
  await page.mouse.move(end.x, end.y, { steps: 12 });

  const chart = page.getByLabel("Clockwise seating chart");
  await expect(chart.locator('[data-seat-index="0"]')).toHaveClass(/dragging/);
  await expect(chart.locator('[data-seat-index="1"]')).toHaveAttribute("data-preview-index", "0");
  await expect(chart.locator('[data-seat-index="2"]')).toHaveAttribute("data-preview-index", "1");
  await expect(chart.locator(".seat-drop-placeholder")).toBeVisible();
  await expect
    .poll(() =>
      page.evaluate(() => {
        const chart = document.querySelector<HTMLElement>(".seating-chart");
        const second = chart?.querySelector<HTMLElement>('[data-seat-index="1"]')?.getBoundingClientRect();
        const third = chart?.querySelector<HTMLElement>('[data-seat-index="2"]')?.getBoundingClientRect();
        const placeholder = chart?.querySelector<HTMLElement>(".seat-drop-placeholder")?.getBoundingClientRect();
        const chartRect = chart?.getBoundingClientRect();
        if (second === undefined || third === undefined || placeholder === undefined || chartRect === undefined)
          return false;
        const seatCenter = (index: number) => {
          const angle = (-90 + (index * 360) / 7) * (Math.PI / 180);
          return {
            x: chartRect.x + chartRect.width * (0.5 + Math.cos(angle) * 0.36),
            y: chartRect.y + chartRect.height * (0.5 + Math.sin(angle) * 0.36),
          };
        };
        const closeTo = (rect: DOMRect, point: { x: number; y: number }) =>
          Math.abs(rect.x + rect.width / 2 - point.x) < 2 && Math.abs(rect.y + rect.height / 2 - point.y) < 2;
        return closeTo(second, seatCenter(0)) && closeTo(third, seatCenter(1)) && closeTo(placeholder, seatCenter(2));
      }),
    )
    .toBe(true);
  await page.mouse.move(end.x + 1, end.y + 1);
  await page.mouse.up();

  await expect(page.getByRole("button", { name: /Seat 1: Player 2\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Seat 2: Player 3\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Seat 3: Player 1\./ })).toBeVisible();
  await expect(page.locator(".center-timeline").getByText("Player 1")).toBeVisible();
  await expect(page.locator(".selected-player-panel")).toHaveCount(0);
});

test("animates and reorders the mobile roster with continuous handle drags", async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 900 });
  await page.goto("/");

  const mobileList = page.locator(".mobile-player-list");
  const handle = page.getByRole("button", { name: "Reorder Player 1" });
  const target = page.getByRole("button", { name: /Player 3: Player 3\./ });
  await expect(handle).toBeVisible();
  await expect(target).toBeVisible();
  await expect(handle).toHaveCSS("user-select", "none");

  const { start, end, initialTops } = await page.evaluate(() => {
    const handleRect = document.querySelector('[data-seat-index="0"] .mobile-drag-handle')?.getBoundingClientRect();
    const targetRect = document.querySelector('[data-seat-index="2"]')?.getBoundingClientRect();
    const rows = [...document.querySelectorAll<HTMLElement>("[data-seat-index]")].slice(0, 3);
    if (handleRect === undefined || targetRect === undefined || rows.length !== 3)
      throw new Error("Mobile drag targets must be visible");
    return {
      start: { x: handleRect.x + handleRect.width / 2, y: handleRect.y + handleRect.height / 2 },
      end: { x: targetRect.x + targetRect.width / 2, y: targetRect.y + targetRect.height / 2 },
      initialTops: rows.map((row) => row.getBoundingClientRect().top),
    };
  });
  await page.mouse.move(start.x, start.y);
  await page.mouse.down();
  await expect(page.locator(".seat-trash-zone")).toBeHidden();
  const targetCenterAfterPointerDown = await page.evaluate(() => {
    const rect = document.querySelector('[data-seat-index="2"]')?.getBoundingClientRect();
    if (rect === undefined) throw new Error("Mobile drop target must remain visible");
    return rect.y + rect.height / 2;
  });
  expect(Math.abs(targetCenterAfterPointerDown - end.y)).toBeLessThan(1);
  await page.mouse.move(end.x, end.y, { steps: 12 });

  await expect(mobileList.locator('[data-seat-index="0"]')).toHaveClass(/dragging/);
  await expect(mobileList.locator('[data-seat-index="1"]')).toHaveClass(/shift-up/);
  await expect(mobileList.locator('[data-seat-index="2"]')).toHaveClass(/shift-up/);
  await expect(mobileList.locator('[data-seat-index="2"]')).toHaveAttribute("data-drop-target", "true");
  await expect
    .poll(() =>
      page.evaluate((tops) => {
        const rows = [...document.querySelectorAll<HTMLElement>("[data-seat-index]")].slice(0, 3);
        if (rows.length !== 3) return false;
        const previewTops = rows.map((row) => row.getBoundingClientRect().top);
        return (
          Math.abs((previewTops[0] ?? 0) - (tops[2] ?? 0)) < 2 &&
          Math.abs((previewTops[1] ?? 0) - (tops[0] ?? 0)) < 2 &&
          Math.abs((previewTops[2] ?? 0) - (tops[1] ?? 0)) < 2
        );
      }, initialTops),
    )
    .toBe(true);
  await page.mouse.up();

  await expect(page.getByRole("button", { name: /Player 1: Player 2\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Player 2: Player 3\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Player 3: Player 1\./ })).toBeVisible();
  await page.waitForTimeout(200);

  const reverseDrag = await page.evaluate(() => {
    const handleRect = document.querySelector('[data-seat-index="2"] .mobile-drag-handle')?.getBoundingClientRect();
    const targetRect = document.querySelector('[data-seat-index="0"]')?.getBoundingClientRect();
    const rows = [...document.querySelectorAll<HTMLElement>("[data-seat-index]")].slice(0, 3);
    if (handleRect === undefined || targetRect === undefined || rows.length !== 3)
      throw new Error("Reverse mobile drag targets must be visible");
    return {
      start: { x: handleRect.x + handleRect.width / 2, y: handleRect.y + handleRect.height / 2 },
      end: { x: targetRect.x + targetRect.width / 2, y: targetRect.y + targetRect.height / 2 },
      initialTops: rows.map((row) => row.getBoundingClientRect().top),
    };
  });
  await page.mouse.move(reverseDrag.start.x, reverseDrag.start.y);
  await page.mouse.down();
  await expect(page.locator(".seat-trash-zone")).toBeHidden();
  await page.mouse.move(reverseDrag.end.x, reverseDrag.end.y, { steps: 12 });

  await expect(mobileList.locator('[data-seat-index="2"]')).toHaveClass(/dragging/);
  await expect(mobileList.locator('[data-seat-index="0"]')).toHaveClass(/shift-down/);
  await expect(mobileList.locator('[data-seat-index="1"]')).toHaveClass(/shift-down/);
  await expect(mobileList.locator('[data-seat-index="0"]')).toHaveAttribute("data-drop-target", "true");
  await expect
    .poll(() =>
      page.evaluate((tops) => {
        const rows = [...document.querySelectorAll<HTMLElement>("[data-seat-index]")].slice(0, 3);
        if (rows.length !== 3) return false;
        const previewTops = rows.map((row) => row.getBoundingClientRect().top);
        return (
          Math.abs((previewTops[0] ?? 0) - (tops[1] ?? 0)) < 2 &&
          Math.abs((previewTops[1] ?? 0) - (tops[2] ?? 0)) < 2 &&
          Math.abs((previewTops[2] ?? 0) - (tops[0] ?? 0)) < 2
        );
      }, reverseDrag.initialTops),
    )
    .toBe(true);
  await page.mouse.up();

  await expect(page.getByRole("button", { name: /Player 1: Player 1\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Player 2: Player 2\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Player 3: Player 3\./ })).toBeVisible();
});

test("renames a seat inline after double-clicking it", async ({ page }) => {
  await page.goto("/");

  await page.getByRole("button", { name: /Seat 1: Player 1\./ }).dblclick();

  const nameInput = page.locator(".seating-chart").getByLabel("Rename Player 1");
  await expect(nameInput).toHaveValue("Player 1");
  await nameInput.fill("Alice");
  await nameInput.press("Enter");

  await expect(page.getByRole("button", { name: /Seat 1: Alice\./ })).toBeVisible();
  await expect(page.locator(".selected-player-panel")).toHaveCount(0);
});

test("player count input does not retain a leading zero", async ({ page }) => {
  await page.goto("/");

  const countInput = page.getByRole("spinbutton", { name: "Players" });
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

  const seatBox = await firstSeat.boundingBox();
  if (seatBox === null) throw new Error("First seat must be visible");
  const start = { x: seatBox.x + seatBox.width / 2, y: seatBox.y + seatBox.height / 2 };
  await page.mouse.move(start.x, start.y);
  await page.mouse.down();
  await page.mouse.move(start.x + 12, start.y + 12, { steps: 3 });
  await expect(trashZone).toBeVisible();

  const trashBox = await trashZone.boundingBox();
  if (trashBox === null) throw new Error("Trash zone must be visible");
  await page.mouse.move(trashBox.x + trashBox.width / 2, trashBox.y + trashBox.height / 2, { steps: 12 });
  await expect(trashZone).toHaveClass(/drop-target/);
  await page.mouse.up();

  await expect(page.getByRole("button", { name: /Seat 1: Player 2\./ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Seat 1: Player 1\./ })).toHaveCount(0);
  await expect(trashZone).toHaveCount(0);
});

test("adds and refines deaths from the timeline panel", async ({ page }) => {
  await page.goto("/");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toBeVisible();
  await expect(timeline).toContainText("Add an execution, night death, or other public event.");

  await timeline.getByRole("button", { name: "+ Add event" }).click();

  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Player 1");
  await expect(page.getByRole("button", { name: /Seat 1: Player 1, executed/ })).toBeVisible();

  const details = page.locator(".timeline-event-details");
  await details.getByLabel("Cause").selectOption("slayerShot");
  await expect(timeline).toContainText("D1 Slayer Shot");
  await expect(page.getByRole("button", { name: /Seat 1: Player 1, died to a Slayer shot/ })).toBeVisible();

  await timeline.getByRole("button", { name: "+ Add event" }).click();
  await details.getByLabel("Cause").selectOption("nightDeath");
  await details.getByLabel("Player 2").check();
  await details.getByLabel("Player 3").check();
  await details.getByLabel("Player 1").uncheck();

  await expect(timeline).toContainText("N2 Night Deaths");
  await expect(timeline).toContainText("Player 2 or Player 3");
  await expect(page.getByRole("button", { name: /Seat 2: Player 2, killed at night/ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Seat 3: Player 3, killed at night/ })).toBeVisible();
});

test("uses a quick event sheet instead of mobile timeline drop zones", async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 900 });
  await page.goto("/");

  await expect(page.locator(".timeline-drop-zone")).toHaveCount(0);
  await page.getByRole("button", { name: "Add event for Player 2" }).click();

  const dialog = page.getByRole("dialog", { name: "Add event for Player 2" });
  await expect(dialog).toBeVisible();
  await dialog.getByRole("button", { name: "Killed at night" }).click();
  await dialog.getByLabel("Timing").selectOption("night_2");
  await dialog.getByRole("button", { name: "Add event" }).click();

  await expect(page.getByLabel("Puzzle timeline")).toContainText("N2 Night Death");
  await expect(page.getByRole("button", { name: "Edit event for Player 2" })).toHaveText("N2");
  await expect
    .poll(() => page.evaluate(() => document.documentElement.scrollWidth <= document.documentElement.clientWidth))
    .toBe(true);
});
