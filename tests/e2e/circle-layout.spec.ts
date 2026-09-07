import { expect, test } from "@playwright/test";

test("all catalog puzzles keep circular reports separate at full width", async ({ page }) => {
  test.setTimeout(60_000);
  await page.setViewportSize({ width: 1440, height: 1100 });
  await page.emulateMedia({ reducedMotion: "reduce" });
  await page.goto("/");
  const examples = await page
    .getByLabel("Load example puzzle")
    .locator("option")
    .evaluateAll((options) => options.map((option) => (option as HTMLOptionElement).value).filter(Boolean));
  expect(examples).toHaveLength(91);
  const collisions: string[] = [];
  for (const id of examples) {
    await page.getByLabel("Load example puzzle").selectOption(id);
    const overlaps = await page.getByLabel("Clockwise seating chart").evaluate((chart) => {
      const boxes = [...chart.querySelectorAll(".claim-callout, .seat-button, .seat-player-name")].map((element) => ({
        rect: element.getBoundingClientRect(),
        text: element.textContent?.trim(),
      }));
      const timeline = chart.parentElement?.querySelector(".timeline-strip");
      if (timeline) boxes.push({ rect: timeline.getBoundingClientRect(), text: "Timeline" });
      return boxes.flatMap(({ rect, text }, index) =>
        boxes
          .slice(index + 1)
          .filter(
            ({ rect: other }) =>
              Math.min(rect.right, other.right) > Math.max(rect.left, other.left) + 1 &&
              Math.min(rect.bottom, other.bottom) > Math.max(rect.top, other.top) + 1,
          )
          .map((other) => `${text} / ${other.text}`),
      );
    });
    if (overlaps.length) collisions.push(`${id}: ${overlaps.join("; ")}`);
  }
  expect(collisions).toEqual([]);
});
