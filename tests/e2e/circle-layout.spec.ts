import { expect, test } from "@playwright/test";

test("small, long-report, and dense puzzles keep circular reports separate at full width", async ({ page }) => {
  await page.setViewportSize({ width: 1440, height: 1100 });
  await page.emulateMedia({ reducedMotion: "reduce" });
  await page.goto("/");
  const examples = [
    "puzzle-01-sober-savant",
    "puzzle-03a-not-throwing-away-my-shot",
    "puzzle-02-come-fly-with-me",
    "puzzle-76-three-for-three",
  ];
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
