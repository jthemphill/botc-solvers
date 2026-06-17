import { expect, test } from "@playwright/test";

test("loads puzzle 34 with structured role clues", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-34-the-vortox-conjecture");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 34 - The Vortox Conjecture");
  await expect(page.getByLabel("Puzzle setup summary")).toHaveCount(0);
  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Nomination Death");
  await expect(timeline).toContainText("Steph");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Aoife");
  await expect(timeline).toContainText("N2 Night Death");
  await expect(timeline).toContainText("Fraser");
  const stephSeat = page.getByRole("button", { name: /Seat 7: Steph, died while nominating/ });
  await expect(stephSeat.locator(".seat-death-badge.nomination-death")).toHaveText("!");
  await expect(stephSeat).toHaveCSS("border-top-color", "rgb(181, 95, 32)");
  const aoifeSeat = page.getByRole("button", { name: /Seat 4: Aoife, executed/ });
  await expect(aoifeSeat.locator(".seat-death-badge.execution")).toHaveText("X");
  await expect(aoifeSeat).toHaveCSS("border-top-color", "rgb(165, 43, 43)");
  const fraserSeat = page.getByRole("button", { name: /Seat 6: Fraser, killed at night/ });
  await expect(fraserSeat.locator(".seat-death-badge.night-kill")).toHaveText("N");
  await expect(fraserSeat).toHaveCSS("border-top-color", "rgb(48, 95, 143)");
  await expect(page.getByRole("button", { name: /Demon 3 steps from Minion/ })).toBeVisible();
  await expect(page.getByRole("button", { name: /Steph and Aoife are same/ })).toBeVisible();
  await expect(
    page.getByRole("button", { name: /1 malfunction \(Night 1\); 0 malfunctions \(Night 2\)/ }),
  ).toBeVisible();

  await page.getByRole("button", { name: /Claims/ }).click();

  await expect(page.getByText("Demon-minion distance").first()).toBeVisible();
  await expect(page.getByText("Malfunctions").first()).toBeVisible();
  await expect(page.getByText("Aoife.role == `No Dashii`").first()).toBeVisible();
  await expect(page.getByText("false info under Vortox")).toHaveCount(0);

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

test("clears stale solve results when loading another puzzle", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-09-the-new-acrobat");
  await page.getByRole("navigation", { name: "Workbench sections" }).getByRole("button", { name: "Solve" }).click();
  const solvePanel = page.locator(".solve-panel");
  await solvePanel.getByRole("button", { name: "Solve" }).click();

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("4");
  await expect(solvePanel.getByText("Solution 1")).toBeVisible();

  await page.getByLabel("Load example puzzle").selectOption("puzzle-10-dont-overcook-it");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 10 - Dont Overcook It");
  await expect(solvePanel.getByText("Press Solve to compute satisfying worlds.")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:")).toHaveCount(0);
  await expect(solvePanel.getByText("Solution 1")).toHaveCount(0);
});

test("puzzle 9 formats claim summaries without leaking hidden death causes", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-09-the-new-acrobat");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("N3 Night Deaths");
  await expect(timeline).not.toContainText("Ability Death");

  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Neither Fraser nor Oscar is the Demon.");
  await expect(claims).not.toContainText("Fraser or Oscar not Demon");
  await expect(claims).toContainText("D1 gossip: Fraser.type == Demon; D2 gossip: Anna.type == Demon");
  await expect(claims).not.toContainText("I am the Gossip");

  await page
    .getByRole("navigation", { name: "Workbench sections" })
    .getByRole("button", { name: /Claims/ })
    .click();

  await expect(page.getByText("Josh — ⚔️ Knight")).toBeVisible();
});

test("puzzle 2 formats Balloonist and Juggler claim summaries with player details", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-02-come-fly-with-me");

  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText(
    "Day 1 guesses: Steph=Knight; Sarah=Leviathan; Anna=Goblin; Sula=Goblin; You=Seamstress; 2 correct.",
  );
  await expect(claims).toContainText("Different types: Tim/Matthew; Matthew/Steph.");
  await expect(claims).not.toContainText("5 guesses, 2 correct");
  await expect(claims).not.toContainText("2 different-type pairs");
});

test("puzzle 1 formats Savant claim summaries as Alloy XOR expressions", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-01-sober-savant");

  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText(
    "(some p: players | p.role == Investigator) != (some p: You.neighbors | p.alignment == Evil)",
  );
  await expect(claims).not.toContainText("2 Savant statements");
});

test("puzzle 20 keeps full claim summaries visible on mobile", async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 900 });
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-20-the-three-wise-men");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 20 - The Three Wise Men");
  await expect
    .poll(() =>
      page.locator("input.title-input").evaluate((input: unknown) => {
        const titleInput = input as { clientWidth: number; scrollWidth: number };
        return titleInput.scrollWidth <= titleInput.clientWidth + 1;
      }),
    )
    .toBe(true);

  const balthazarSeat = page.getByRole("button", { name: /Seat 3: Balthazar/ });
  await expect(balthazarSeat.locator(".seat-player-name")).toHaveCSS("white-space", "nowrap");

  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toBeVisible();
  await expect(claims).toContainText("Balthazar nominated me on day 1 and nothing happened.");
  await expect(claims).toContainText("I checked: Balthazar -> evil, Mary -> evil.");
  await expect(claims).toContainText("I checked: Joseph -> evil, Caspar -> evil.");
  await expect(claims).toContainText("I checked: Mary -> evil, Joseph -> evil.");
});
