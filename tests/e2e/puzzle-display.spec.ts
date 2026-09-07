import { expect, test } from "@playwright/test";
import { selectPlayerClaims } from "./editor-helpers";

test("renders claim details and distinct timeline death markers", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-34-the-vortox-conjecture");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 34 - The Vortox Conjecture");
  await expect(page.getByLabel("Puzzle setup summary")).toHaveCount(0);
  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Witch Curse");
  await expect(timeline).toContainText("Steph");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Aoife");
  await expect(timeline).toContainText("N2 Night Death");
  await expect(timeline).toContainText("Fraser");
  const stephSeat = page.getByRole("button", { name: /Seat 7: Steph, died to a Witch curse/ });
  await expect(stephSeat.locator(".seat-death-badge.witch-curse")).toHaveText("🪄");
  await expect(stephSeat).toHaveCSS("border-top-color", "rgb(122, 75, 159)");
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

  const claimsPanel = page.locator(".claims-panel");
  await selectPlayerClaims(page, "Sula");
  await expect(claimsPanel.getByText("Demon-minion distance").first()).toBeVisible();
  await selectPlayerClaims(page, "You");
  await expect(claimsPanel.getByText("Malfunctions").first()).toBeVisible();
  await selectPlayerClaims(page, "Steph");
  await expect(claimsPanel.getByText("Aoife.initial_role == `No Dashii`").first()).toBeVisible();
  await expect(page.getByText("false info under Vortox")).toHaveCount(0);

  await expect(page.getByText("Satisfying worlds:")).toBeVisible();
  await expect(page.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(page.locator(".solve-panel").getByText("100%")).toHaveCount(0);
  const sula = page.getByLabel("Sula: Vortox, claimed Clockmaker");
  await expect(sula).toBeVisible();
  await expect(sula).toContainText("Vortox");
  await expect(sula).not.toContainText("Clockmaker");
  await expect(sula).toHaveCSS("border-top-color", "rgb(165, 43, 43)");
});

test("renders Slayer shot death markers", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-19-he-could-be-you-he-could-be-me");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D2 Slayer Shot");
  await expect(timeline).toContainText("Oscar");
  const oscarSeat = page.getByRole("button", { name: /Seat 7: Oscar, died to a Slayer shot/ });
  await expect(oscarSeat.locator(".seat-death-badge.slayer-shot")).toHaveText("🏹");
  await expect(oscarSeat).toHaveCSS("border-top-color", "rgb(47, 125, 98)");
});

test("refreshes automatic solve results when loading another puzzle", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-09-the-new-acrobat");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByText("Solution 1")).toBeVisible();

  await page.getByLabel("Load example puzzle").selectOption("puzzle-10-dont-overcook-it");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 10 - Dont Overcook It");
  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Dan: Imp")).toBeVisible();
});

test("shows structured summaries without inventing hidden death causes", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-09-the-new-acrobat");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("N3 Night Deaths");
  await expect(timeline).not.toContainText("Ability Death");

  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Neither Fraser nor Oscar is the Demon.");
  await expect(claims).not.toContainText("Fraser or Oscar not Demon");
  await expect(claims).toContainText("N2: Sula=Goblin; N3: You=Drunk");
  await expect(claims).not.toContainText("I am the Gambler");
  await expect(claims).toContainText("N2: chose Fraser, survived; N3: chose Josh, died");
  await expect(claims).not.toContainText("I am the Acrobat");
  await expect(claims).toContainText("D1 gossip: Fraser.initial_type == Demon; D2 gossip: Anna.initial_type == Demon");
  await expect(claims).not.toContainText("I am the Gossip");

  await selectPlayerClaims(page, "Josh");
  await expect(page.getByText("Josh — ⚔️ Knight")).toBeVisible();
});

test("shows player and role details in pair and guess summaries", async ({ page }) => {
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

test("renders repeated, timed, and role-choice summaries", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-12a-thunderstruck");
  await expect(page.getByLabel("Player claim summaries")).toContainText("Chose Vortox on N1; drunk N1.");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-16-who-watches-the-watchmen");
  await expect(page.getByLabel("Player claim summaries")).toContainText("Tim did not learn Nightwatchman.");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-27-is-this-a-legion-game");
  await expect(page.getByLabel("Player claim summaries")).toContainText("N1: 1 living evil; N2: 2 living evil");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-28-a-study-in-scarlet");
  const studyClaims = page.getByLabel("Player claim summaries");
  await expect(studyClaims).toContainText("1 dead evil");
  await expect(studyClaims).toContainText("N1: Adam + Sarah, 1 woke");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-31-no-your-other-left");
  await expect(
    page.getByRole("button", {
      name: /N1: 0 evil neighbors; N2: 1 evil neighbor; N3: 1 evil neighbor/,
    }),
  ).toBeVisible();
  await expect(page.getByRole("button", { name: /N1: Aoife \+ Tim -> no; N2: Aoife \+ Olivia -> no/ })).toBeVisible();
  await selectPlayerClaims(page, "Olivia");
  await expect(page.getByText("Olivia — 🔮 Fortune Teller")).toHaveCount(2);
  await expect(page.getByText("+ Add check")).toHaveCount(0);

  await page.getByLabel("Load example puzzle").selectOption("puzzle-11-false-is-the-new-black");
  await expect(page.getByLabel("Player claim summaries")).toContainText("Chose Snake Charmer.");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-24-the-ultimate-blunder");
  await expect(page.getByLabel("Player claim summaries")).toContainText("Chose Adam.");
});

test("renders Savant expressions in claim summaries", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-01-sober-savant");

  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText(
    "(some p: players | p.initial_role == Investigator) != (some p: You.neighbors | p.alignment == Evil)",
  );
  await expect(claims).not.toContainText("2 Savant statements");
});

test("keeps long titles and claim summaries visible on mobile", async ({ page }) => {
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

  const roster = page.getByLabel("Players in seating order");
  const balthazarRow = page.getByRole("button", { name: /Player 3: Balthazar/ });
  await expect(balthazarRow.locator("strong")).toHaveCSS("white-space", "nowrap");

  await expect(roster).toBeVisible();
  await expect(roster).toContainText("Balthazar nominated me on day 1 and nothing happened.");
  await expect(roster).toContainText("I checked: Balthazar -> evil, Mary -> evil.");
  await expect(roster).toContainText("I checked: Joseph -> evil, Caspar -> evil.");
  await expect(roster).toContainText("I checked: Mary -> evil, Joseph -> evil.");

  await expect
    .poll(() =>
      roster
        .locator(".mobile-player-copy small")
        .evaluateAll((summaries) => summaries.every((summary) => summary.scrollHeight <= summary.clientHeight + 1)),
    )
    .toBe(true);
});

test("shows incomplete coverage and a trace witness", async ({ page }) => {
  await page.goto("/");
  await page.getByLabel("Load example puzzle").selectOption("puzzle-11-false-is-the-new-black");
  const solvePanel = page.locator(".solve-panel");
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByText("Rule coverage is incomplete.", { exact: false })).toBeVisible();
  await expect(solvePanel.getByText("All initial character assignments enumerated.")).toBeVisible();
  await solvePanel.getByText("Character changes and hidden choices", { exact: true }).click();
  await expect(solvePanel.getByText("Sarah, Cerenovus:player", { exact: false }).first()).toBeVisible();
});
