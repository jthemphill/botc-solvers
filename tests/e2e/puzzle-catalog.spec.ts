import { expect, test } from "@playwright/test";

test("loads puzzle 34 with structured role clues", async ({ page }) => {
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
  await expect(claimsPanel.getByText("Demon-minion distance").first()).toBeVisible();
  await page.getByLabel("Claiming player").selectOption("You");
  await expect(claimsPanel.getByText("Malfunctions").first()).toBeVisible();
  await page.getByLabel("Claiming player").selectOption("Steph");
  await expect(claimsPanel.getByText("Aoife.role == `No Dashii`").first()).toBeVisible();
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

test("solves puzzle 41 with the Lunatic and starpassed Imp solution", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-41-no-john-you-are-the-demons");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 41 - No, John, You Are the Demons");
  await expect(page.getByLabel("Puzzle setup summary")).toHaveCount(0);
  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Witch Curse");
  await expect(timeline).toContainText("Gina");
  await expect(timeline).toContainText("N2 Night Death");
  await expect(timeline).toContainText("Chris");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("Josef");
  await expect(page.getByLabel("Player claim summaries")).toContainText("I learned that Riley is not a Townsfolk.");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("You: Lunatic, claimed Imp")).toBeVisible();
  await expect(solvePanel.getByLabel("Chris: Imp, claimed Artist")).toBeVisible();
  await expect(solvePanel.getByLabel("Katharine: Witch, claimed Poppy Grower")).toBeVisible();
});

test("solves puzzle 42 with the Widow-poisoned Philosopher world", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-42-life-the-universe-and-everything");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 42 - Life, the Universe, and Everything");
  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("You");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("Jasmine");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("N1: Fraser + Matthew -> yes");
  await expect(claims).toContainText("Day 1 guesses: You=Philosopher; Matthew=Imp; 1 correct.");
  await expect(claims).toContainText("I learned that Oscar, Hannah, or Jasmine was poisoned on day 1.");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Jasmine: Imp, claimed Recluse")).toBeVisible();
  await expect(solvePanel.getByLabel("Matthew: Widow, claimed Fortune Teller")).toBeVisible();
  await expect(solvePanel.getByLabel("Hannah: Undertaker")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Philosopher")).toBeVisible();
});

test("solves puzzle 43 with a unique Demon and Minion", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-43-two-many-cooks");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 43 - Two Many Cooks");
  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Aoife");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("You");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Anna or Steph is the Poisoner.");
  await expect(claims).toContainText("N1: You + Fraser -> no");
  await expect(claims).toContainText("Fraser is the Chef.");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Dan: Imp, claimed Saint")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Poisoner, claimed Chef")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Ravenkeeper")).toBeVisible();
});

test("solves puzzle 44 with the homebrew Prodigy token claims", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-44-trouble-homebrewing");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 44 - Trouble Homebrewing");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("I checked: N1: Dan -> Tim, N2: Sarah -> Dan, N3: Sarah -> Steph.");
  await expect(claims).toContainText("I checked: N1: Steph -> Olivia, N2: Fraser -> Matt, N3: Steph -> Fraser.");
  await expect(claims).toContainText("N1: Tim + Dan -> no");
  await expect(claims).toContainText("N2: Tim + Fraser -> no");
  await expect(claims).toContainText("N3: You + Steph -> yes");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Olivia: Leviathan, claimed Chef")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Scarlet Woman, claimed Shugenja")).toBeVisible();
  await expect(solvePanel.getByLabel("Matt: Solar Prodigy")).toBeVisible();
  await expect(solvePanel.getByLabel("Dan: Lunar Prodigy")).toBeVisible();
  await expect(solvePanel.getByLabel("Tim: Drunk, claimed Noble")).toBeVisible();
});

test("solves puzzle 45a with the Hermit hidden-role rules", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-45a-dont-try-this-at-home");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 45a - Don't Try This at Home");
  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Eliz");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("Julia");
  await expect(page.getByLabel("Player claim summaries")).toContainText("I shot Ben on day 3 and nothing happened.");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Shan: Imp, claimed Washerwoman")).toBeVisible();
  await expect(solvePanel.getByLabel("Eliz: Scarlet Woman, claimed Investigator")).toBeVisible();
  await expect(solvePanel.getByLabel("Louisa: Drunk, claimed Fortune Teller")).toBeVisible();
});

test("solves puzzle 45b with the Hermit and Spy solution", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-45b-dont-try-this-at-home");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 45b - Don't Try This at Home");
  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Dan");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("You");
  await expect(page.getByLabel("Player claim summaries")).toContainText("I shot Adam on day 2 and nothing happened.");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Sula: Imp, claimed Washerwoman")).toBeVisible();
  await expect(solvePanel.getByLabel("Adam: Spy, claimed Investigator")).toBeVisible();
  await expect(solvePanel.getByLabel("Tim: Hermit, claimed Undertaker")).toBeVisible();
});

test("solves puzzle 46 with the Princess and Gossip timing rules", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-46-the-princess-diaries");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 46 - The Princess Diaries");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("N2: chose Jasmine; N3: chose Aoife");
  await expect(claims).toContainText("Nominated You on day 1");
  await expect(claims).toContainText("Demon 3 steps from Minion");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Josh: Imp, claimed Gambler")).toBeVisible();
  await expect(solvePanel.getByLabel("Adam: Poisoner, claimed Chambermaid")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Investigator")).toBeVisible();
});

test("solves puzzle 47 with the Baron starpass solution", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-47-we-have-evil-twin-at-home");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 47 - We Have Evil Twin at Home");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Josh or Tom is the Baron.");
  await expect(claims).toContainText("Olivia is the Investigator.");
  await expect(claims).toContainText("Tom was Drunk");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("N2 Night Death");
  await expect(timeline).toContainText("Fraser");
  await expect(timeline).toContainText("N4 Night Death");
  await expect(timeline).toContainText("Olivia");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Fraser: Imp, claimed Ravenkeeper")).toBeVisible();
  await expect(solvePanel.getByLabel("Josh: Baron, claimed Saint")).toBeVisible();
  await expect(solvePanel.getByLabel("Steph: Drunk, claimed Undertaker")).toBeVisible();
});

test("solves puzzle 48 with the Xaan and Puzzlemaster-drunk solution", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-48-solving-for-x");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 48 - Solving for X");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("D3: guessed Tom, learned Matthew is Demon");
  await expect(claims).toContainText("N1: Olivia + Jasmine, 2 woke");
  await expect(claims).toContainText("1 malfunction (Night 1)");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D3 Nomination Death");
  await expect(timeline).toContainText("Tom");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Jasmine: Leviathan, claimed Village Idiot")).toBeVisible();
  await expect(solvePanel.getByLabel("Tom: Xaan, claimed Artist")).toBeVisible();
  const matthew = solvePanel.getByLabel("Matthew: Chambermaid");
  await expect(matthew).toBeVisible();
  await expect(matthew).toContainText("Drunk");
});

test("solves puzzle 49 with the Riot nomination solution", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-49-bastille-day");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 49 - Bastille Day");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("N1: 0 evil neighbors");
  await expect(claims).toContainText("N3: 1 evil neighbor");
  await expect(claims).toContainText("You or Matthew is the Drunk.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D3 Nomination Death");
  await expect(timeline).toContainText("Matthew");
  await expect(timeline).toContainText("Tom");
  await expect(timeline).toContainText("You");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Matthew: Riot, claimed Chef")).toBeVisible();
  await expect(solvePanel.getByLabel("Sula: Baron, claimed Librarian")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Drunk, claimed Undertaker")).toBeVisible();
});

test("solves puzzle 51 with the Nightwatchman bluff", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-51-weird-science");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 51 - Weird Science");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Tim learned Nightwatchman.");
  await expect(claims).toContainText("I learned that Hannah is not the Boffin.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Slayer Shot");
  await expect(timeline).toContainText("D1 Nomination Death");
  await expect(timeline).toContainText("N2 Night Death");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Josh: Kazali, claimed Nightwatchman")).toBeVisible();
  await expect(solvePanel.getByLabel("Tim: Spy, claimed Artist")).toBeVisible();
});

test("solves puzzle 52 with the Drunk Undertaker world", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-52-two-votes-is-enough");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 52 - Two Votes Is Enough");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("You or Steph is the Drunk.");
  await expect(claims).toContainText("Anna or Steph is the Spy.");
  await expect(claims).toContainText("Josh was Imp");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("N4 Night Death");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Sarah: Imp, claimed Empath")).toBeVisible();
  await expect(solvePanel.getByLabel("Josh: Baron, claimed Virgin")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Drunk, claimed Undertaker")).toBeVisible();
});

test("solves puzzle 53 with the Fang Gu jump world", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-53-lets-do-the-time-warp-again");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 53 - Let's Do the Time Warp Again");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Demon 4 steps from Minion");
  await expect(claims).toContainText("Olivia is Mutant or Witch");
  await expect(claims).toContainText(
    "Day 1 guesses: Aoife=Dreamer; Tim=Mutant; Fraser=Mutant; Sarah=Vortox; 2 correct.",
  );

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("N2 Night Death");
  await expect(timeline).toContainText("D2 Witch Curse");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Jasmine: Fang Gu, claimed Mathematician")).toBeVisible();
  await expect(solvePanel.getByLabel("Olivia: Witch, claimed Juggler")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Mutant, claimed Oracle")).toBeVisible();
});

test("solves puzzle 54 with the Baron outsider world", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-54-silence-in-the-library");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 54 - Silence in the Library");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Oscar + Anna -> no");
  await expect(claims).toContainText("0 evil neighbors");
  await expect(claims).toContainText("0 Outsiders");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("N3 Night Death");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Matthew: Imp, claimed Ravenkeeper")).toBeVisible();
  await expect(solvePanel.getByLabel("Oscar: Baron, claimed Investigator")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Drunk, claimed Librarian")).toBeVisible();
});

test("solves puzzle 55 with the Flowergirl Demon worlds", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-55-the-life-of-a-flowergirl");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 55 - The Life of a Flowergirl");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("I learned that Aoife is not the Artist.");
  await expect(claims).toContainText("N2: You, Fraser, Steph, Aoife, or Jasmine voted -> yes");
  await expect(claims).toContainText("Sarah and Jasmine are same");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D2 Witch Curse");
  await expect(timeline).toContainText("N3 Night Death");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("2");
  await expect(solvePanel.getByLabel("Anna: Vortox, claimed Juggler")).toBeVisible();
  await expect(solvePanel.getByLabel("Steph: No Dashii, claimed Klutz")).toBeVisible();
  await expect(solvePanel.getByLabel("Jasmine: Witch, claimed Oracle")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Flowergirl")).toHaveCount(2);
});

test("solves puzzle 56 with the Imp and Poisoner conclusion", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-56-meanwhile-at-the-legion-of-doom");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 56 - Meanwhile, at the Legion of Doom");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Neither Aoife nor Matthew is the Demon.");
  await expect(claims).toContainText("Aoife + Tom, 2 woke");
  await expect(claims).toContainText("I shot Fraser on day 3 and nothing happened.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("N3 Night Death");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Fraser: Imp, claimed Investigator")).toBeVisible();
  await expect(solvePanel.getByLabel("Aoife: Poisoner, claimed Oracle")).toBeVisible();
  await expect(solvePanel.getByLabel("Matthew: Empath")).toBeVisible();
});

test("solves puzzle 57 with the Vigormortis and Tea Lady conclusion", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-57-neither-victims-nor-executioners");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 57 - Neither Victims nor Executioners");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("You and Adam are same");
  await expect(claims).toContainText("I learned that Matt is not a Demon.");
  await expect(claims).toContainText("Steph, Sarah, or Aoife: 1 evil");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Survived Execution");
  await expect(timeline).toContainText("D3 Survived Execution");
  await expect(timeline).toContainText("N4 Night Death");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Fraser: Vigormortis, claimed Artist")).toBeVisible();
  await expect(solvePanel.getByLabel("Aoife: Poisoner, claimed Ravenkeeper")).toBeVisible();
  await expect(solvePanel.getByLabel("Matt: Tea Lady")).toBeVisible();
});

test("solves puzzle 58 with the Riot, Xaan, and Politician conclusion", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-58-minus-one-thats-three");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 58 - Minus One, That's Three");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Matthew did not learn Nightwatchman.");
  await expect(claims).toContainText(
    "Day 1 guesses: Fraser=Riot; Jasmine=Politician; Adam=Noble; Steph=Nightwatchman; Tom=Xaan; 2 correct.",
  );
  await expect(claims).toContainText("D3: guessed Oscar, learned You is Demon");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D3 Nomination Death");
  await expect(timeline).toContainText("Jasmine");
  await expect(timeline).toContainText("You");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Adam: Riot, claimed Noble")).toBeVisible();
  await expect(solvePanel.getByLabel("Oscar: Xaan, claimed Nightwatchman")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Politician")).toBeVisible();
  const steph = solvePanel.getByLabel("Steph: Nightwatchman");
  await expect(steph).toBeVisible();
  await expect(steph).toContainText("Drunk");
});

test("solves puzzle 59 with the Spy registering to Virgin and Undertaker", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-59-fifty-fifty");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 59 - Fifty-Fifty");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Jasmine nominated me on day 1 and was executed.");
  await expect(claims).toContainText("Jasmine or Adam is the Spy.");
  await expect(claims).toContainText("Jasmine was Empath");
  await expect(claims).toContainText("Matthew is the Chef.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Nomination Death");
  await expect(timeline).toContainText("N4 Night Death");
  await expect(timeline).toContainText("Josh");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Oscar: Imp, claimed Butler")).toBeVisible();
  await expect(solvePanel.getByLabel("Jasmine: Spy, claimed Empath")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Virgin")).toBeVisible();
  await expect(solvePanel.getByLabel("Adam: Undertaker")).toBeVisible();
});

test("solves puzzle 60 with the No Dashii and Drunk conclusion", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-60-whats-a-mind-goblin");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 60 - What's a Mind Goblin?");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Tim or Fraser is the Artist.");
  await expect(claims).toContainText("N2: 2 evil neighbors");
  await expect(claims).toContainText("Olivia or Fraser is Demon");
  await expect(claims).toContainText("I learned that Olivia is not a Townsfolk.");
  await expect(claims).toContainText("You or Aoife is the Drunk.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("N2 Night Death");
  await expect(timeline).toContainText("Aoife");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("You");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Jasmine: No Dashii, claimed Washerwoman")).toBeVisible();
  await expect(solvePanel.getByLabel("Aoife: Drunk, claimed Sage")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Goblin")).toBeVisible();
  await expect(solvePanel.getByLabel("Olivia: Poppy Grower")).toBeVisible();
});

test("solves puzzle 61 with the Sweetheart-drunk Savant conclusion", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-61-thus-with-a-kiss-i-die");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 61 - Thus With a Kiss I Die");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText(
    "Day 1 guesses: You=Savant; Matthew=Vigormortis; Fraser=Mathematician; Steph=Witch; Tim=Fang Gu; 0 correct.",
  );
  await expect(claims).toContainText("role_distance(3, `No Dashii`, Witch)");
  await expect(claims).toContainText("N1: Fraser is not Demon");
  await expect(claims).toContainText("Fraser and Anna are same");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Witch Curse");
  await expect(timeline).toContainText("Oscar");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("Tim");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Anna: No Dashii, claimed Oracle")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Witch, claimed Mathematician")).toBeVisible();
  await expect(solvePanel.getByLabel("Steph: Sweetheart")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Savant")).toBeVisible();
});

test("solves puzzle 62 with the Storm Catcher Drunk conclusion", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-62-have-you-ever-seen-the-rain");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 62 - Have You Ever Seen The Rain?");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Fraser or Jasmine is the Spy.");
  await expect(claims).toContainText("N2: 0 evil neighbors");
  await expect(claims).toContainText("N3: Sula + Fraser -> yes");
  await expect(claims).toContainText("I shot Sula on day 2 and nothing happened.");
  await expect(claims).toContainText("Oscar or Tim is the Drunk.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("N4 Night Death");
  await expect(timeline).toContainText("Dan");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Hannah: Imp, claimed Washerwoman")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Spy, claimed Fortune Teller")).toBeVisible();
  await expect(solvePanel.getByLabel("Sula: Drunk, claimed Librarian")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Recluse")).toBeVisible();
});

test("solves puzzle 63 with unique evil players", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-63-the-limiting-factor");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 63 - The Limiting Factor");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Steph or Josh is the Baron.");
  await expect(claims).toContainText("N4: 2 evil neighbors");
  await expect(claims).toContainText("Steph is the Undertaker.");
  await expect(claims).toContainText("Matt or Josh is the Empath.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Fraser");
  await expect(timeline).toContainText("N4 Night Death");
  await expect(timeline).toContainText("Dan");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Tom: Imp, claimed Recluse")).toBeVisible();
  await expect(solvePanel.getByLabel("Steph: Poisoner, claimed Undertaker")).toBeVisible();
  await expect(solvePanel.getByLabel("Olivia: Investigator")).toBeVisible();
  await expect(solvePanel.getByLabel("Dan: Ravenkeeper")).toBeVisible();
});

test("solves puzzle 64 with the Pope duplicate Mutants", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-64-copycatholic");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 64 - Copycatholic");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Adam or Hannah is the Librarian.");
  await expect(claims).toContainText("I shot Olivia on day 4 and nothing happened.");
  await expect(claims).toContainText("Dan or Tim is the Mutant.");
  await expect(claims).toContainText("Josh is the Saint.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Hannah");
  await expect(timeline).toContainText("N4 Night Death");
  await expect(timeline).toContainText("Josh");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Olivia: Imp, claimed Saint")).toBeVisible();
  await expect(solvePanel.getByLabel("Tim: Baron, claimed Washerwoman")).toBeVisible();
  await expect(solvePanel.getByLabel("Adam: Mutant, claimed Librarian")).toBeVisible();
  await expect(solvePanel.getByLabel("Sarah: Mutant, claimed Slayer")).toBeVisible();
});

test("solves puzzle 65 with the Fang Gu jump to the Mutant", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-65-the-slip-up");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 65 - The Slip-Up");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("N3: Tom is not Demon");
  await expect(claims).toContainText("Day 1 guesses: Tom=Seamstress; Fraser=Snake Charmer; Matt=Oracle; 1 correct.");
  await expect(claims).toContainText("Demon 4 steps from Minion");
  await expect(claims).toContainText("Chose Dan and did not lose.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D2 Witch Curse");
  await expect(timeline).toContainText("Anna");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("Tom");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Tom: Fang Gu, claimed Seamstress")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Witch, claimed Snake Charmer")).toBeVisible();
  await expect(solvePanel.getByLabel("Dan: Mutant, claimed Clockmaker")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Klutz")).toBeVisible();
});

test("solves puzzle 66 with the starpassed Imp and drunk Village Idiot", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-66-the-useful-idiot");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 66 - The Useful Idiot");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Matt or Tim is the Poisoner.");
  await expect(claims).toContainText("Day 1 guesses: Aoife=Imp; Matt=Imp; Sarah=Imp; 0 correct.");
  await expect(claims).toContainText("N3: Aoife + Sarah -> yes");
  await expect(claims).toContainText("I checked: N1 Tim -> evil, N2 Olivia -> good.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("N2 Night Death");
  await expect(timeline).toContainText("Tim");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("Olivia");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Tim: Imp, claimed Ravenkeeper")).toBeVisible();
  await expect(solvePanel.getByLabel("Matt: Poisoner, claimed Village Idiot")).toBeVisible();
  await expect(solvePanel.getByLabel("Aoife: Village Idiot")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Village Idiot")).toBeVisible();
});

test("solves puzzle 67 with Spy registrations and a Puzzlemaster drunk", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-67-minus-one-thats-three-times-two");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 67 - Minus One, That's Three (Times Two)");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("You and Hannah are same");
  await expect(claims).toContainText("Oscar did not learn Nightwatchman.");
  await expect(claims).toContainText("D2: guessed Sarah, learned Matthew is Demon");
  await expect(claims).toContainText(
    "Day 1 guesses: Sarah=Politician; Oscar=Politician; Fraser=Xaan; Tim=Puzzlemaster; 2 correct.",
  );

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D3 Nomination Death");
  await expect(timeline).toContainText("Fraser");
  await expect(timeline).toContainText("You");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Fraser: Riot, claimed Seamstress")).toBeVisible();
  await expect(solvePanel.getByLabel("Sarah: Spy, claimed Noble")).toBeVisible();
  await expect(solvePanel.getByLabel("Matthew: Nightwatchman")).toBeVisible();
  await expect(solvePanel.getByLabel("Tim: Puzzlemaster")).toBeVisible();
  await expect(solvePanel.getByLabel("Hannah: Politician")).toBeVisible();
});

test("solves puzzle 68 with the Vortox, Witch, and Mutant", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-68-the-numbers-are-all-wrong");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 68 - The Numbers Are All Wrong");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("0 dead evil");
  await expect(claims).toContainText("I learned that Tom is a Townsfolk.");
  await expect(claims).toContainText("N3: Sarah is not Demon");
  await expect(claims).toContainText("1 malfunction (Night 1); 2 malfunctions (Night 2)");
  await expect(claims).toContainText("Day 1 guesses: Sarah=Witch; Matthew=Mutant; Anna=Snake Charmer");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Witch Curse");
  await expect(timeline).toContainText("Fraser");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("You");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Sarah: Vortox, claimed Oracle")).toBeVisible();
  await expect(solvePanel.getByLabel("Anna: Witch, claimed Snake Charmer")).toBeVisible();
  await expect(solvePanel.getByLabel("Matthew: Mutant, claimed Artist")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Mathematician")).toBeVisible();
});

test("solves puzzle 69 with the No Dashii and self-cursing Witch", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-69-thats-the-sects-number");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 69 - That's the Sects Number");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("I learned that Fraser is not the Artist.");
  await expect(claims).toContainText(
    "Day 1 guesses: You=Witch; Hannah=No Dashii; Matt=Mutant; Fraser=No Dashii; 1 correct.",
  );
  await expect(claims).toContainText("2 malfunctions (Night 1); 1 malfunction (Night 2); 2 malfunctions (Night 3)");
  await expect(claims).toContainText("Adam or Tom is Demon");
  await expect(claims).toContainText("N2: Dan is not Demon");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Witch Curse");
  await expect(timeline).toContainText("Oscar");
  await expect(timeline).toContainText("D2 Witch Curse");
  await expect(timeline).toContainText("Sarah");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Fraser: No Dashii, claimed Artist")).toBeVisible();
  await expect(solvePanel.getByLabel("Sarah: Witch, claimed Juggler")).toBeVisible();
  await expect(solvePanel.getByLabel("Matt: Sweetheart")).toBeVisible();
  await expect(solvePanel.getByLabel("Dan: Klutz")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Sage")).toBeVisible();
});

test("solves puzzle 70 with the Imp and Poisoner", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-70-digging-your-own-grave");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 70 - Digging Your Own Grave");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Hannah or Sarah is the Spy.");
  await expect(claims).toContainText("Tom is the Undertaker.");
  await expect(claims).toContainText("N2: 0 evil neighbors");
  await expect(claims).toContainText("N1: Sarah + Fraser -> no");
  await expect(claims).toContainText("N2: You + Hannah -> no");
  await expect(claims).toContainText("N3: Dan + Hannah -> no");
  await expect(claims).toContainText("Tom or Fraser is the Drunk.");
  await expect(claims).toContainText("Dan was Spy");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Matthew: Imp, claimed Saint")).toBeVisible();
  await expect(solvePanel.getByLabel("Hannah: Poisoner, claimed Librarian")).toBeVisible();
  await expect(solvePanel.getByLabel("Sarah: Butler")).toBeVisible();
  await expect(solvePanel.getByLabel("Adam: Recluse")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Empath")).toBeVisible();
});

test("solves puzzle 71 with the No Dashii and Scarlet Woman catch", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-71-the-disappearing-act");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 71 - The Disappearing Act");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("N1: 0 evil neighbors");
  await expect(claims).toContainText("1 malfunction (Night 1); 0 malfunctions (Night 2); 0 malfunctions (Night 3)");
  await expect(claims).toContainText("Demon 4 steps from Minion");
  await expect(claims).toContainText("I checked: N1 Fraser -> evil, N2 Oscar -> evil, N3 Tom -> evil.");
  await expect(claims).toContainText("N1: Dan is not Demon");
  await expect(claims).toContainText("N2: Sarah is not Demon");
  await expect(claims).toContainText("N3: Matt is not Demon");
  await expect(claims).toContainText("Day 1 guesses: Oscar=Mutant; Fraser=Ravenkeeper; Dan=No Dashii; 1 correct.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Hannah");
  await expect(timeline).toContainText("N2 Night Death");
  await expect(timeline).toContainText("Fraser");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Fraser: No Dashii, claimed Ravenkeeper")).toBeVisible();
  await expect(solvePanel.getByLabel("Dan: Scarlet Woman, claimed Clockmaker")).toBeVisible();
  await expect(solvePanel.getByLabel("Matt: Village Idiot")).toBeVisible();
  await expect(solvePanel.getByLabel("Oscar: Mutant")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Snake Charmer")).toBeVisible();
});

test("solves puzzle 72 with the six-Legion world", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-72-one-digit-too-many");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 72 - One Digit Too Many");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Matt is the Drunk.");
  await expect(claims).toContainText("1 dead evil");
  await expect(claims).toContainText("I learned that someone is the Imp.");
  await expect(claims).toContainText("Hannah was Chambermaid");
  await expect(claims).toContainText("Sarah or Josh is the Spy.");
  await expect(claims).toContainText("N1: 1 evil neighbor");
  await expect(claims).toContainText("N2: 1 evil neighbor");
  await expect(claims).toContainText("N1: Matt + Josh, 2 woke");
  await expect(claims).toContainText("You or Hannah is the Drunk.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Hannah");
  await expect(timeline).toContainText("N2 Night Death");
  await expect(timeline).toContainText("Sarah");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Sarah: Legion, claimed Ravenkeeper")).toBeVisible();
  await expect(solvePanel.getByLabel("Tim: Legion, claimed Oracle")).toBeVisible();
  await expect(solvePanel.getByLabel("Josh: Legion, claimed Artist")).toBeVisible();
  await expect(solvePanel.getByLabel("Oscar: Legion, claimed Undertaker")).toBeVisible();
  await expect(solvePanel.getByLabel("Hannah: Legion, claimed Chambermaid")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Legion, claimed Librarian")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Investigator")).toBeVisible();
  await expect(solvePanel.getByLabel("Matt: Empath")).toBeVisible();
});

test("solves puzzle 73 with the poisoned Vortox opening", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-73-opening-theory");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 73 - Opening Theory");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Demon 4 steps from Minion");
  await expect(claims).toContainText("Fraser is Knight or Poisoner");
  await expect(claims).toContainText("N1: 1 evil neighbor");
  await expect(claims).toContainText("N2: 1 evil neighbor");
  await expect(claims).toContainText("N1: You + Fraser, 1 woke");
  await expect(claims).toContainText("N2: Fraser + Matthew, 1 woke");
  await expect(claims).toContainText("N1: Olivia is not Demon");
  await expect(claims).toContainText("N2: Sarah is not Demon");
  await expect(claims).toContainText("N3: Jasmine is not Demon");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Tom");
  await expect(timeline).toContainText("D2 Execution");
  await expect(timeline).toContainText("Olivia");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Sarah: Vortox, claimed Clockmaker")).toBeVisible();
  await expect(solvePanel.getByLabel("Olivia: Poisoner, claimed Chambermaid")).toBeVisible();
  await expect(solvePanel.getByLabel("Matthew: Snake Charmer")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Butler")).toBeVisible();
});

test("solves puzzle 74 with Oscar Imp and Matt Poisoner", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-74-youre-obviously-evil");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 74 - You're Obviously Evil");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Fraser was Drunk");
  await expect(claims).toContainText("Tom was Fortune Teller");
  await expect(claims).toContainText("0 adjacent evil pairs");
  await expect(claims).toContainText("N1: Fraser + Aoife -> yes");
  await expect(claims).toContainText("N2: Tom + Matt -> no");
  await expect(claims).toContainText("Aoife or Dan is the Spy.");
  await expect(claims).toContainText("N1: 0 evil neighbors");
  await expect(claims).toContainText("Oscar is the Spy.");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Fraser");
  await expect(timeline).toContainText("N4 Night Death");
  await expect(timeline).toContainText("Dan");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Oscar: Imp, claimed Chef")).toBeVisible();
  await expect(solvePanel.getByLabel("Matt: Poisoner, claimed Recluse")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Investigator")).toBeVisible();
  await expect(solvePanel.getByLabel("Sarah: Undertaker")).toBeVisible();
});

test("solves puzzle 75 with the Fang Gu jump world", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-75-cut-from-the-same-cloth");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 75 - Cut From the Same Cloth");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Adam is Artist or Vigormortis");
  await expect(claims).toContainText("Demon 2 steps from Minion");
  await expect(claims).toContainText("I learned that Fraser is a Demon.");
  await expect(claims).toContainText("Day 1 guesses: You=No Dashii; Matt=Vigormortis; 0 correct.");
  await expect(claims).toContainText("Sarah and Adam are same");
  await expect(claims).toContainText("2 malfunctions (Night 1); 0 malfunctions (Night 2)");
  await expect(claims).toContainText("N3: Fraser is not Demon");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("D1 Execution");
  await expect(timeline).toContainText("Jasmine");
  await expect(timeline).toContainText("D2 Witch Curse");
  await expect(timeline).toContainText("Tom");
  await expect(timeline).toContainText("N3 Night Death");
  await expect(timeline).toContainText("Fraser");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Fraser: Fang Gu, claimed Mathematician")).toBeVisible();
  await expect(solvePanel.getByLabel("Hannah: Witch, claimed Snake Charmer")).toBeVisible();
  await expect(solvePanel.getByLabel("Matt: Mutant, claimed Clockmaker")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Seamstress")).toBeVisible();
});

test("solves puzzle 76 with the full good-team assignment", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-76-three-for-three");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 76 - Three for Three");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("N1: 1 evil neighbor");
  await expect(claims).toContainText("1 adjacent evil pair");
  await expect(claims).toContainText("N1: 0 evil neighbors");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("You: Imp")).toBeVisible();
  await expect(solvePanel.getByLabel("Adam: Poisoner")).toBeVisible();
  await expect(solvePanel.getByLabel("Oscar: Scarlet Woman")).toBeVisible();
  await expect(solvePanel.getByLabel("Sula: Godfather")).toBeVisible();
  await expect(solvePanel.getByLabel("Sarah: Butler")).toBeVisible();
  await expect(solvePanel.getByLabel("Tom: Empath")).toBeVisible();
  await expect(solvePanel.getByLabel("Steph: Recluse")).toBeVisible();
  await expect(solvePanel.getByLabel("Matthew: Chef")).toBeVisible();
});

test("solves puzzle 77 with Sarah Imp and Matt Poisoner", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-77-yes-but-dont");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 77 - Yes, But Don't");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("0 adjacent evil pairs");
  await expect(claims).toContainText("Matt or Josh is the Poisoner.");
  await expect(claims).toContainText("N1: 0 evil neighbors");
  await expect(claims).toContainText("Sarah is the Baron.");
  await expect(claims).toContainText("Fraser or Tom is the Drunk.");
  await expect(claims).toContainText("Adam was Drunk");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Sarah: Imp, claimed Saint")).toBeVisible();
  await expect(solvePanel.getByLabel("Matt: Poisoner, claimed Imp")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Drunk, claimed Undertaker")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Ravenkeeper")).toBeVisible();
});

test("solves puzzle 78 with the Imp starpass to the Baron", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-78-its-pronounced-eefa");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 78 - It's Pronounced Ee-fa");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Aoife or Fraser is the Baron.");
  await expect(claims).toContainText("Sarah is the Poisoner.");
  await expect(claims).toContainText("Jasmine was Scarlet Woman");
  await expect(claims).toContainText("N4: Aoife + Fraser -> yes");
  await expect(claims).toContainText("I shot Charlotte on day 4 and nothing happened.");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Dan: Imp, claimed Ravenkeeper")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Baron, claimed Slayer")).toBeVisible();
  await expect(solvePanel.getByLabel("You: Drunk, claimed Undertaker")).toBeVisible();
  await expect(solvePanel.getByLabel("Aoife: Recluse")).toBeVisible();
});

test("solves puzzle 79 with Goose Vortox and Louisa Witch", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-79-erudition-lesson");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 79 - Erudition Lesson");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Demon 1 step from Minion");
  await expect(claims).toContainText("Day 1 guesses: You=Fang Gu; Edd=Vigormortis; Marc=Mutant; 1 correct.");
  await expect(claims).toContainText("You and Chris are different");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Goose: Vortox, claimed Snake Charmer")).toBeVisible();
  await expect(solvePanel.getByLabel("Louisa: Witch, claimed Artist")).toBeVisible();
  await expect(solvePanel.getByLabel("Edd: Sweetheart")).toBeVisible();
});

test("solves puzzle 80 with Sarah Imp and Fraser Xaan", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-80-the-x-factor");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 80 - The X Factor");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Fraser or Hannah is the Xaan.");
  await expect(claims).toContainText("N3: Charlotte + Aoife -> yes");
  await expect(claims).toContainText("Hannah was Chef");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Sarah: Imp, claimed Butler")).toBeVisible();
  await expect(solvePanel.getByLabel("Fraser: Xaan, claimed Undertaker")).toBeVisible();
  await expect(solvePanel.getByLabel("Charlotte: Drunk, claimed Fortune Teller")).toBeVisible();
});

test("solves puzzle 81 with Fraser Imp and Matthew Widow", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-81-arachnophobia");

  await expect(page.locator("input.title-input")).toHaveValue("Puzzle 81 - Arachnophobia");
  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Matthew or Hannah is the Spy.");
  await expect(claims).toContainText("Hannah or Charlotte is the Ravenkeeper.");
  await expect(claims).toContainText("I shot Hannah on day 3 and nothing happened.");
  const solvePanel = page.locator(".solve-panel");

  await expect(solvePanel.getByText("Satisfying worlds:")).toBeVisible();
  await expect(solvePanel.getByText("Satisfying worlds:").locator("strong")).toHaveText("1");
  await expect(solvePanel.getByLabel("Fraser: Imp, claimed Washerwoman")).toBeVisible();
  await expect(solvePanel.getByLabel("Matthew: Widow, claimed Butler")).toBeVisible();
  await expect(solvePanel.getByLabel("Charlotte: Ravenkeeper")).toBeVisible();
});

test("loads puzzle 19 with Slayer Shot death markers", async ({ page }) => {
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

test("puzzle 9 formats claim summaries without leaking hidden death causes", async ({ page }) => {
  await page.goto("/");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-09-the-new-acrobat");

  const timeline = page.getByLabel("Puzzle timeline");
  await expect(timeline).toContainText("N3 Night Deaths");
  await expect(timeline).not.toContainText("Ability Death");

  const claims = page.getByLabel("Player claim summaries");
  await expect(claims).toContainText("Neither Fraser nor Oscar is the Demon.");
  await expect(claims).not.toContainText("Fraser or Oscar not Demon");
  await expect(claims).toContainText("N2: Sula=Goblin, survived; N3: You=Drunk");
  await expect(claims).not.toContainText("I am the Gambler");
  await expect(claims).toContainText("N2: chose Fraser, survived; N3: chose Josh, died");
  await expect(claims).not.toContainText("I am the Acrobat");
  await expect(claims).toContainText("D1 gossip: Fraser.type == Demon; D2 gossip: Anna.type == Demon");
  await expect(claims).not.toContainText("I am the Gossip");

  await page.getByLabel("Claiming player").selectOption("Josh");
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

test("formats remaining structured claim summaries with their details", async ({ page }) => {
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
  await page.getByLabel("Claiming player").selectOption("Olivia");
  await expect(page.getByText("Olivia — 🔮 Fortune Teller")).toHaveCount(2);
  await expect(page.getByText("+ Add check")).toHaveCount(0);

  await page.getByLabel("Load example puzzle").selectOption("puzzle-11-false-is-the-new-black");
  await expect(page.getByLabel("Player claim summaries")).toContainText("Chose Snake Charmer.");

  await page.getByLabel("Load example puzzle").selectOption("puzzle-24-the-ultimate-blunder");
  await expect(page.getByLabel("Player claim summaries")).toContainText("Chose Adam and did not lose.");
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
