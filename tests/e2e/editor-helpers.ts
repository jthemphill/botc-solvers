import { expect, type Locator, type Page } from "@playwright/test";
import { readFileSync } from "node:fs";
import type { Claim, PuzzleDoc, TimelineEventDoc } from "../../src/schema/puzzleDoc";

export async function enterPuzzle(page: Page, doc: PuzzleDoc) {
  await page.goto("/");
  await setTitleAndPlayers(page, doc);
  await setRoleUniverseAndRules(page, doc);
  await setTimeline(page, doc.timeline ?? [], doc.players);
  await addAndFillClaims(page, doc.claims);
  await setCustomConstraints(page, doc);
}

export function comparableDoc(doc: PuzzleDoc) {
  return {
    ...doc,
    script: [...doc.script].sort(),
    timeline: doc.timeline?.map((event) => ({ ...event, players: [...event.players].sort() })),
  };
}

async function setTitleAndPlayers(page: Page, doc: PuzzleDoc) {
  if (doc.title !== undefined) await page.getByLabel("Title").fill(doc.title);

  const countInput = page.getByRole("spinbutton", { name: "Players" });
  await countInput.fill("");
  await countInput.fill(String(doc.players.length));
  await expect(page.getByRole("spinbutton", { name: "Players" })).toHaveValue(String(doc.players.length));

  const currentNames = Array.from({ length: doc.players.length }, (_, index) => `Player ${index + 1}`);
  for (const [index, name] of doc.players.entries()) {
    const currentName = currentNames[index] as string;
    if (currentName === name) continue;
    const mobile = (page.viewportSize()?.width ?? 1280) < 700;
    if (mobile) {
      await page
        .getByRole("button", { name: new RegExp(`^Player ${index + 1}: ${escapeRegExp(currentName)}[,.]`) })
        .dblclick();
    } else {
      await seatFor(page, currentName).focus();
      await page.keyboard.press("F2");
    }
    const input = page.getByLabel(`Rename ${currentName}${mobile ? " on mobile" : ""}`, { exact: true });
    await input.fill(name);
    await input.press("Enter");
    currentNames[index] = name;
  }
}

export async function setTimeline(page: Page, timeline: readonly TimelineEventDoc[], players: readonly string[]) {
  if (timeline.length === 0) return;

  for (const event of timeline) {
    await page.getByRole("button", { name: "+ Add event" }).click();

    const details = page.locator(".timeline-event-details");
    await details.getByLabel("Cause").selectOption(event.type);
    await details.getByLabel("Timing").selectOption(event.timing);
    const playerPicker = details.locator(".timeline-detail-players");
    if (event.type === "nightDeath") {
      for (const player of event.players) await playerPicker.getByLabel(player, { exact: true }).check();
      for (const player of players) {
        if (event.players.includes(player)) continue;
        const checkbox = playerPicker.getByLabel(player, { exact: true });
        if (await checkbox.isChecked()) await checkbox.uncheck();
      }
    } else {
      const player = event.players[0];
      if (player !== undefined) await playerPicker.getByLabel(player, { exact: true }).check();
    }
    if (event.caller !== undefined) {
      await details.getByLabel("Caller").selectOption(event.caller);
    }
    if (event.sourceActedBeforeDeath === true) {
      await details.getByLabel("Curse set before Witch died").check();
    }
  }
}

export async function addAndFillClaims(page: Page, claims: readonly Claim[]) {
  const panel = claimsPanel(page);

  for (const claim of claims) {
    await panel.getByLabel("Claim type").fill(claim.type);
    await panel.getByLabel("Claiming player").selectOption(claim.name);
    await panel.getByRole("button", { name: "+ Add claim" }).click();
    const blocks = panel.locator(":scope .selected-claims > .claim-block");
    await fillClaim(blocks.last(), claim);
  }
}

async function setRoleUniverseAndRules(page: Page, doc: PuzzleDoc) {
  const panel = page.locator("section.hidden-roles-editor");

  for (const role of doc.script) {
    const existing = panel.getByRole("button", { name: new RegExp(`^${escapeRegExp(role)}(?: |$)`) });
    if ((await existing.count()) > 0) continue;
    const input = panel.getByLabel("Add hidden role");
    await input.fill(role);
    await expect(panel.getByText(role, { exact: true })).toBeVisible();
  }

  if (doc.setup === "none" || doc.setup === "atheist" || doc.uniqueCharacters === false) {
    const advanced = page.locator("details.advanced-puzzle-rules");
    await advanced.locator("summary").click();
    if (doc.setup === "none") await advanced.getByLabel("Use standard setup counts").uncheck();
    if (doc.setup === "atheist") await advanced.getByLabel("Atheist puzzle rules").check();
    if (doc.uniqueCharacters === false) await advanced.getByLabel("Unique actual characters").uncheck();
  }
}

async function fillClaim(block: Locator, claim: Claim) {
  if (claim.roleTiming) {
    const advanced = block.locator("details.advanced-claim-fields");
    if (!(await advanced.evaluate((element) => element.hasAttribute("open"))))
      await advanced.locator("summary").click();
    await advanced.getByLabel("Character claim refers to").selectOption(claim.roleTiming);
  }
  switch (claim.type) {
    case "Assassin":
      if (claim.target !== undefined) await selectField(block, "Kill target", claim.target);
      if (claim.timing !== undefined) await selectField(block, "Action timing", claim.timing);
      break;
    case "Acrobat":
      for (const [index, choice] of (claim.choices ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add choice" }).click();
        if (choice.timing !== undefined) await selectField(block, "Choice timing", choice.timing, index);
        await selectField(block, "Chosen player", choice.player, index);
        if (choice.died) await checkboxField(block, "Died", index).check();
      }
      break;
    case "Investigator":
      if (claim.role ?? claim.minionRole)
        await fillRoleField(block, "Minion role", claim.role ?? claim.minionRole ?? "");
      await checkPlayers(block, "Among", claim.among);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Librarian":
      if (claim.role !== undefined) await fillRoleField(block, "Role", claim.role);
      await checkPlayers(block, "Among", claim.among ?? []);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Washerwoman":
      if (claim.role !== undefined) await fillRoleField(block, "Role", claim.role);
      await checkPlayers(block, "Among", claim.among);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Chambermaid":
      for (const [index, check] of (claim.checks ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add check" }).click();
        await selectField(block, "Left", check.left, index);
        await selectField(block, "Right", check.right, index);
        await fillField(block, "Count", String(check.count), index);
        if (check.timing !== undefined) await selectField(block, "Timing", check.timing, index);
      }
      break;
    case "Chef":
      if (claim.count !== undefined) await fillField(block, "Count", String(claim.count));
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Empath":
      if (claim.count !== undefined) await fillField(block, "Count", String(claim.count));
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Exorcist":
      for (const [index, choice] of (claim.choices ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add choice" }).click();
        if (choice.timing !== undefined) await selectField(block, "Choice timing", choice.timing, index);
        await selectField(block, "Chosen player", choice.player, index);
      }
      break;
    case "Innkeeper":
      for (const [index, choice] of (claim.choices ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add choice" }).click();
        if (choice.timing !== undefined) await selectField(block, "Choice timing", choice.timing, index);
        await checkPlayers(block, "Protected players", choice.players, index);
      }
      break;
    case "Devil's Advocate":
      for (const [index, choice] of (claim.choices ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add choice" }).click();
        if (choice.timing !== undefined) await selectField(block, "Choice timing", choice.timing, index);
        await selectField(block, "Protected player", choice.player, index);
      }
      break;
    case "Godfather":
      for (const role of claim.outsiderRoles ?? []) await addRoleToList(block, "Godfather known Outsiders", role);
      for (const [index, choice] of (claim.choices ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add choice" }).click();
        if (choice.timing !== undefined) await selectField(block, "Choice timing", choice.timing, index);
        await selectField(block, "Revenge target", choice.player, index);
      }
      break;
    case "Grandmother":
      if (claim.grandchild !== undefined) await selectField(block, "Grandchild", claim.grandchild);
      if (claim.role !== undefined) await fillRoleField(block, "Grandchild role", claim.role);
      break;
    case "Sailor":
      for (const [index, choice] of (claim.choices ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add choice" }).click();
        if (choice.timing !== undefined) await selectField(block, "Choice timing", choice.timing, index);
        await selectField(block, "Drinking partner", choice.player, index);
      }
      break;
    case "Moonchild":
      if (claim.chosen !== undefined) await selectField(block, "Chosen player", claim.chosen);
      if (claim.timing !== undefined) await selectField(block, "Choice timing", claim.timing);
      break;
    case "Flowergirl":
      for (const [index, vote] of (claim.votes ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add vote" }).click();
        await selectField(block, "Vote timing", vote.timing, index);
        await checkPlayers(block, "Voters", vote.voters, index);
        await selectField(block, "Demon voted", vote.demonVoted ? "true" : "false", index);
      }
      break;
    case "FortuneTeller": {
      const check = claim.checks[0];
      if (check !== undefined) {
        await selectField(block, "Left", check.left);
        await selectField(block, "Right", check.right);
        if (check.yes) await checkboxField(block, "Saw demon").check();
        if (check.timing !== undefined) await selectField(block, "Timing", check.timing);
      }
      break;
    }
    case "Undertaker":
      if (claim.player !== undefined) await selectField(block, "Executed player", claim.player);
      if (claim.role !== undefined) await fillRoleField(block, "Role learned", claim.role);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Noble":
      await checkPlayers(block, "One evil among", claim.oneEvilAmong ?? []);
      break;
    case "Steward":
      if (claim.goodPlayer !== undefined) await selectField(block, "Good player", claim.goodPlayer);
      break;
    case "Knight":
      await checkPlayers(block, "No demon among", claim.noDemonAmong);
      break;
    case "Seamstress":
      await selectField(block, "Left", claim.among[0] ?? "");
      await selectField(block, "Right", claim.among[1] ?? "");
      if (claim.aligned !== undefined) await selectField(block, "Same alignment", claim.aligned ? "same" : "different");
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Juggler":
      if (claim.correctCount !== undefined) await fillField(block, "Correct count", String(claim.correctCount));
      for (const [player, role] of Object.entries(claim.guesses)) {
        await fillRoleInput(block.getByLabel(`${player} Juggler guessed role`), role);
      }
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Dreamer":
      if (claim.player !== undefined) await selectField(block, "Player checked", claim.player);
      for (const role of claim.roles) await addRoleToList(block, "Dreamer possible roles", role);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Shugenja":
      if (claim.evilDirection !== undefined) await selectField(block, "Evil direction", claim.evilDirection);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Clockmaker":
      if (claim.distance !== undefined) await fillField(block, "Demon-minion distance", String(claim.distance));
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Courtier":
      if (claim.role !== undefined) await fillRoleField(block, "Chosen role", claim.role);
      if (claim.timing !== undefined) await selectField(block, "Choice timing", claim.timing);
      for (let index = 1; index < (claim.drunkTimings ?? []).length; index += 1) {
        await block.getByRole("button", { name: "+ Add timing" }).click();
      }
      for (const [index, timing] of (claim.drunkTimings ?? []).entries()) {
        await selectField(block, "Drunk timing", timing, index);
      }
      break;
    case "Mathematician":
      for (let index = 1; index < (claim.malfunctions ?? []).length; index += 1) {
        await block.getByRole("button", { name: "+ Add count" }).click();
      }
      for (const [index, entry] of (claim.malfunctions ?? []).entries()) {
        await selectField(block, "Timing", entry.timing, index);
        await fillField(block, "Malfunctions", String(entry.count), index);
      }
      break;
    case "Town Crier":
      for (let index = 1; index < claim.checks.length; index += 1) {
        await block.getByRole("button", { name: "+ Add check" }).click();
      }
      for (const [index, check] of claim.checks.entries()) {
        await selectField(block, "Timing", check.timing, index);
        await checkPlayers(block, "Nominators", check.nominators, index);
        if (check.minionNominated) await block.getByLabel("Minion nominated").nth(index).check();
      }
      break;
    case "Ravenkeeper":
      if (claim.player !== undefined) await selectField(block, "Player seen", claim.player);
      if (claim.role !== undefined) await fillRoleField(block, "Role seen", claim.role);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Sage":
      await checkPlayers(block, "Demon among", claim.demonAmong ?? []);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Professor":
      if (claim.target !== undefined) await selectField(block, "Resurrection target", claim.target);
      if (claim.timing !== undefined) await selectField(block, "Action timing", claim.timing);
      break;
    case "Slayer":
      if (claim.target !== undefined) await selectField(block, "Shot player", claim.target);
      if (claim.timing !== undefined) await selectField(block, "Shot timing", claim.timing);
      if (claim.killed !== undefined) await selectField(block, "Target died", claim.killed ? "yes" : "no");
      break;
    case "Snake Charmer": {
      const check = claim.checks[0];
      if (check !== undefined) {
        await selectField(block, "Checked player", check.player);
        await selectField(block, "Is Demon", check.demon ? "yes" : "no");
        await selectField(block, "Timing", check.timing);
      }
      break;
    }
    case "VillageIdiot":
      for (const [index, check] of claim.checks.entries()) {
        await block.getByRole("button", { name: "+ Add check" }).click();
        if (check.timing !== undefined) await selectField(block, "Timing", check.timing, index);
        await selectField(block, "Checked player", check.player, index);
        await block
          .getByLabel(check.good ? "Good" : "Evil")
          .nth(index)
          .check();
      }
      break;
    case "Balloonist":
      for (const [index, pair] of claim.differentCharacterTypePairs.entries()) {
        await block.getByRole("button", { name: "+ Add pair" }).click();
        const row = block
          .locator("xpath=.//*[contains(concat(' ', normalize-space(@class), ' '), ' row ')][count(.//select) >= 2]")
          .nth(index);
        await row.locator("select").nth(0).selectOption(pair[0]);
        await row.locator("select").nth(1).selectOption(pair[1]);
      }
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Savant":
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      for (const [index, option] of (claim.statements[0]?.options ?? []).entries()) {
        await block.locator(".statement-block textarea").nth(index).fill(option);
      }
      break;
    case "Gambler":
      for (const [index, guess] of (claim.guesses ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add guess" }).click();
        await selectField(block, "Player", guess.player, index);
        await fillRoleField(block, "Role", guess.role, index);
        if (guess.timing !== undefined) await selectField(block, "Timing", guess.timing, index);
      }
      break;
    case "Princess":
      for (const [index, nomination] of (claim.nominations ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add nomination" }).click();
        if (nomination.timing !== undefined) await selectField(block, "Nomination timing", nomination.timing, index);
        await selectField(block, "Nominated player", nomination.player, index);
      }
      break;
    case "Prodigy":
      for (const [index, check] of (claim.checks ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add check" }).click();
        if (check.timing !== undefined) await selectField(block, "Check timing", check.timing, index);
        await selectField(block, "Chosen player", check.chosen, index);
        await selectField(block, "Learned player", check.learned, index);
      }
      break;
    case "Puzzlemaster":
      for (const [index, guess] of (claim.guesses ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add guess" }).click();
        if (guess.timing !== undefined) await selectField(block, "Guess timing", guess.timing, index);
        await selectField(block, "Guessed drunk", guess.player, index);
        await selectField(block, "Learned Demon", guess.learnedDemon, index);
      }
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Gossip":
      for (const [index, statement] of (claim.statements ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add statement" }).click();
        if (statement.timing !== undefined) await selectField(block, "Timing", statement.timing, index);
        await fillField(block, "Statement", statement.expression, index);
      }
      break;
    case "Oracle":
      if (claim.count !== undefined) await fillField(block, "Dead evil count", String(claim.count));
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Philosopher":
      if (claim.role !== undefined) await fillRoleField(block, "Chosen role", claim.role);
      if (claim.timing !== undefined) await selectField(block, "Choice timing", claim.timing);
      if (claim.seamstress !== undefined) {
        await selectField(block, "Seamstress left", claim.seamstress.among[0] ?? "");
        await selectField(block, "Seamstress right", claim.seamstress.among[1] ?? "");
        if (claim.seamstress.aligned !== undefined && !claim.seamstress.aligned) {
          await checkboxField(block, "Aligned").uncheck();
        }
        if (claim.seamstress.timing !== undefined) await selectField(block, "Info timing", claim.seamstress.timing);
      }
      break;
    case "Legionary":
      for (const [index, entry] of (claim.counts ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add count" }).click();
        await fillField(block, "Living evil", String(entry.count), index);
        if (entry.timing !== undefined) await selectField(block, "Timing", entry.timing, index);
      }
      break;
    case "Klutz":
      if (claim.chosen !== undefined) await selectField(block, "Chosen player", claim.chosen);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Virgin":
      if (claim.nominator !== undefined) await selectField(block, "Nominator", claim.nominator);
      if (claim.executed !== undefined)
        await selectField(block, "Nominator executed", claim.executed ? "true" : "false");
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Nightwatchman":
      if (claim.chosen !== undefined) await selectField(block, "Chosen player", claim.chosen);
      if (claim.learned !== undefined) await selectField(block, "Learned", claim.learned ? "true" : "false");
      if (claim.confirmedByChosen === true) await checkboxField(block, "Confirmed by chosen").check();
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Artist":
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    default:
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
  }

  for (const role of claim.possibleActualRoles ?? []) await addAdvancedRole(block, role);
  if (claim.alignment !== undefined) {
    await openAdvancedFields(block);
    await selectField(block, "Claimed alignment", claim.alignment);
  }
  if (claim.heardWidowCall === true) await block.getByLabel("Heard the Widow's call").check();
  if (claim.knownEvilTwin !== undefined) await selectField(block, "Known Evil Twin", claim.knownEvilTwin);
  if (claim.type === "Artist") await fillArtistInfo(block, claim.info ?? []);
}

async function fillArtistInfo(block: Locator, info: NonNullable<Claim["info"]>) {
  for (const [index, entry] of info.entries()) {
    await block.getByRole("button", { name: "+ Add info" }).click();
    const statementBlock = block.locator(".statement-block").filter({ hasText: "Info" });
    if (entry.timing !== undefined) await selectField(statementBlock, "Timing", entry.timing, index);
    if (entry.expression !== undefined) await fillField(statementBlock, "Expression", entry.expression, index);
  }
}

export async function setCustomConstraints(page: Page, doc: PuzzleDoc) {
  if ((doc.constraints ?? []).length === 0) return;
  const panel = page.locator("section.panel", { hasText: "Custom constraints" });

  for (const constraint of doc.constraints ?? []) {
    await panel.getByRole("button", { name: "+ Add custom constraint" }).click();
    const block = panel.locator(":scope > .claim-block").last();
    await fillField(block, "Expression", constraint.expression);
  }
}

export async function exportPuzzleDoc(page: Page): Promise<PuzzleDoc> {
  const downloadPromise = page.waitForEvent("download");
  await page.getByRole("button", { name: "Export JSON" }).click();
  const download = await downloadPromise;
  const path = await download.path();
  if (path === null) throw new Error("Export download did not produce a local file");
  return JSON.parse(readFileSync(path, "utf8")) as PuzzleDoc;
}

export function claimsPanel(page: Page): Locator {
  return page.locator("section.panel", { has: page.getByRole("heading", { name: "Claims" }) });
}

function seatFor(page: Page, player: string): Locator {
  return page.getByRole("button", { name: new RegExp(`Seat \\d+: ${escapeRegExp(player)}(?:[,.])`) });
}

function fieldRoot(scope: Locator, label: string, index = 0): Locator {
  return scope
    .locator(
      `xpath=.//*[contains(concat(" ", normalize-space(@class), " "), " field-grid ")]/*[self::span and normalize-space(.)=${xpathLiteral(
        label,
      )}]`,
    )
    .nth(index)
    .locator("xpath=following-sibling::*[1]");
}

export async function fillField(scope: Locator, label: string, value: string, index = 0) {
  const root = fieldRoot(scope, label, index);
  await fillControl(root, value);
}

export async function fillRoleField(scope: Locator, label: string, value: string, index = 0) {
  const root = fieldRoot(scope, label, index);
  const input = await control(root, "input");
  await fillRoleInput(input, value);
}

async function fillRoleInput(input: Locator, value: string) {
  await input.fill(value);
  await input.press("Enter");
  await expect(input).toHaveValue(value);
}

export async function selectField(scope: Locator, label: string, value: string, index = 0) {
  const root = fieldRoot(scope, label, index);
  const select = await control(root, "select");
  await select.selectOption(value);
}

function checkboxField(scope: Locator, label: string, index = 0): Locator {
  return fieldRoot(scope, label, index).locator("xpath=self::input[@type='checkbox'] | .//input[@type='checkbox']");
}

export async function checkPlayers(scope: Locator, label: string, players: readonly string[], index = 0) {
  const root = fieldRoot(scope, label, index);
  for (const player of players) await root.getByLabel(player, { exact: true }).check();
}

async function addAdvancedRole(block: Locator, role: string) {
  await openAdvancedFields(block);
  await addRoleToList(block, "Possible actual roles", role);
}

async function openAdvancedFields(block: Locator) {
  const details = block.locator("details.advanced-claim-fields");
  const open = await details.evaluate((element) => (element as HTMLDetailsElement).open);
  if (!open) await details.locator("summary").click();
}

export async function addRoleToList(scope: Locator, label: string, role: string) {
  const input = scope.getByLabel(`Add ${label}`).last();
  await input.fill(role);
  await expect(scope.getByRole("button", { name: new RegExp(escapeRegExp(role)) }).last()).toBeVisible();
}

async function control(root: Locator, selector: string): Promise<Locator> {
  if (await root.evaluate((element, selector) => element.matches(selector), selector)) return root;
  return root.locator(selector).first();
}

async function fillControl(root: Locator, value: string) {
  const target = await control(root, "input, textarea");
  await target.fill(value);
}

function escapeRegExp(value: string): string {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function xpathLiteral(value: string): string {
  if (!value.includes("'")) return `'${value}'`;
  if (!value.includes('"')) return `"${value}"`;
  return `concat('${value.replace(/'/g, `', "'", '`)}')`;
}
