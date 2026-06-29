import { expect, test, type Locator, type Page } from "@playwright/test";
import { readFileSync, readdirSync } from "node:fs";
import { fileURLToPath } from "node:url";

const examplesDir = fileURLToPath(new URL("../../src/examples/", import.meta.url));
const puzzleSpecs = readdirSync(examplesDir)
  .filter((file) => file.endsWith(".json") && !file.endsWith(".solutions.json"))
  .sort((left, right) => left.localeCompare(right))
  .map((file) => ({
    id: file.replace(/\.json$/, ""),
    doc: JSON.parse(readFileSync(`${examplesDir}/${file}`, "utf8")) as PuzzleDoc,
  }));

type PuzzleDoc = {
  readonly version?: 1;
  readonly title?: string;
  readonly players: readonly string[];
  readonly script: readonly string[];
  readonly setup?: "standard" | "none" | "atheist";
  readonly uniqueCharacters?: boolean;
  readonly fixedRoles?: readonly RoleConstraint[];
  readonly forbiddenRoles?: readonly RoleConstraint[];
  readonly constraints?: readonly PuzzleConstraintDoc[];
  readonly timeline?: readonly TimelineEventDoc[];
  readonly claims: readonly Claim[];
};

type RoleConstraint = {
  readonly name: string;
  readonly roles: readonly string[];
};

type PuzzleConstraintDoc = {
  readonly expression: string;
};

type TimelineEventDoc = {
  readonly timing: string;
  readonly type: "nominationDeath" | "witchCurse" | "slayerShot" | "execution" | "nightDeath" | "doomsayerDeath";
  readonly players: readonly string[];
  readonly caller?: string;
};

type Claim = Record<string, any> & {
  readonly type: string;
  readonly name: string;
  readonly timing?: string;
};

test.describe("manual puzzle entry", () => {
  test.setTimeout(60_000);

  for (const { id, doc } of puzzleSpecs) {
    test(`${id} can be created from scratch`, async ({ page }) => {
      await page.goto("/");

      await setTitleAndPlayers(page, doc);
      await setScriptRules(page, doc);
      await setTimeline(page, doc.timeline ?? []);
      const claims = manualClaimsFor(doc.claims);
      await addClaimShells(page, claims);
      await fillClaims(page, claims, doc);
      await setRoleConstraints(page, doc);

      const exported = await exportPuzzleDoc(page);
      expect(normalizeDoc(exported)).toEqual(normalizeDoc({ ...doc, claims: manualClaimsFor(doc.claims) }));
    });
  }
});

async function setTitleAndPlayers(page: Page, doc: PuzzleDoc) {
  if (doc.title !== undefined) await page.getByLabel("Title").fill(doc.title);

  const countInput = page.getByLabel("Players");
  await countInput.fill("");
  await countInput.fill(String(doc.players.length));
  await expect(page.locator(".seat-button")).toHaveCount(doc.players.length);

  const currentNames = Array.from({ length: doc.players.length }, (_, index) => `Player ${index + 1}`);
  for (const [index, name] of doc.players.entries()) {
    const currentName = currentNames[index] as string;
    if (currentName === name) continue;
    await seatFor(page, currentName).focus();
    await page.keyboard.press("F2");
    const input = page.getByLabel(`Rename ${currentName}`);
    await input.fill(name);
    await input.press("Enter");
    currentNames[index] = name;
  }
}

async function setScriptRules(page: Page, doc: PuzzleDoc) {
  await openWorkbenchTab(page, "Script");
  const rules = page.locator(".script-rules-grid");
  await rules.getByLabel("Setup").selectOption(doc.setup ?? "standard");
  if (doc.uniqueCharacters === false) await rules.getByLabel("Unique characters").uncheck();

  for (const role of doc.script) {
    const search = page.getByLabel("Search roles");
    await search.fill(role);
    await search.press("Enter");
    await expect(page.locator(".script-picker-panel .role-stamp", { hasText: role })).toBeVisible();
  }
}

async function setTimeline(page: Page, timeline: readonly TimelineEventDoc[]) {
  if (timeline.length === 0) return;
  await openWorkbenchTab(page, "Draw");

  for (const event of timeline) {
    const firstPlayer = event.players[0];
    if (firstPlayer === undefined) continue;
    const dropZone =
      event.type === "nightDeath"
        ? page.locator(".timeline-drop-zone.night-kill")
        : page.locator(".timeline-drop-zone.execution");
    const dataTransfer = await page.evaluateHandle(() => new DataTransfer());
    await seatFor(page, firstPlayer).dispatchEvent("dragstart", { dataTransfer });
    await dropZone.dispatchEvent("dragenter", { dataTransfer });
    await dropZone.dispatchEvent("dragover", { dataTransfer });
    await dropZone.dispatchEvent("drop", { dataTransfer });

    const details = page.locator(".timeline-event-details");
    await details.getByLabel("Cause").selectOption(event.type);
    await details.getByLabel("Timing").selectOption(event.timing);
    for (const player of event.players) {
      await details.locator(".timeline-detail-players").getByLabel(player, { exact: true }).check();
    }
    if (event.caller !== undefined) {
      await details.getByLabel("Caller").selectOption(event.caller);
    }
  }
}

async function addClaimShells(page: Page, claims: readonly Claim[]) {
  await openWorkbenchTab(page, "Claims");
  const panel = claimsPanel(page);
  const addRow = panel.locator(":scope > .row").first();

  for (const claim of claims) {
    await addRow.locator("select").nth(0).selectOption(claim.type);
    await addRow.locator("select").nth(1).selectOption(claim.name);
    await addRow.getByRole("button", { name: "+ Add claim" }).click();
  }

  await expect(panel.locator(":scope > .claim-block")).toHaveCount(claims.length);
}

async function fillClaims(page: Page, claims: readonly Claim[], doc: PuzzleDoc) {
  const blocks = claimsPanel(page).locator(":scope > .claim-block");
  for (const [index, claim] of claims.entries()) {
    await fillClaim(blocks.nth(index), claim, doc);
  }
}

async function fillClaim(block: Locator, claim: Claim, doc: PuzzleDoc) {
  switch (claim.type) {
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
      if (claim.outsiderCount === 0) await checkboxField(block, "No Outsiders").check();
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
      await checkPlayers(block, "Neighbors", claim.neighbors ?? []);
      break;
    case "Exorcist":
      for (const [index, choice] of (claim.choices ?? []).entries()) {
        await block.getByRole("button", { name: "+ Add choice" }).click();
        if (choice.timing !== undefined) await selectField(block, "Choice timing", choice.timing, index);
        await selectField(block, "Chosen player", choice.player, index);
      }
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
      await checkPlayers(block, "One evil among", claim.oneEvilAmong ?? claim.among ?? []);
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
        await fillRoleInput(block.getByLabel(`${player} Juggler guessed role`), String(role));
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
      await checkPlayers(block, "Seating override", claim.seating ?? []);
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
    case "Ravenkeeper":
      if (claim.player !== undefined) await selectField(block, "Player seen", claim.player);
      if (claim.role !== undefined) await fillRoleField(block, "Role seen", claim.role);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
      break;
    case "Sage":
      await checkPlayers(block, "Demon among", claim.demonAmong ?? []);
      if (claim.timing !== undefined) await selectField(block, "Timing", claim.timing);
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
      if (claim.evilTwin !== undefined) {
        await selectField(block, "Evil Twin", claim.evilTwin.player);
        await selectField(block, "Evil Twin timing", claim.evilTwin.timing);
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
        if (guess.survived !== undefined)
          await selectField(block, "Survived", guess.survived ? "true" : "false", index);
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
      await checkPlayers(block, "Dead players", claim.deadPlayers ?? []);
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
      if (claim.lost !== undefined) await selectField(block, "Lost", claim.lost ? "true" : "false");
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

  for (const role of claim.extraPossibleActualRoles ?? []) await addAdvancedRole(block, role);
  if (claim.heardWidowCall === true) await block.getByLabel("Heard the Widow's call").check();
  if (claim.type === "Artist") await fillArtistInfo(block, claim.info ?? []);
}

async function fillArtistInfo(block: Locator, info: readonly Record<string, string | undefined>[]) {
  for (const [index, entry] of info.entries()) {
    await block.getByRole("button", { name: "+ Add info" }).click();
    const statementBlock = block.locator(".statement-block").filter({ hasText: "Info" });
    if (entry.timing !== undefined) await selectField(statementBlock, "Timing", entry.timing, index);
    if (entry.expression !== undefined) await fillField(statementBlock, "Expression", entry.expression, index);
  }
}

async function setRoleConstraints(page: Page, doc: PuzzleDoc) {
  if (
    (doc.fixedRoles ?? []).length === 0 &&
    (doc.forbiddenRoles ?? []).length === 0 &&
    (doc.constraints ?? []).length === 0
  )
    return;
  await openWorkbenchTab(page, "Script");
  const panel = page.locator("section.panel", { hasText: "Role constraints" });

  for (const fixedRole of doc.fixedRoles ?? []) {
    await panel.getByRole("button", { name: "+ Add fixed role" }).click();
    const block = panel.locator(":scope > .claim-block").last();
    await block.locator("select").selectOption(fixedRole.name);
    for (const role of fixedRole.roles) await addRoleToList(block, "Possible roles", role);
  }

  for (const forbiddenRole of doc.forbiddenRoles ?? []) {
    await panel.getByRole("button", { name: "+ Add excluded role" }).click();
    const block = panel.locator(":scope > .claim-block").last();
    await block.locator("select").selectOption(forbiddenRole.name);
    for (const role of forbiddenRole.roles) await addRoleToList(block, "Excluded roles", role);
  }

  for (const constraint of doc.constraints ?? []) {
    await panel.getByRole("button", { name: "+ Add custom constraint" }).click();
    const block = panel.locator(":scope > .claim-block").last();
    await fillField(block, "Expression", constraint.expression);
  }
}

async function exportPuzzleDoc(page: Page): Promise<PuzzleDoc> {
  const downloadPromise = page.waitForEvent("download");
  await page.getByRole("button", { name: "Export JSON" }).click();
  const download = await downloadPromise;
  const path = await download.path();
  if (path === null) throw new Error("Export download did not produce a local file");
  return JSON.parse(readFileSync(path, "utf8")) as PuzzleDoc;
}

async function openWorkbenchTab(page: Page, tab: "Draw" | "Script" | "Claims" | "Solve") {
  await page.getByRole("navigation", { name: "Workbench sections" }).getByRole("button", { name: tab }).click();
}

function claimsPanel(page: Page): Locator {
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

async function fillField(scope: Locator, label: string, value: string, index = 0) {
  const root = fieldRoot(scope, label, index);
  await fillControl(root, value);
}

async function fillRoleField(scope: Locator, label: string, value: string, index = 0) {
  const root = fieldRoot(scope, label, index);
  const input = await control(root, "input");
  await fillRoleInput(input, value);
}

async function fillRoleInput(input: Locator, value: string) {
  await input.fill(value);
  await input.press("Enter");
  await expect(input).toHaveValue(value);
}

async function selectField(scope: Locator, label: string, value: string, index = 0) {
  const root = fieldRoot(scope, label, index);
  const select = await control(root, "select");
  await select.selectOption(value);
}

function checkboxField(scope: Locator, label: string, index = 0): Locator {
  return fieldRoot(scope, label, index).locator("xpath=self::input[@type='checkbox'] | .//input[@type='checkbox']");
}

async function checkPlayers(scope: Locator, label: string, players: readonly string[], index = 0) {
  const root = fieldRoot(scope, label, index);
  for (const player of players) await root.getByLabel(player, { exact: true }).check();
}

async function addAdvancedRole(block: Locator, role: string) {
  const details = block.locator("details.advanced-claim-fields");
  const open = await details.evaluate((element) => (element as HTMLDetailsElement).open);
  if (!open) await details.locator("summary").click();
  await addRoleToList(block, "Possible actual roles", role);
}

async function addRoleToList(scope: Locator, label: string, role: string) {
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

function manualClaimsFor(claims: readonly Claim[]): Claim[] {
  return claims.flatMap((claim) => {
    if (claim.type === "FortuneTeller" && claim.checks.length > 1) {
      const { info: _info, ...claimWithoutInfo } = claim;
      return claim.checks.map((check: unknown, index: number) =>
        index === 0 ? { ...claim, checks: [check] } : { ...claimWithoutInfo, checks: [check] },
      );
    }
    if (claim.type === "Snake Charmer" && claim.checks.length > 1) {
      const { info: _info, evilTwin: _evilTwin, ...claimWithoutSharedInfo } = claim;
      return claim.checks.map((check: unknown, index: number) =>
        index === 0 ? { ...claim, checks: [check] } : { ...claimWithoutSharedInfo, checks: [check] },
      );
    }
    if (claim.type === "Juggler" && claim.timing === undefined) {
      return [{ ...claim, timing: "night_2" }];
    }
    return [claim];
  });
}

function normalizeDoc(doc: PuzzleDoc): unknown {
  const normalized = stripEmpty({
    ...doc,
    version: undefined,
    setup: doc.setup === "standard" ? undefined : doc.setup,
    uniqueCharacters: doc.uniqueCharacters === true ? undefined : doc.uniqueCharacters,
    script: sorted(doc.script),
    fixedRoles: normalizeRoleConstraints(doc.fixedRoles),
    forbiddenRoles: normalizeRoleConstraints(doc.forbiddenRoles),
    timeline: doc.timeline === undefined ? undefined : [...doc.timeline].sort(compareTimelineEvents),
    claims: manualClaimsFor(doc.claims).map(normalizeClaim),
  });
  return normalized;
}

function normalizeRoleConstraints(
  constraints: PuzzleDoc["fixedRoles"] | PuzzleDoc["forbiddenRoles"],
): PuzzleDoc["fixedRoles"] | PuzzleDoc["forbiddenRoles"] {
  if (constraints === undefined) return undefined;
  return constraints
    .map((constraint) => ({ ...constraint, roles: sorted(constraint.roles) }))
    .sort(
      (left, right) => left.name.localeCompare(right.name) || left.roles.join("|").localeCompare(right.roles.join("|")),
    );
}

function normalizeClaim(claim: Claim): unknown {
  const normalized = { ...claim } as Record<string, unknown>;
  delete normalized.gameContinued;
  delete normalized.minionRole;
  if (claim.type === "Investigator") {
    normalized.role = claim.role ?? claim.minionRole;
    normalized.among = claim.among.slice(0, 2);
  }
  if (claim.type === "Librarian" && claim.among !== undefined) normalized.among = claim.among.slice(0, 2);
  if (claim.type === "Washerwoman") normalized.among = claim.among.slice(0, 2);
  if ("roles" in normalized && Array.isArray(normalized.roles)) normalized.roles = sorted(normalized.roles);
  if ("extraPossibleActualRoles" in normalized && Array.isArray(normalized.extraPossibleActualRoles)) {
    normalized.extraPossibleActualRoles = sorted(normalized.extraPossibleActualRoles);
  }
  if (claim.type === "Noble" && Array.isArray(normalized.among) && normalized.among.length === 0)
    delete normalized.among;
  return stripEmpty(normalized);
}

function stripEmpty(value: unknown): unknown {
  if (Array.isArray(value)) return value.map(stripEmpty);
  if (value === null || typeof value !== "object") return value;
  const result: Record<string, unknown> = {};
  for (const [key, entry] of Object.entries(value)) {
    if (entry === undefined) continue;
    if (Array.isArray(entry) && entry.length === 0 && key !== "claims" && key !== "players" && key !== "script")
      continue;
    result[key] = stripEmpty(entry);
  }
  return result;
}

function sorted(values: readonly string[]): string[] {
  return [...values].sort((left, right) => left.localeCompare(right));
}

function compareTimelineEvents(left: TimelineEventDoc, right: TimelineEventDoc): number {
  return timingOrder(left.timing) - timingOrder(right.timing);
}

function timingOrder(timing: string): number {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) return Number.MAX_SAFE_INTEGER;
  return Number(match[2]) * 2 + (match[1] === "day" ? 1 : 0);
}

function escapeRegExp(value: string): string {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function xpathLiteral(value: string): string {
  if (!value.includes("'")) return `'${value}'`;
  if (!value.includes('"')) return `"${value}"`;
  return `concat('${value.replace(/'/g, `', "'", '`)}')`;
}
