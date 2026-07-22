import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { buildFromDoc } from "../src/builders/buildFromDoc";
import { CharacterType, roleCharacterType } from "../src/model/core";
import type { Timing, World } from "../src/model/model";
import { roleByName } from "../src/model/roleRegistry";
import { KissatBackend } from "../src/model/sat";
import type { Claim, PuzzleDoc } from "../src/schema/puzzleDoc";
import { validatePuzzleDoc } from "../src/schema/validate";

const PUZZLE_PATH = fileURLToPath(new URL("../src/examples/a-clean-sweep.json", import.meta.url));

const backend = await KissatBackend.create();
const puzzle = validatePuzzleDoc(JSON.parse(readFileSync(PUZZLE_PATH, "utf8")));

if (process.argv.includes("--verify")) {
  await verify(puzzle);
} else if (process.argv.includes("--solutions-json")) {
  await printSolutionsJson(puzzle);
} else if (process.argv.includes("--search-gossip")) {
  await searchGossip(puzzle);
} else if (process.argv.includes("--search-actions")) {
  await searchActions(puzzle);
} else if (process.argv.includes("--search-chronology")) {
  await searchChronology(puzzle);
} else if (process.argv.includes("--search-roster")) {
  await searchRoster(puzzle);
} else if (process.argv.includes("--search-deaths")) {
  await searchDeaths(puzzle);
} else {
  await diagnose(puzzle);
}

async function searchRoster(source: PuzzleDoc): Promise<void> {
  const fixedClaimants = new Set(["Ada", "You", "Eve", "Finn", "Drew", "Hugo"]);
  const fixedClaims = source.claims.filter((claim) => fixedClaimants.has(claim.name));
  const flexiblePlayers = source.players.filter((player) => !fixedClaimants.has(player));
  const fixedTypes = new Set<string>(fixedClaims.map((claim) => claim.type));
  const passiveTypes = ["Grandmother", "Fool", "Goon", "Lunatic", "Tinker", "Moonchild", "Minstrel"].filter(
    (role) => !fixedTypes.has(role),
  );
  const candidates: Array<{
    readonly doc: PuzzleDoc;
    readonly roster: string;
    readonly worlds: number;
    readonly teamCount: number;
    readonly uniqueTeam?: EvilTeam;
    readonly hiddenEvilGoon: boolean;
    readonly necessaryClaims: number;
  }> = [];

  for (const leftType of passiveTypes) {
    for (const middleType of passiveTypes) {
      for (const rightType of passiveTypes) {
        if (new Set([leftType, middleType, rightType]).size !== 3) continue;
        const claims: Claim[] = [
          ...fixedClaims,
          { type: leftType, name: flexiblePlayers[0] } as Claim,
          { type: middleType, name: flexiblePlayers[1] } as Claim,
          { type: rightType, name: flexiblePlayers[2] } as Claim,
        ];
        const candidate = {
          ...source,
          script: [...new Set([...source.script, leftType, middleType, rightType])],
          claims,
        };
        if (!hasExplicitOutsiderClaim(candidate) || !claims.some((claim) => claim.type === "Minstrel")) continue;

        const worlds = await solve(candidate, 50);
        if (worlds.length === 0) continue;
        const teams = distinctTeams(worlds, candidate);
        const uniqueTeam = worlds.length < 50 && teams.length === 1 ? teams[0] : undefined;
        const hiddenEvilGoon = uniqueTeam !== undefined && (await everyWorldHasLyingEvilGoon(candidate));
        let necessaryClaims = 0;
        if (uniqueTeam !== undefined && hiddenEvilGoon && (await hasUniqueAnswer(candidate, uniqueTeam))) {
          necessaryClaims = (await claimNecessity(candidate, uniqueTeam)).filter((result) => result.necessary).length;
        }
        candidates.push({
          doc: candidate,
          roster: claims.map((claim) => `${claim.name}=${claim.type}`).join(", "),
          worlds: worlds.length,
          teamCount: teams.length,
          uniqueTeam,
          hiddenEvilGoon,
          necessaryClaims,
        });
      }
    }
  }

  candidates.sort(
    (left, right) =>
      Number(right.uniqueTeam !== undefined) - Number(left.uniqueTeam !== undefined) ||
      Number(right.hiddenEvilGoon) - Number(left.hiddenEvilGoon) ||
      right.necessaryClaims - left.necessaryClaims ||
      left.teamCount - right.teamCount ||
      left.worlds - right.worlds,
  );
  const count = numericArg("--show", 10);
  for (const candidate of candidates.slice(0, count)) {
    const answer = candidate.uniqueTeam
      ? `Demon ${candidate.uniqueTeam.demon}; Minions ${candidate.uniqueTeam.minions.join(", ")}`
      : `${candidate.teamCount}${candidate.worlds === 50 ? "+" : ""} evil teams`;
    console.log(
      `${candidate.necessaryClaims}/9 necessary; hidden evil Goon=${candidate.hiddenEvilGoon}; ${candidate.worlds}${candidate.worlds === 50 ? "+" : ""} worlds; ${answer}\n  ${candidate.roster}`,
    );
  }
  const best = candidates[0];
  if (best !== undefined) console.log(`\nBest candidate\n${JSON.stringify(best.doc, null, 2)}`);
}

async function searchDeaths(source: PuzzleDoc): Promise<void> {
  if (!hasExplicitOutsiderClaim(source)) throw new Error("Death search requires an explicit Outsider claim.");
  const expressions = [
    "Ada.alignment == Evil",
    "Ada.type != Outsider",
    "some Po.~role",
    "some Pukka.~role",
    "Iris.role != Shabaloth",
    "Drew.type != Minion",
    "Hugo.type != Minion",
    "Ada.type != Outsider or some Po.~role",
    "some Po.~role or Drew.type != Minion",
  ];
  const dayThreeExecution = (source.timeline ?? []).find(
    (event) => event.timing === "day_3" && event.type === "execution",
  )?.players[0];
  const living = [...livingAt(source, "night_3")].filter((player) => player !== "Eve" && player !== dayThreeExecution);
  const candidates: Array<{
    readonly doc: PuzzleDoc;
    readonly worlds: number;
    readonly team: EvilTeam;
    readonly necessaryClaims: number;
    readonly necessaryDetails: number;
  }> = [];

  for (let leftIndex = 0; leftIndex < living.length; leftIndex += 1) {
    for (let rightIndex = leftIndex + 1; rightIndex < living.length; rightIndex += 1) {
      for (const expression of expressions) {
        const deaths = [living[leftIndex] as string, living[rightIndex] as string, "Eve"];
        const candidate: PuzzleDoc = {
          ...source,
          timeline: (source.timeline ?? []).map((event) =>
            event.timing === "night_3" && event.type === "nightDeath" ? { ...event, players: deaths } : event,
          ),
          claims: source.claims.map((claim): Claim =>
            claim.type === "Gossip"
              ? {
                  ...claim,
                  statements: [{ timing: claim.statements?.[0]?.timing ?? "day_1", expression }],
                }
              : claim,
          ),
        };
        const worlds = await solve(candidate, 50);
        if (worlds.length === 0 || worlds.length === 50) continue;
        const teams = distinctTeams(worlds, candidate);
        if (teams.length !== 1 || !(await everyWorldHasLyingEvilGoon(candidate))) continue;
        const team = teams[0] as EvilTeam;
        if (!(await hasUniqueAnswer(candidate, team))) continue;
        const necessaryClaims = (await claimNecessity(candidate, team)).filter((result) => result.necessary).length;
        let necessaryDetails = 0;
        for (const simplification of claimSimplifications(candidate)) {
          if (simplification.label === "You.possibleActualRoles") continue;
          if (!(await hasUniqueAnswer(simplification.doc, team))) necessaryDetails += 1;
        }
        candidates.push({ doc: candidate, worlds: worlds.length, team, necessaryClaims, necessaryDetails });
        console.log(
          `${deaths.join(",")}; ${expression}: ${necessaryClaims}/9 claims, ${necessaryDetails} details, ${worlds.length} worlds; Demon ${team.demon}; Minions ${team.minions.join(", ")}`,
        );
      }
    }
  }
  candidates.sort(
    (left, right) =>
      right.necessaryClaims - left.necessaryClaims ||
      right.necessaryDetails - left.necessaryDetails ||
      left.worlds - right.worlds,
  );
  const best = candidates[0];
  if (best === undefined) throw new Error("No death-pattern candidate kept a unique team and hidden evil Goon.");
  console.log(`\nBest candidate\n${JSON.stringify(best.doc, null, 2)}`);
}

async function searchChronology(source: PuzzleDoc): Promise<void> {
  const candidate: PuzzleDoc = {
    ...source,
    timeline: (source.timeline ?? []).map((event) => {
      if (event.timing === "day_1" && event.type === "execution") return { ...event, players: ["Finn"] };
      if (event.timing === "day_2" && event.type === "execution") return { ...event, players: ["Drew"] };
      return event;
    }),
  };
  await searchActions(candidate);
}

async function searchActions(source: PuzzleDoc): Promise<void> {
  if (!hasExplicitOutsiderClaim(source)) throw new Error("Action search requires an explicit Outsider claim.");
  const expected: EvilTeam = { demon: "Hugo", minions: ["Ada"] };
  let seed = numericArg("--seed", 84);
  const random = <T>(values: readonly T[]): T => {
    seed = (seed * 1664525 + 1013904223) >>> 0;
    return values[seed % values.length] as T;
  };
  const randomPair = (values: readonly string[]): readonly [string, string] => {
    const left = random(values);
    return [left, random(values.filter((value) => value !== left))];
  };
  let bestScore = -1;
  let best: PuzzleDoc | undefined;
  const attempts = numericArg("--attempts", 500);
  const fixedNightOneCheck = source.claims
    .find((claim): claim is Extract<Claim, { type: "Chambermaid" }> => claim.type === "Chambermaid")
    ?.checks?.find((check) => check.timing === "night_1");
  if (fixedNightOneCheck?.left !== "Drew" || fixedNightOneCheck.right !== "Hugo" || fixedNightOneCheck.count !== 2)
    throw new Error("Action search preserves the required night-1 Drew/Hugo Chambermaid 2.");
  const hypothesizedWakers = new Map<string, ReadonlySet<string>>([
    ["night_2", new Set(["Cora", "Drew", "Eve", "Iris"])],
    ["night_3", new Set(["Cora", "Eve", "Iris"])],
    ["night_4", new Set(["Cora"])],
  ]);

  for (let attempt = 1; attempt <= attempts; attempt += 1) {
    const laterChecks = ["night_2", "night_3", "night_4"].map((timing) => {
      const [left, right] = randomPair([...livingAt(source, timing)].filter((player) => player !== "You"));
      const wakers = hypothesizedWakers.get(timing) as ReadonlySet<string>;
      return { timing: timing as Timing, left, right, count: Number(wakers.has(left)) + Number(wakers.has(right)) };
    });
    const sailorChoices = ["night_1", "night_2", "night_3", "night_4"].map((timing) => ({
      timing: timing as Timing,
      player: random([...livingAt(source, timing)].filter((player) => player !== "Ada")),
    }));
    const candidate: PuzzleDoc = {
      ...source,
      claims: source.claims.map((claim): Claim => {
        if (claim.type === "Sailor") return { ...claim, choices: sailorChoices };
        if (claim.type === "Chambermaid")
          return {
            ...claim,
            checks: [fixedNightOneCheck, ...laterChecks],
          };
        return claim;
      }),
    };
    const worlds = await solve(candidate, 40);
    if (
      worlds.length === 0 ||
      worlds.length === 40 ||
      !worlds.every((world) => sameTeam(evilTeam(world, candidate), expected))
    )
      continue;
    if (!(await everyWorldHasLyingEvilGoon(candidate))) continue;
    const necessaryClaims = (await claimNecessity(candidate, expected)).filter((result) => result.necessary).length;
    let necessaryDetails = 0;
    const simplifications = claimSimplifications(candidate).filter(
      (entry) => entry.label !== "You.possibleActualRoles",
    );
    for (const simplification of simplifications)
      if (!(await hasUniqueAnswer(simplification.doc, expected))) necessaryDetails += 1;
    const score = necessaryClaims * 100 + necessaryDetails;
    if (score <= bestScore) continue;
    bestScore = score;
    best = candidate;
    console.log(
      `Attempt ${attempt}: ${necessaryClaims}/9 claims and ${necessaryDetails}/${simplifications.length} details affect the team answer (${worlds.length} worlds).`,
    );
    if (necessaryClaims === 9 && necessaryDetails === simplifications.length) break;
  }
  if (best === undefined) throw new Error("No action candidate preserved the intended team.");
  console.log(JSON.stringify(best, null, 2));
}

function numericArg(name: string, fallback: number): number {
  const value = process.argv.find((argument) => argument.startsWith(`${name}=`))?.slice(name.length + 1);
  const parsed = Number(value);
  return Number.isInteger(parsed) && parsed > 0 ? parsed : fallback;
}

function sameTeam(left: EvilTeam, right: EvilTeam): boolean {
  return left.demon === right.demon && left.minions.join("\0") === right.minions.join("\0");
}

function hasExplicitOutsiderClaim(doc: PuzzleDoc): boolean {
  return doc.claims.some((claim) => roleCharacterType(roleByName(claim.type)) === CharacterType.Outsider);
}

function groupTeams(
  worlds: readonly World[],
  doc: PuzzleDoc,
): ReadonlyMap<string, { readonly team: EvilTeam; count: number }> {
  const teams = new Map<string, { readonly team: EvilTeam; count: number }>();
  for (const world of worlds) {
    const team = evilTeam(world, doc);
    const key = `${team.demon}|${team.minions.join("|")}`;
    const entry = teams.get(key);
    if (entry === undefined) teams.set(key, { team, count: 1 });
    else teams.set(key, { team, count: entry.count + 1 });
  }
  return teams;
}

function distinctTeams(worlds: readonly World[], doc: PuzzleDoc): readonly EvilTeam[] {
  return [...groupTeams(worlds, doc).values()].map((entry) => entry.team);
}

async function printSolutionsJson(doc: PuzzleDoc): Promise<void> {
  const worlds = await solve(doc);
  const solutions = worlds
    .map((world) => {
      const roles = Object.fromEntries([...doc.players].sort().map((player) => [player, world.actualRole(player)]));
      const poisoned = serializeTimedPlayers(world.poisonedByTiming);
      const drunkByTiming = serializeTimedPlayers(world.drunkByTiming);
      const drunk = [...world.drunk].sort();
      return {
        roles,
        ...(Object.keys(poisoned).length > 0 ? { poisoned } : {}),
        ...(drunk.length > 0 ? { drunk } : {}),
        ...(Object.keys(drunkByTiming).length > 0 ? { drunkByTiming } : {}),
      };
    })
    .sort((left, right) => JSON.stringify(left).localeCompare(JSON.stringify(right)));
  console.log(JSON.stringify({ solutions }, null, 2));
}

function serializeTimedPlayers(values: ReadonlyMap<string, ReadonlySet<string>>): Record<string, readonly string[]> {
  return Object.fromEntries(
    [...values.entries()]
      .filter(([, players]) => players.size > 0)
      .sort(([left], [right]) => timingSortValue(left) - timingSortValue(right) || left.localeCompare(right))
      .map(([timing, players]) => [timing, [...players].sort()]),
  );
}

async function searchGossip(source: PuzzleDoc): Promise<void> {
  const expressions = [
    "Ada.alignment == Evil",
    "Ada.type != Outsider",
    "some Po.~role",
    "some Pukka.~role",
    "some (Po + Pukka).~role",
    "Iris.role != Shabaloth",
    "Drew.type != Minion",
    "Hugo.type != Minion",
    "Ada.type != Outsider or some Po.~role",
    "Ada.type != Outsider or some Pukka.~role",
    "Iris.role != Shabaloth or Drew.type != Minion",
    "Iris.role != Shabaloth or Hugo.type != Minion",
    "Drew.type != Minion or Hugo.type != Minion",
    "some Po.~role or Drew.type != Minion",
    "some Po.~role or Hugo.type != Minion",
    "some Pukka.~role or Drew.type != Minion",
    "some Pukka.~role or Hugo.type != Minion",
  ];
  const expected: PuzzleAnswer = { demon: "Hugo", minions: ["Ada"] };
  for (const expression of expressions) {
    const candidate: PuzzleDoc = {
      ...source,
      claims: source.claims.map((claim): Claim =>
        claim.type === "Gossip"
          ? { ...claim, statements: [{ timing: claim.statements?.[0]?.timing ?? "day_1", expression }] }
          : claim,
      ),
    };
    if (!(await hasUniqueAnswer(candidate, expected))) {
      console.log(`${expression}: not unique`);
      continue;
    }
    const necessity = await claimNecessity(candidate, expected);
    const redundantClaims = necessity.filter((result) => !result.necessary).map((result) => result.name);
    const redundantDetails = [];
    for (const simplification of claimSimplifications(candidate)) {
      if (simplification.label === "You.possibleActualRoles") continue;
      if (await hasUniqueAnswer(simplification.doc, expected)) redundantDetails.push(simplification.label);
    }
    console.log(
      `${expression}: unique; evil Goon=${await everyWorldHasEvilGoon(candidate)}; redundant claims=${redundantClaims.join(",") || "none"}; redundant details=${redundantDetails.join(",") || "none"}`,
    );
  }
}

async function diagnose(source: PuzzleDoc): Promise<void> {
  const candidate = source;
  const worlds = await solve(candidate, 200);
  const teams = groupTeams(worlds, candidate);
  console.log(`Sampled ${worlds.length}${worlds.length === 200 ? "+" : ""} worlds across ${teams.size} evil teams:`);
  for (const { team, count } of teams.values()) {
    console.log(
      `  Demon ${team.demon}; Minions ${team.minions.join(", ")} (${count}${worlds.length === 200 ? "+/sample" : ""} worlds)`,
    );
  }
  if (worlds.length > 0 && teams.size === 1) {
    const world = worlds[0] as World;
    const answer = puzzleAnswer(world, candidate);
    const goon = world.holder("Goon");
    console.log(`Forced evil Goon: ${goon !== undefined && (await hasForcedEvilGoon(candidate, goon))}`);
    console.log(`Every world has an evil Goon: ${await everyWorldHasEvilGoon(candidate)}`);
    const necessity = await claimNecessity(candidate, answer);
    console.log(
      `Whole-claim necessity: ${necessity.map((result) => `${result.name}=${result.necessary ? "needed" : "redundant"}`).join(", ")}`,
    );
    const replacementNecessity = [];
    for (const claim of candidate.claims) {
      const changed = {
        ...candidate,
        claims: candidate.claims.map((entry): Claim =>
          entry === claim ? { type: "Minstrel", name: claim.name } : entry,
        ),
      };
      replacementNecessity.push({ name: claim.name, needed: !(await hasUniqueAnswer(changed, answer)) });
    }
    console.log(
      `Minstrel-perturbation necessity: ${replacementNecessity.map((result) => `${result.name}=${result.needed ? "changes" : "same"}`).join(", ")}`,
    );
    const simplifications = claimSimplifications(candidate);
    const redundantDetails = [];
    for (const simplification of simplifications) {
      if (await hasUniqueAnswer(simplification.doc, answer)) redundantDetails.push(simplification.label);
    }
    console.log(
      `Individual claim details: ${redundantDetails.length === 0 ? "all needed" : `redundant ${redundantDetails.join(", ")}`}`,
    );
  }
  console.log("\nWorld details");
  worlds.forEach((world, index) => {
    console.log(`World ${index + 1}:`);
    printWorld(candidate, world);
    for (const timing of ["night_2", "night_3", "night_4"] as const) {
      const poisoned = candidate.players.filter((player) => world.isPoisoned(player, timing));
      const drunk = candidate.players.filter((player) => world.isDrunk(player, timing));
      if (poisoned.length > 0 || drunk.length > 0)
        console.log(`  ${timing}: poisoned ${poisoned.join(", ") || "none"}; drunk ${drunk.join(", ") || "none"}`);
    }
  });
  console.log("\nCandidate");
  console.log(JSON.stringify(candidate, null, 2));
}

async function everyWorldHasEvilGoon(doc: PuzzleDoc): Promise<boolean> {
  const noGoon = buildFromDoc(doc, backend);
  for (const player of doc.players) noGoon.addFalse(noGoon.actualIs(player, "Goon"));
  if ((await noGoon.solveAll({ limit: 1 })).length > 0) return false;

  const goodGoon = buildFromDoc(doc, backend);
  goodGoon.addTruth(
    goodGoon.anyOf(
      doc.players.map((player) =>
        goodGoon.allOf(
          [
            goodGoon.actualIs(player, "Goon"),
            goodGoon.not(goodGoon.isEvilAt(player, "night_4" as Timing), `${player}_good_at_puzzle_time`),
          ],
          `${player}_is_good_goon`,
        ),
      ),
      "some_good_goon_at_puzzle_time",
    ),
  );
  return (await goodGoon.solveAll({ limit: 1 })).length === 0;
}

async function everyWorldHasLyingEvilGoon(doc: PuzzleDoc): Promise<boolean> {
  if (!(await everyWorldHasEvilGoon(doc))) return false;
  const eligibleClaimants = new Set(
    doc.claims.filter((claim) => claim.type !== "Goon" && claimIncludesAction(claim)).map((claim) => claim.name),
  );
  if (eligibleClaimants.size === 0) return false;
  const ineligibleGoon = buildFromDoc(doc, backend);
  ineligibleGoon.addTruth(
    ineligibleGoon.anyOf(
      doc.players
        .filter((player) => !eligibleClaimants.has(player))
        .map((player) => ineligibleGoon.actualIs(player, "Goon")),
      "an_ineligible_player_is_the_goon",
    ),
  );
  return (await ineligibleGoon.solveAll({ limit: 1 })).length === 0;
}

function claimSimplifications(doc: PuzzleDoc): readonly { readonly label: string; readonly doc: PuzzleDoc }[] {
  const variants: Array<{ readonly label: string; readonly doc: PuzzleDoc }> = [];
  const add = (claim: Claim, label: string, replacement: Claim): void => {
    variants.push({
      label: `${claim.name}.${label}`,
      doc: { ...doc, claims: doc.claims.map((entry) => (entry === claim ? replacement : entry)) },
    });
  };
  for (const claim of doc.claims) {
    if (claim.possibleActualRoles !== undefined)
      add(claim, "possibleActualRoles", { ...claim, possibleActualRoles: undefined });
    switch (claim.type) {
      case "Grandmother":
        if (claim.grandchild !== undefined) add(claim, "grandchild", { ...claim, grandchild: undefined });
        if (claim.role !== undefined) add(claim, "role", { ...claim, role: undefined });
        break;
      case "Chambermaid":
        for (const [index] of (claim.checks ?? []).entries())
          add(claim, `checks[${index}]`, {
            ...claim,
            checks: claim.checks?.filter((_, checkIndex) => checkIndex !== index),
          });
        break;
      case "Gambler":
        for (const [index] of (claim.guesses ?? []).entries())
          add(claim, `guesses[${index}]`, {
            ...claim,
            guesses: claim.guesses?.filter((_, guessIndex) => guessIndex !== index),
          });
        break;
      case "Exorcist":
        for (const [index] of (claim.choices ?? []).entries())
          add(claim, `choices[${index}]`, {
            ...claim,
            choices: claim.choices?.filter((_, choiceIndex) => choiceIndex !== index),
          });
        break;
      case "Gossip":
        for (const [index] of (claim.statements ?? []).entries())
          add(claim, `statements[${index}]`, {
            ...claim,
            statements: claim.statements?.filter((_, statementIndex) => statementIndex !== index),
          });
        break;
      case "Sailor":
        for (const [index] of (claim.choices ?? []).entries())
          add(claim, `choices[${index}]`, {
            ...claim,
            choices: claim.choices?.filter((_, choiceIndex) => choiceIndex !== index),
          });
        break;
      case "Professor":
        if (claim.target !== undefined) add(claim, "target", { ...claim, target: undefined });
        break;
      case "Seamstress":
        if (claim.aligned !== undefined) add(claim, "aligned", { ...claim, aligned: undefined });
        break;
      case "Washerwoman":
        if (claim.role !== undefined) add(claim, "role", { ...claim, role: undefined });
        break;
    }
  }
  return variants;
}

async function verify(doc: PuzzleDoc): Promise<void> {
  assertRequestedShape(doc);
  const worlds = await solve(doc);
  if (worlds.length === 0) throw new Error("Expected at least one solution.");
  const world = worlds[0] as World;
  const answer = puzzleAnswer(world, doc);
  if (!(await hasUniqueAnswer(doc, answer))) throw new Error("The Demon and Minion players are not unique.");
  if (!(await everyWorldHasLyingEvilGoon(doc)))
    throw new Error("Some satisfying world lacks an evil Goon who lies about a role and action.");
  for (const candidate of worlds) {
    if (candidate.holder("Godfather") === undefined) throw new Error("A satisfying world lacks the Godfather.");
    if (candidate.holder("Gambler") === undefined) throw new Error("A satisfying world lacks the Gambler.");
    if (!demonClaimIsUnique(doc, candidate)) throw new Error("The Demon double-claims another player's claimed role.");
    const goon = candidate.holder("Goon");
    const goonClaim = doc.claims.find((claim) => claim.name === goon);
    if (goon === undefined || goonClaim === undefined || !claimIncludesAction(goonClaim))
      throw new Error("Every hidden Goon must lie about a role and an action.");
  }

  const necessity = await claimNecessity(doc, answer);
  const redundant = necessity.filter((result) => !result.necessary);

  const stablePerturbations: string[] = [];
  for (const claim of doc.claims) {
    const changed = {
      ...doc,
      claims: doc.claims.map((entry): Claim => (entry === claim ? perturbClaim(claim) : entry)),
    };
    if (await hasUniqueAnswer(changed, answer)) stablePerturbations.push(claim.name);
  }

  const redundantDetails = [];
  for (const simplification of claimSimplifications(doc)) {
    if (simplification.label === "You.possibleActualRoles") continue;
    if (await hasUniqueAnswer(simplification.doc, answer)) redundantDetails.push(simplification.label);
  }
  worlds.forEach((candidate, index) => {
    console.log(`World ${index + 1}:`);
    printWorld(doc, candidate);
  });
  console.log(
    `\nVerified: ${answer.demon} is the forced Demon; ${answer.minions.join(" and ")} are the forced Minions; all ${worlds.length} internal worlds contain a lying evil Goon, the Godfather, and the fatal night-3 Gambler. Whole claims removable without changing the team: ${redundant.map((result) => result.name).join(", ") || "none"}. Simple role perturbations that preserve the team: ${stablePerturbations.join(", ") || "none"}. Redundant mandated action details: ${redundantDetails.join(", ") || "none"}.`,
  );
}

function perturbClaim(claim: Claim): Claim {
  return new Set(["Gossip", "Minstrel"]).has(claim.type)
    ? { type: "Grandmother", name: claim.name }
    : { type: "Minstrel", name: claim.name };
}

function claimIncludesAction(claim: Claim): boolean {
  switch (claim.type) {
    case "Chambermaid":
      return (claim.checks?.length ?? 0) > 0;
    case "Exorcist":
      return (claim.choices?.length ?? 0) > 0;
    case "Gambler":
      return (claim.guesses?.length ?? 0) > 0;
    case "Gossip":
      return (claim.statements?.length ?? 0) > 0;
    case "Moonchild":
      return claim.chosen !== undefined;
    case "Professor":
      return claim.target !== undefined;
    case "Sailor":
      return (claim.choices?.length ?? 0) > 0;
    default:
      return false;
  }
}

function assertRequestedShape(doc: PuzzleDoc): void {
  if (doc.players.length !== 9) throw new Error("Expected 9 players.");
  if (doc.setup !== "standard") throw new Error("Expected standard setup.");
  if ((doc.constraints?.length ?? 0) !== 0) throw new Error("Expected no custom constraints.");
  if (doc.uniqueCharacters !== true) throw new Error("Expected unique characters.");
  if (doc.claims.length !== 9) throw new Error("Expected exactly nine claimed characters.");
  if (doc.claims.some((claim) => claim.type === "Pacifist")) throw new Error("Expected no Pacifist claim.");
  if (!hasExplicitOutsiderClaim(doc))
    throw new Error("Expected at least one explicit Outsider claim; all-Townsfolk rosters are excluded.");
  if (
    !doc.claims.some(
      (claim) =>
        claim.name === "You" && claim.type === "Chambermaid" && claim.possibleActualRoles?.join("\0") === "Chambermaid",
    )
  )
    throw new Error('Expected "You" to remain locked as the Chambermaid.');
  for (const role of ["Seamstress", "Washerwoman"])
    if (doc.script.includes(role) || doc.claims.some((claim) => claim.type === role))
      throw new Error(`${role} is not a Bad Moon Rising character.`);
  if (!doc.claims.some((claim) => claim.type === "Minstrel")) throw new Error("Expected someone to claim Minstrel.");
  const timeline = doc.timeline ?? [];
  const firstExecuted = timeline.find((event) => event.type === "execution")?.players[0];
  if (doc.claims.some((claim) => claim.name === firstExecuted && claim.type === "Minstrel"))
    throw new Error("The Minstrel claimant must not be the first player executed.");
  for (const day of ["day_1", "day_2", "day_3"]) {
    if (
      !timeline.some(
        (event) =>
          event.timing === day &&
          (event.type === "execution" || event.type === "survivedExecution") &&
          event.players.length === 1,
      )
    )
      throw new Error(`Expected one execution on ${day}.`);
  }
  const expectedNightDeaths = new Map<string, number>([
    ["night_2", 0],
    ["night_3", 3],
    ["night_4", 0],
  ]);
  for (const [timing, count] of expectedNightDeaths) {
    if (
      !timeline.some(
        (event) => event.timing === timing && event.type === "nightDeath" && event.players.length === count,
      )
    )
      throw new Error(`Expected ${count} deaths on ${timing}.`);
  }
  const expectedActionNights = new Map<string, readonly string[]>([
    ["Sailor", ["night_1", "night_2", "night_3", "night_4"]],
    ["Exorcist", ["night_2", "night_3", "night_4"]],
    ["Chambermaid", ["night_1", "night_2", "night_3", "night_4"]],
  ]);
  for (const [type, expectedTimings] of expectedActionNights) {
    const claim = doc.claims.find((entry) => entry.type === type);
    const timings =
      claim?.type === "Chambermaid"
        ? (claim.checks ?? []).map((check) => check.timing)
        : claim?.type === "Sailor" || claim?.type === "Exorcist"
          ? (claim.choices ?? []).map((choice) => choice.timing)
          : [];
    if (timings.join("\0") !== expectedTimings.join("\0"))
      throw new Error(`Expected ${type} to act on ${expectedTimings.join(", ")}.`);
    if (claim?.type === "Sailor" || claim?.type === "Exorcist")
      for (const choice of claim.choices ?? [])
        if (!livingAt(doc, choice.timing).has(choice.player))
          throw new Error(`${type} must choose a living player on ${choice.timing}.`);
  }
  const chambermaid = doc.claims.find(
    (claim): claim is Extract<Claim, { type: "Chambermaid" }> => claim.type === "Chambermaid",
  );
  for (const check of chambermaid?.checks ?? []) {
    const alive = livingAt(doc, check.timing);
    if (
      check.left === check.right ||
      check.left === chambermaid?.name ||
      !alive.has(check.left) ||
      !alive.has(check.right)
    )
      throw new Error(`Chambermaid must choose two other alive players on ${check.timing}.`);
  }
  if (livingAt(doc, "day_4").size !== 4) throw new Error("Expected four living players at puzzle time.");
  const gambler = doc.claims.find((claim) => claim.type === "Gambler");
  const nightThreeDeaths = new Set(
    (doc.timeline ?? [])
      .filter((event) => event.type === "nightDeath" && event.timing === "night_3")
      .flatMap((event) => event.players),
  );
  if (
    gambler?.guesses?.some(
      (guess) =>
        guess.timing === "night_3" &&
        doc.claims.some((claim) => claim.name === guess.player && claim.type === guess.role),
    ) !== true ||
    !nightThreeDeaths.has(gambler.name)
  ) {
    throw new Error("Expected the night-3 Gambler to guess a player's claimed role and die that night.");
  }
}

function livingAt(doc: PuzzleDoc, timing: string | undefined): ReadonlySet<string> {
  if (timing === undefined) return new Set();
  const order = timingSortValue(timing);
  const dead = new Set(
    (doc.timeline ?? [])
      .filter((event) => event.type !== "survivedExecution" && timingSortValue(event.timing) < order)
      .flatMap((event) => event.players),
  );
  return new Set(doc.players.filter((player) => !dead.has(player)));
}

function timingSortValue(timing: string): number {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) return Number.MAX_SAFE_INTEGER;
  return Number(match[2]) * 2 + (match[1] === "day" ? 1 : 0);
}

async function solve(doc: PuzzleDoc, limit?: number): Promise<readonly World[]> {
  return buildFromDoc(doc, backend).solveAll(limit === undefined ? {} : { limit });
}

async function hasForcedEvilGoon(doc: PuzzleDoc, player: string): Promise<boolean> {
  const notGoon = buildFromDoc(doc, backend);
  notGoon.addFalse(notGoon.actualIs(player, "Goon"));
  if ((await notGoon.solveAll({ limit: 1 })).length > 0) return false;

  const notEvil = buildFromDoc(doc, backend);
  notEvil.addFalse(notEvil.isEvilAt(player, "night_4" as Timing));
  return (await notEvil.solveAll({ limit: 1 })).length === 0;
}

function demonClaimIsUnique(doc: PuzzleDoc, world: World): boolean {
  const demon = doc.players.find(
    (player) => roleCharacterType(roleByName(world.actualRole(player))) === CharacterType.Demon,
  );
  if (demon === undefined) return false;
  const demonClaim = doc.claims.find((claim) => claim.name === demon)?.type;
  if (demonClaim === undefined) return false;
  return doc.claims.every((claim) => claim.name === demon || claim.type !== demonClaim);
}

async function claimNecessity(
  doc: PuzzleDoc,
  solution: PuzzleAnswer,
): Promise<readonly { readonly name: string; readonly necessary: boolean }[]> {
  const results: Array<{ readonly name: string; readonly necessary: boolean }> = [];
  for (const removed of doc.claims) {
    const changed = { ...doc, claims: doc.claims.filter((claim) => claim !== removed) };
    results.push({
      name: removed.name,
      necessary: !(await hasUniqueAnswer(changed, solution)),
    });
  }
  return results;
}

interface EvilTeam {
  readonly demon: string;
  readonly minions: readonly string[];
}

type PuzzleAnswer = EvilTeam;

function evilTeam(world: World, doc: PuzzleDoc): EvilTeam {
  const demons = doc.players.filter(
    (player) => roleCharacterType(roleByName(world.actualRole(player))) === CharacterType.Demon,
  );
  const minions = doc.players
    .filter((player) => roleCharacterType(roleByName(world.actualRole(player))) === CharacterType.Minion)
    .sort();
  if (demons.length !== 1) throw new Error(`Expected one Demon, found ${demons.length}.`);
  return { demon: demons[0] as string, minions };
}

function puzzleAnswer(world: World, doc: PuzzleDoc): PuzzleAnswer {
  return evilTeam(world, doc);
}

async function hasUniqueAnswer(doc: PuzzleDoc, expected: PuzzleAnswer): Promise<boolean> {
  return hasUniqueEvilTeam(doc, expected);
}

async function hasUniqueEvilTeam(doc: PuzzleDoc, expected: EvilTeam): Promise<boolean> {
  const first = await solve(doc, 1);
  if (first.length === 0) return false;
  const firstTeam = evilTeam(first[0] as World, doc);
  if (firstTeam.demon !== expected.demon || firstTeam.minions.join("\0") !== expected.minions.join("\0")) return false;

  for (const player of doc.players) {
    if (player !== expected.demon) {
      const otherDemon = buildFromDoc(doc, backend);
      otherDemon.addTruth(otherDemon.isDemon(player));
      if ((await otherDemon.solveAll({ limit: 1 })).length > 0) return false;
    }

    const changesMinionMembership = buildFromDoc(doc, backend);
    if (expected.minions.includes(player)) changesMinionMembership.addFalse(changesMinionMembership.isMinion(player));
    else changesMinionMembership.addTruth(changesMinionMembership.isMinion(player));
    if ((await changesMinionMembership.solveAll({ limit: 1 })).length > 0) return false;
  }
  return true;
}

function printWorld(doc: PuzzleDoc, world: World): void {
  for (const player of doc.players)
    console.log(
      `${player}: ${world.actualRole(player)} (claims ${doc.claims.find((claim) => claim.name === player)?.type ?? "nothing"})`,
    );
}
