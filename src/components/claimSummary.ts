import type { Claim } from "../schema/puzzleDoc";

export function claimSummary(claim: Claim): string {
  const customInfo = (claim.info ?? [])
    .map((info) => info.expression?.trim())
    .filter((text): text is string => Boolean(text));
  if (customInfo.length > 0) return customInfo.join("; ");

  switch (claim.type) {
    case "Acrobat":
      return acrobatSummary(claim);
    case "Chef":
      return `${claim.count} adjacent evil pair${claim.count === 1 ? "" : "s"}`;
    case "Chambermaid":
      return chambermaidSummary(claim);
    case "Empath":
      return empathSummary(claim);
    case "Investigator": {
      const role = claim.role ?? claim.minionRole ?? "a Minion";
      const subject =
        claim.among.length === 2 ? `Either ${claim.among[0]} or ${claim.among[1]}` : formatList(claim.among);
      return `${subject} is ${rolePhrase(role, "a Minion")}.`;
    }
    case "Librarian":
      return claim.outsiderCount !== undefined
        ? `${claim.outsiderCount} Outsider${claim.outsiderCount === 1 ? "" : "s"}`
        : `${formatList(claim.among ?? [])} could be ${claim.role || "an Outsider"}`;
    case "Washerwoman":
      return `${formatList(claim.among)} could be ${claim.role || "a Townsfolk"}`;
    case "FortuneTeller":
      return fortuneTellerSummary(claim);
    case "Undertaker":
      return `${claim.player || "Executed player"} was ${claim.role || "unknown"}`;
    case "Noble":
      return `${formatList(claim.oneEvilAmong ?? claim.among ?? [])}: ${claim.evilCount ?? 1} evil`;
    case "Steward":
      return `${claim.goodPlayer || "Someone"} is good`;
    case "Knight":
      return knightSummary(claim.noDemonAmong);
    case "Gambler":
      return gamblerSummary(claim);
    case "Seamstress":
      return `${formatPair(claim.among)} are ${claim.aligned ? "same" : "different"}`;
    case "Juggler":
      return jugglerSummary(claim);
    case "Dreamer":
      return `${claim.player || "Player"} is ${formatList(claim.roles)}`;
    case "Shugenja":
      return `Evil is ${claim.evilDirection}`;
    case "Clockmaker":
      return claim.distance === undefined
        ? "No Clockmaker number"
        : `Demon ${claim.distance} step${claim.distance === 1 ? "" : "s"} from Minion`;
    case "Gossip":
      return gossipSummary(claim);
    case "Courtier":
      return courtierSummary(claim);
    case "Legionary":
      return legionarySummary(claim);
    case "Mathematician":
      return (claim.malfunctions ?? []).length === 0
        ? "No malfunction counts"
        : (claim.malfunctions ?? [])
            .map((entry) => `${entry.count} malfunction${entry.count === 1 ? "" : "s"} (${timingLabel(entry.timing)})`)
            .join("; ");
    case "Oracle":
      return oracleSummary(claim);
    case "Philosopher":
      return claim.role === undefined ? "No Philosopher choice" : `Chose ${claim.role}.`;
    case "Ravenkeeper":
      return claim.player === undefined
        ? "No Ravenkeeper pick yet"
        : `${claim.player} is ${rolePhrase(claim.role, "unknown")}.`;
    case "Sage":
      return `${formatList(claim.demonAmong ?? [])} is Demon`;
    case "Slayer": {
      const target = claim.target ?? "someone";
      const timing = claim.timing === undefined ? "that day" : sentenceTimingLabel(claim.timing);
      if (claim.killed === true) return `I shot ${target} on ${timing} and they died.`;
      if (claim.killed === false) return `I shot ${target} on ${timing} and nothing happened.`;
      return `I shot ${target} on ${timing}.`;
    }
    case "Snake Charmer":
      return claim.checked ? `${claim.checked} is ${claim.demon ? "" : "not "}Demon` : "No check yet";
    case "VillageIdiot": {
      if (claim.checks.length === 0) return "No checks yet";
      const showTimings = claim.checks.some((check) => check.timing !== undefined);
      const checks = claim.checks
        .map((check) => {
          const timing = showTimings && check.timing !== undefined ? `${compactTimingLabel(check.timing)} ` : "";
          return `${timing}${check.player} -> ${check.good ? "good" : "evil"}`;
        })
        .join(", ");
      return `I checked: ${checks}.`;
    }
    case "Klutz": {
      if (claim.chosen === undefined) return "No Klutz choice";
      if (claim.lost === true) return `Chose ${claim.chosen} and lost.`;
      if (claim.lost === false) return `Chose ${claim.chosen} and did not lose.`;
      return `Chose ${claim.chosen}.`;
    }
    case "Balloonist":
      return balloonistSummary(claim);
    case "Savant":
      return savantSummary(claim.statements[0]?.options ?? []);
    case "Virgin": {
      const nominator = claim.nominator ?? "Someone";
      const timing = claim.timing === undefined ? "that day" : sentenceTimingLabel(claim.timing);
      if (claim.executed === true) return `${nominator} nominated me on ${timing} and was executed.`;
      if (claim.executed === false) return `${nominator} nominated me on ${timing} and nothing happened.`;
      return `${nominator} nominated me on ${timing}.`;
    }
    case "Nightwatchman":
      return nightwatchmanSummary(claim);
    default:
      return `I am the ${claim.type}`;
  }
}

function acrobatSummary(claim: Extract<Claim, { readonly type: "Acrobat" }>): string {
  const choices = (claim.choices ?? [])
    .filter((choice) => choice.player.trim() !== "")
    .map((choice, index) => {
      const timing = choice.timing === undefined ? defaultNightLabel(index) : compactTimingLabel(choice.timing);
      return `${timing}: chose ${choice.player}, ${choice.died ? "died" : "survived"}`;
    });
  return choices.length === 0 ? "No Acrobat choices" : choices.join("; ");
}

function chambermaidSummary(claim: Extract<Claim, { readonly type: "Chambermaid" }>): string {
  const checks = (claim.checks ?? [])
    .filter((check) => check.left.trim() !== "" && check.right.trim() !== "")
    .map((check, index) => {
      const timing = check.timing === undefined ? defaultNightLabel(index) : compactTimingLabel(check.timing);
      return `${timing}: ${check.left} + ${check.right}, ${check.count} woke`;
    });
  return checks.length === 0 ? "No Chambermaid checks" : checks.join("; ");
}

function empathSummary(claim: Extract<Claim, { readonly type: "Empath" }>): string {
  const timing = claim.timing === undefined ? "" : `${compactTimingLabel(claim.timing)}: `;
  const count = claim.count === undefined ? "unknown" : String(claim.count);
  const evil = `${count} evil`;
  const neighbors = claim.neighbors?.filter(Boolean) ?? [];
  if (neighbors.length === 2) return `${timing}${neighbors[0]} + ${neighbors[1]} -> ${evil}`;

  const subject = claim.player ? `${claim.player}: ` : "";
  return `${timing}${subject}${evil} neighbor${claim.count === 1 ? "" : "s"}`;
}

function fortuneTellerSummary(claim: Extract<Claim, { readonly type: "FortuneTeller" }>): string {
  const checks = claim.checks
    .filter((check) => check.left.trim() !== "" && check.right.trim() !== "")
    .map((check, index) => {
      const timing = check.timing === undefined ? defaultNightLabel(index) : compactTimingLabel(check.timing);
      return `${timing}: ${check.left} + ${check.right} -> ${check.yes ? "yes" : "no"}`;
    });
  return checks.length === 0 ? "I checked nobody yet" : checks.join("; ");
}

function gamblerSummary(claim: Extract<Claim, { readonly type: "Gambler" }>): string {
  const guesses = (claim.guesses ?? [])
    .filter((guess) => guess.player.trim() !== "" && guess.role.trim() !== "")
    .map((guess, index) => {
      const timing = guess.timing === undefined ? defaultNightLabel(index) : compactTimingLabel(guess.timing);
      const outcome = guess.survived === undefined ? "" : `, ${guess.survived ? "survived" : "died"}`;
      return `${timing}: ${guess.player}=${guess.role}${outcome}`;
    });
  return guesses.length === 0 ? "No Gambler guesses" : guesses.join("; ");
}

function rolePhrase(role: string | undefined, fallback: string): string {
  const value = role?.trim() || fallback;
  return /^(a|an|the)\s/i.test(value) ? value : `the ${value}`;
}

function jugglerSummary(claim: Extract<Claim, { readonly type: "Juggler" }>): string {
  const guesses = Object.entries(claim.guesses)
    .filter(([player, role]) => player.trim() !== "" && role.trim() !== "")
    .map(([player, role]) => `${player}=${role}`);
  const correct = claim.correctCount === undefined ? "correct count unknown" : `${claim.correctCount} correct`;
  return `Day 1 guesses: ${guesses.length === 0 ? "none" : guesses.join("; ")}; ${correct}.`;
}

function balloonistSummary(claim: Extract<Claim, { readonly type: "Balloonist" }>): string {
  const pairs = claim.differentCharacterTypePairs
    .map(([left, right]) => [left.trim(), right.trim()] as const)
    .filter(([left, right]) => left !== "" && right !== "")
    .map(([left, right]) => `${left}/${right}`);

  return pairs.length === 0 ? "No Balloonist pairs yet" : `Different types: ${pairs.join("; ")}.`;
}

function gossipSummary(claim: Extract<Claim, { readonly type: "Gossip" }>): string {
  const statements = (claim.statements ?? [])
    .map((statement) => {
      const expression = statement.expression.trim();
      if (expression === "") return undefined;
      const timing = statement.timing === undefined ? "Gossip" : `${compactTimingLabel(statement.timing)} gossip`;
      return `${timing}: ${expression}`;
    })
    .filter((statement): statement is string => statement !== undefined);

  return statements.length === 0 ? "No Gossip statements" : statements.join("; ");
}

function courtierSummary(claim: Extract<Claim, { readonly type: "Courtier" }>): string {
  const role = claim.role?.trim() || "no role";
  const choiceTiming = claim.timing === undefined ? "" : ` on ${compactTimingLabel(claim.timing)}`;
  const drunkTimings = (claim.drunkTimings ?? []).map(compactTimingLabel);
  const drunkSummary = drunkTimings.length === 0 ? "" : `; drunk ${drunkTimings.join(", ")}`;
  return `Chose ${role}${choiceTiming}${drunkSummary}.`;
}

function legionarySummary(claim: Extract<Claim, { readonly type: "Legionary" }>): string {
  const counts = (claim.counts ?? []).map((entry, index) => {
    const timing = entry.timing === undefined ? defaultNightLabel(index) : compactTimingLabel(entry.timing);
    return `${timing}: ${entry.count} living evil`;
  });
  return counts.length === 0 ? "No Legionary counts" : counts.join("; ");
}

function oracleSummary(claim: Extract<Claim, { readonly type: "Oracle" }>): string {
  const count = claim.count === undefined ? "Unknown" : String(claim.count);
  const deadPlayers = claim.deadPlayers?.filter(Boolean) ?? [];
  const scope = deadPlayers.length === 0 ? "" : ` among ${formatList(deadPlayers)}`;
  return `${count} dead evil${scope}`;
}

function nightwatchmanSummary(claim: Extract<Claim, { readonly type: "Nightwatchman" }>): string {
  const chosen = claim.chosen?.trim();
  if (!chosen) return "No Nightwatchman choice";
  if (claim.learned === true) return `${chosen} learned Nightwatchman.`;
  if (claim.learned === false) return `${chosen} did not learn Nightwatchman.`;
  return `Chose ${chosen}.`;
}

function knightSummary(players: readonly string[]): string {
  const visible = players.filter(Boolean);
  if (visible.length === 0) return "No Knight picks yet";
  if (visible.length === 1) return `${visible[0]} is not the Demon.`;
  if (visible.length === 2) return `Neither ${visible[0]} nor ${visible[1]} is the Demon.`;
  return `None of ${formatList(visible)} are the Demon.`;
}

function savantSummary(options: readonly string[]): string {
  const expressions = options.map((option) => option.trim()).filter(Boolean);
  return expressions.length === 0
    ? "No Savant statements"
    : expressions.map((expression) => `(${expression})`).join(" != ");
}

export function formatList(values: readonly string[]): string {
  const visible = values.filter(Boolean);
  if (visible.length === 0) return "Someone";
  if (visible.length === 1) return visible[0] as string;
  if (visible.length === 2) return `${visible[0]} or ${visible[1]}`;
  return `${visible.slice(0, -1).join(", ")}, or ${visible[visible.length - 1]}`;
}

function formatPair(values: readonly string[]): string {
  const visible = values.filter(Boolean);
  if (visible.length === 2) return `${visible[0]} and ${visible[1]}`;
  return formatList(values);
}

export function timingLabel(timing: string): string {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) return timing;
  const [, period, number] = match;
  if (period === undefined || number === undefined) return timing;
  return `${period[0]?.toUpperCase()}${period.slice(1)} ${number}`;
}

function sentenceTimingLabel(timing: string): string {
  return timingLabel(timing).toLowerCase();
}

export function compactTimingLabel(timing: string): string {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) return timing;
  const [, period, number] = match;
  if (period === undefined || number === undefined) return timing;
  return `${period[0]?.toUpperCase()}${number}`;
}

function defaultNightLabel(index: number): string {
  return `N${index + 1}`;
}
