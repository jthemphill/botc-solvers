import type { Claim } from "../schema/puzzleDoc";

export function claimSummary(claim: Claim): string {
  const customInfo = (claim.info ?? [])
    .map((info) => info.expression?.trim())
    .filter((text): text is string => Boolean(text));
  if (customInfo.length > 0) return customInfo.join("; ");

  switch (claim.type) {
    case "Chef":
      return `${claim.count} adjacent evil pair${claim.count === 1 ? "" : "s"}`;
    case "Empath":
      return `${claim.player ? `${claim.player}: ` : ""}${claim.count} evil neighbor${claim.count === 1 ? "" : "s"}`;
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
    case "FortuneTeller": {
      const check = claim.checks[0];
      if (check === undefined) return "I checked nobody yet";
      return `${check.left} + ${check.right}: ${check.yes ? "yes" : "no"}`;
    }
    case "Undertaker":
      return `${claim.player || "Executed player"} was ${claim.role || "unknown"}`;
    case "Noble":
      return `${formatList(claim.oneEvilAmong ?? claim.among ?? [])}: ${claim.evilCount ?? 1} evil`;
    case "Steward":
      return `${claim.goodPlayer || "Someone"} is good`;
    case "Knight":
      return knightSummary(claim.noDemonAmong);
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
    case "Mathematician":
      return (claim.malfunctions ?? []).length === 0
        ? "No malfunction counts"
        : (claim.malfunctions ?? [])
            .map((entry) => `${entry.count} malfunction${entry.count === 1 ? "" : "s"} (${timingLabel(entry.timing)})`)
            .join("; ");
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
    default:
      return `I am the ${claim.type}`;
  }
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
