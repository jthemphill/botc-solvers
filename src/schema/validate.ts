import {
  type Claim,
  type PuzzleDoc,
  SUPPORTED_CLAIM_TYPES,
  TIMELINE_EVENT_TYPES,
  type TimelineEventDoc,
} from "./puzzleDoc";

export class ValidationError extends Error {
  constructor(
    message: string,
    readonly path: string,
  ) {
    super(`${message} at ${path}`);
  }
}

function isObject(v: unknown): v is Record<string, unknown> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

function expectString(v: unknown, path: string): string {
  if (typeof v !== "string") throw new ValidationError(`Expected string`, path);
  return v;
}

function expectStringArray(v: unknown, path: string): string[] {
  if (!Array.isArray(v)) throw new ValidationError(`Expected array of strings`, path);
  return v.map((el, i) => expectString(el, `${path}[${i}]`));
}

function expectArray(v: unknown, path: string): unknown[] {
  if (!Array.isArray(v)) throw new ValidationError(`Expected array`, path);
  return v;
}

function expectBool(v: unknown, path: string): boolean {
  if (typeof v !== "boolean") throw new ValidationError(`Expected boolean`, path);
  return v;
}

function expectNumber(v: unknown, path: string): number {
  if (typeof v !== "number" || !Number.isInteger(v)) throw new ValidationError(`Expected integer`, path);
  return v;
}

function rejectLegacyField(input: Record<string, unknown>, key: string, path: string): void {
  if (input[key] !== undefined) throw new ValidationError(`Unsupported legacy field '${key}'`, path);
}

export function validatePuzzleDoc(input: unknown): PuzzleDoc {
  if (!isObject(input)) throw new ValidationError(`Expected object`, "$");
  rejectLegacyField(input, "fixedRoles", "$.fixedRoles");
  rejectLegacyField(input, "forbiddenRoles", "$.forbiddenRoles");
  const players = expectStringArray(input["players"], "$.players");
  const script = expectStringArray(input["script"], "$.script");
  const claims = input["claims"];
  if (!Array.isArray(claims)) throw new ValidationError(`Expected array`, "$.claims");
  const validatedClaims = claims.map((c, i) => validateClaim(c, `$.claims[${i}]`));

  const setup = input["setup"];
  if (setup !== undefined && setup !== "standard" && setup !== "none" && setup !== "atheist")
    throw new ValidationError(`setup must be "standard", "none", or "atheist"`, "$.setup");

  const title = input["title"] === undefined ? undefined : expectString(input["title"], "$.title");
  const uniqueCharacters =
    input["uniqueCharacters"] === undefined ? undefined : expectBool(input["uniqueCharacters"], "$.uniqueCharacters");
  const constraints =
    input["constraints"] === undefined ? undefined : validateConstraints(input["constraints"], "$.constraints");
  const timeline = input["timeline"] === undefined ? undefined : validateTimeline(input["timeline"], "$.timeline");

  return {
    title,
    players,
    script,
    setup,
    uniqueCharacters,
    constraints,
    timeline,
    claims: validatedClaims,
  };
}

function validateConstraints(v: unknown, pathRoot: string): NonNullable<PuzzleDoc["constraints"]> {
  if (!Array.isArray(v)) throw new ValidationError(`Expected array`, pathRoot);
  return v.map((entry, i) => {
    const path = `${pathRoot}[${i}]`;
    if (!isObject(entry)) throw new ValidationError(`Expected object`, path);
    return {
      expression: expectString(entry["expression"], `${path}.expression`),
    };
  });
}

function validateTimeline(v: unknown, pathRoot: string): TimelineEventDoc[] {
  if (!Array.isArray(v)) throw new ValidationError(`Expected array`, pathRoot);
  const eventTypeList = TIMELINE_EVENT_TYPES.map((type) => `"${type}"`).join(", ");
  return v.map((entry, i) => {
    const path = `${pathRoot}[${i}]`;
    if (!isObject(entry)) throw new ValidationError(`Expected object`, path);
    const type = expectString(entry["type"], `${path}.type`);
    if (!(TIMELINE_EVENT_TYPES as readonly string[]).includes(type)) {
      throw new ValidationError(`Timeline event type must be ${eventTypeList}`, `${path}.type`);
    }
    return {
      timing: expectString(entry["timing"], `${path}.timing`),
      type: type as TimelineEventDoc["type"],
      players: expectStringArray(entry["players"], `${path}.players`),
      caller: entry["caller"] === undefined ? undefined : expectString(entry["caller"], `${path}.caller`),
      sourceActedBeforeDeath:
        entry["sourceActedBeforeDeath"] === undefined
          ? undefined
          : expectBool(entry["sourceActedBeforeDeath"], `${path}.sourceActedBeforeDeath`),
    };
  });
}

function validateClaim(input: unknown, path: string): Claim {
  if (!isObject(input)) throw new ValidationError(`Expected object`, path);
  rejectLegacyField(input, "extraPossibleActualRoles", `${path}.extraPossibleActualRoles`);
  const type = expectString(input["type"], `${path}.type`);
  if (!SUPPORTED_CLAIM_TYPES.has(type as Claim["type"]))
    throw new ValidationError(`Unsupported claim type '${type}'`, `${path}.type`);
  const name = expectString(input["name"], `${path}.name`);
  const timing = input["timing"] === undefined ? undefined : expectString(input["timing"], `${path}.timing`);
  const possibleActualRoles =
    input["possibleActualRoles"] === undefined
      ? undefined
      : expectStringArray(input["possibleActualRoles"], `${path}.possibleActualRoles`);
  const heardWidowCall =
    input["heardWidowCall"] === undefined ? undefined : expectBool(input["heardWidowCall"], `${path}.heardWidowCall`);
  const knownEvilTwin =
    input["knownEvilTwin"] === undefined ? undefined : expectString(input["knownEvilTwin"], `${path}.knownEvilTwin`);
  const info = input["info"] === undefined ? undefined : validateCustomInfo(input["info"], `${path}.info`, type);
  const base = { name, timing, possibleActualRoles, heardWidowCall, knownEvilTwin, info };

  switch (type as Claim["type"]) {
    case "Assassin":
      return {
        ...base,
        type: "Assassin",
        target: input["target"] === undefined ? undefined : expectString(input["target"], `${path}.target`),
      };
    case "Acrobat": {
      const choices = input["choices"];
      return {
        ...base,
        type: "Acrobat",
        choices:
          choices === undefined
            ? undefined
            : expectArray(choices, `${path}.choices`).map((entry, index) => {
                if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.choices[${index}]`);
                return {
                  player: expectString(entry["player"], `${path}.choices[${index}].player`),
                  timing:
                    entry["timing"] === undefined
                      ? undefined
                      : expectString(entry["timing"], `${path}.choices[${index}].timing`),
                  died: expectBool(entry["died"], `${path}.choices[${index}].died`),
                };
              }),
      };
    }
    case "Investigator":
      return {
        ...base,
        type: "Investigator",
        minionRole: input["minionRole"] as string | undefined,
        role: input["role"] as string | undefined,
        among: expectStringArray(input["among"], `${path}.among`),
      };
    case "Librarian":
      return {
        ...base,
        type: "Librarian",
        role: input["role"] as string | undefined,
        among: input["among"] === undefined ? undefined : expectStringArray(input["among"], `${path}.among`),
      };
    case "Washerwoman":
      return {
        ...base,
        type: "Washerwoman",
        role: input["role"] === undefined ? undefined : expectString(input["role"], `${path}.role`),
        among: input["among"] === undefined ? [] : expectStringArray(input["among"], `${path}.among`),
      };
    case "Chef":
      return {
        ...base,
        type: "Chef",
        count: input["count"] === undefined ? undefined : expectNumber(input["count"], `${path}.count`),
      };
    case "Chambermaid": {
      const checks = input["checks"];
      return {
        ...base,
        type: "Chambermaid",
        checks:
          checks === undefined
            ? undefined
            : expectArray(checks, `${path}.checks`).map((entry, index) => {
                if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.checks[${index}]`);
                return {
                  left: expectString(entry["left"], `${path}.checks[${index}].left`),
                  right: expectString(entry["right"], `${path}.checks[${index}].right`),
                  count: expectNumber(entry["count"], `${path}.checks[${index}].count`),
                  timing:
                    entry["timing"] === undefined
                      ? undefined
                      : expectString(entry["timing"], `${path}.checks[${index}].timing`),
                };
              }),
      };
    }
    case "Empath": {
      return {
        ...base,
        type: "Empath",
        count: input["count"] === undefined ? undefined : expectNumber(input["count"], `${path}.count`),
      };
    }
    case "Exorcist": {
      const choices = input["choices"];
      return {
        ...base,
        type: "Exorcist",
        choices:
          choices === undefined
            ? undefined
            : expectArray(choices, `${path}.choices`).map((entry, index) => {
                if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.choices[${index}]`);
                return {
                  player: expectString(entry["player"], `${path}.choices[${index}].player`),
                  timing:
                    entry["timing"] === undefined
                      ? undefined
                      : expectString(entry["timing"], `${path}.choices[${index}].timing`),
                };
              }),
      };
    }
    case "Innkeeper": {
      const choices = input["choices"];
      return {
        ...base,
        type: "Innkeeper",
        choices:
          choices === undefined
            ? undefined
            : expectArray(choices, `${path}.choices`).map((entry, index) => {
                const choicePath = `${path}.choices[${index}]`;
                if (!isObject(entry)) throw new ValidationError(`Expected object`, choicePath);
                const players = expectStringArray(entry["players"], `${choicePath}.players`);
                if (players.length > 2)
                  throw new ValidationError(`Innkeeper choice must have at most 2 players`, `${choicePath}.players`);
                return {
                  players,
                  timing:
                    entry["timing"] === undefined ? undefined : expectString(entry["timing"], `${choicePath}.timing`),
                };
              }),
      };
    }
    case "Devil's Advocate":
      return { ...base, type: "Devil's Advocate", choices: validateNightlyPlayerChoices(input["choices"], path) };
    case "Sailor":
      return { ...base, type: "Sailor", choices: validateNightlyPlayerChoices(input["choices"], path) };
    case "Godfather":
      return {
        ...base,
        type: "Godfather",
        outsiderRoles:
          input["outsiderRoles"] === undefined
            ? undefined
            : expectStringArray(input["outsiderRoles"], `${path}.outsiderRoles`),
        choices: validateNightlyPlayerChoices(input["choices"], path),
      };
    case "Grandmother":
      return {
        ...base,
        type: "Grandmother",
        grandchild:
          input["grandchild"] === undefined ? undefined : expectString(input["grandchild"], `${path}.grandchild`),
        role: input["role"] === undefined ? undefined : expectString(input["role"], `${path}.role`),
      };
    case "Moonchild":
      return {
        ...base,
        type: "Moonchild",
        chosen: input["chosen"] === undefined ? undefined : expectString(input["chosen"], `${path}.chosen`),
      };
    case "Flowergirl": {
      const votes = input["votes"];
      return {
        ...base,
        type: "Flowergirl",
        votes:
          votes === undefined
            ? undefined
            : expectArray(votes, `${path}.votes`).map((entry, index) => {
                if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.votes[${index}]`);
                return {
                  timing: expectString(entry["timing"], `${path}.votes[${index}].timing`),
                  voters: expectStringArray(entry["voters"], `${path}.votes[${index}].voters`),
                  demonVoted: expectBool(entry["demonVoted"], `${path}.votes[${index}].demonVoted`),
                };
              }),
      };
    }
    case "FortuneTeller": {
      const checks = input["checks"];
      if (!Array.isArray(checks)) throw new ValidationError(`Expected array`, `${path}.checks`);
      return {
        ...base,
        type: "FortuneTeller",
        checks: checks.map((c, i) => {
          if (!isObject(c)) throw new ValidationError(`Expected object`, `${path}.checks[${i}]`);
          return {
            left: expectString(c["left"], `${path}.checks[${i}].left`),
            right: expectString(c["right"], `${path}.checks[${i}].right`),
            yes: expectBool(c["yes"], `${path}.checks[${i}].yes`),
            timing: c["timing"] as string | undefined,
          };
        }),
      };
    }
    case "Undertaker":
      return {
        ...base,
        type: "Undertaker",
        player: input["player"] === undefined ? undefined : expectString(input["player"], `${path}.player`),
        role: input["role"] === undefined ? undefined : expectString(input["role"], `${path}.role`),
      };
    case "Legionary": {
      const counts = input["counts"];
      return {
        ...base,
        type: "Legionary",
        counts:
          counts === undefined
            ? undefined
            : expectArray(counts, `${path}.counts`).map((entry, index) => {
                if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.counts[${index}]`);
                return {
                  count: expectNumber(entry["count"], `${path}.counts[${index}].count`),
                  timing:
                    entry["timing"] === undefined
                      ? undefined
                      : expectString(entry["timing"], `${path}.counts[${index}].timing`),
                };
              }),
      };
    }
    case "Noble":
      return {
        ...base,
        type: "Noble",
        oneEvilAmong:
          input["oneEvilAmong"] === undefined
            ? undefined
            : expectStringArray(input["oneEvilAmong"], `${path}.oneEvilAmong`),
        among: input["among"] === undefined ? undefined : expectStringArray(input["among"], `${path}.among`),
        evilCount: input["evilCount"] as number | undefined,
      };
    case "Oracle":
      return {
        ...base,
        type: "Oracle",
        count: input["count"] === undefined ? undefined : expectNumber(input["count"], `${path}.count`),
      };
    case "Professor":
      return {
        ...base,
        type: "Professor",
        target: input["target"] === undefined ? undefined : expectString(input["target"], `${path}.target`),
      };
    case "Steward":
      return {
        ...base,
        type: "Steward",
        goodPlayer:
          input["goodPlayer"] === undefined ? undefined : expectString(input["goodPlayer"], `${path}.goodPlayer`),
      };
    case "Knight": {
      const noDemonAmong = expectStringArray(input["noDemonAmong"], `${path}.noDemonAmong`);
      if (noDemonAmong.length > 2) {
        throw new ValidationError(`Knight 'noDemonAmong' must have at most ${2} players`, `${path}.noDemonAmong`);
      }
      return {
        ...base,
        type: "Knight",
        noDemonAmong,
      };
    }
    case "Gambler": {
      const guesses = input["guesses"];
      return {
        ...base,
        type: "Gambler",
        guesses:
          guesses === undefined
            ? undefined
            : expectArray(guesses, `${path}.guesses`).map((entry, index) => {
                if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.guesses[${index}]`);
                rejectLegacyField(entry, "survived", `${path}.guesses[${index}].survived`);
                return {
                  player: expectString(entry["player"], `${path}.guesses[${index}].player`),
                  role: expectString(entry["role"], `${path}.guesses[${index}].role`),
                  timing:
                    entry["timing"] === undefined
                      ? undefined
                      : expectString(entry["timing"], `${path}.guesses[${index}].timing`),
                };
              }),
      };
    }
    case "Gossip": {
      const statements = input["statements"];
      return {
        ...base,
        type: "Gossip",
        statements:
          statements === undefined
            ? undefined
            : expectArray(statements, `${path}.statements`).map((entry, index) => {
                if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.statements[${index}]`);
                return {
                  expression: expectString(entry["expression"], `${path}.statements[${index}].expression`),
                  timing:
                    entry["timing"] === undefined
                      ? undefined
                      : expectString(entry["timing"], `${path}.statements[${index}].timing`),
                };
              }),
      };
    }
    case "Philosopher":
      return {
        ...base,
        type: "Philosopher",
        role: input["role"] === undefined ? undefined : expectString(input["role"], `${path}.role`),
        seamstress:
          input["seamstress"] === undefined
            ? undefined
            : validatePhilosopherSeamstress(input["seamstress"], `${path}.seamstress`),
      };
    case "Princess": {
      const nominations = input["nominations"];
      return {
        ...base,
        type: "Princess",
        nominations:
          nominations === undefined
            ? undefined
            : expectArray(nominations, `${path}.nominations`).map((entry, index) => {
                if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.nominations[${index}]`);
                return {
                  player: expectString(entry["player"], `${path}.nominations[${index}].player`),
                  timing:
                    entry["timing"] === undefined
                      ? undefined
                      : expectString(entry["timing"], `${path}.nominations[${index}].timing`),
                };
              }),
      };
    }
    case "Prodigy": {
      const checks = input["checks"];
      if (!Array.isArray(checks)) throw new ValidationError(`Expected array`, `${path}.checks`);
      return {
        ...base,
        type: "Prodigy",
        checks: checks.map((entry, index) => {
          if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.checks[${index}]`);
          return {
            chosen: expectString(entry["chosen"], `${path}.checks[${index}].chosen`),
            learned: expectString(entry["learned"], `${path}.checks[${index}].learned`),
            timing:
              entry["timing"] === undefined
                ? undefined
                : expectString(entry["timing"], `${path}.checks[${index}].timing`),
          };
        }),
      };
    }
    case "Puzzlemaster": {
      const guesses = input["guesses"];
      return {
        ...base,
        type: "Puzzlemaster",
        guesses:
          guesses === undefined
            ? undefined
            : expectArray(guesses, `${path}.guesses`).map((entry, index) => {
                if (!isObject(entry)) throw new ValidationError(`Expected object`, `${path}.guesses[${index}]`);
                return {
                  player: expectString(entry["player"], `${path}.guesses[${index}].player`),
                  learnedDemon: expectString(entry["learnedDemon"], `${path}.guesses[${index}].learnedDemon`),
                  timing:
                    entry["timing"] === undefined
                      ? undefined
                      : expectString(entry["timing"], `${path}.guesses[${index}].timing`),
                };
              }),
      };
    }
    case "Seamstress": {
      const among = input["among"] === undefined ? [] : expectStringArray(input["among"], `${path}.among`);
      const aligned = input["aligned"] === undefined ? undefined : expectBool(input["aligned"], `${path}.aligned`);
      if (aligned !== undefined && among.length !== 2)
        throw new ValidationError(`Seamstress 'among' must have exactly two players`, `${path}.among`);
      return {
        ...base,
        type: "Seamstress",
        among,
        aligned,
      };
    }
    case "Juggler": {
      const guesses = input["guesses"];
      if (!isObject(guesses)) throw new ValidationError(`Expected object`, `${path}.guesses`);
      const out: Record<string, string> = {};
      for (const [k, v] of Object.entries(guesses)) out[k] = expectString(v, `${path}.guesses.${k}`);
      return {
        ...base,
        type: "Juggler",
        guesses: out,
        correctCount: input["correctCount"] as number | undefined,
      };
    }
    case "Dreamer":
      return {
        ...base,
        type: "Dreamer",
        player: input["player"] === undefined ? undefined : expectString(input["player"], `${path}.player`),
        roles: input["roles"] === undefined ? [] : expectStringArray(input["roles"], `${path}.roles`),
      };
    case "Shugenja": {
      if (input["evilDirection"] === undefined) return { ...base, type: "Shugenja" };
      const dir = expectString(input["evilDirection"], `${path}.evilDirection`);
      if (dir !== "clockwise" && dir !== "anticlockwise")
        throw new ValidationError(`evilDirection must be clockwise or anticlockwise`, `${path}.evilDirection`);
      return { ...base, type: "Shugenja", evilDirection: dir };
    }
    case "Clockmaker":
      return {
        ...base,
        type: "Clockmaker",
        distance:
          input["distance"] === undefined ? undefined : expectPositiveInteger(input["distance"], `${path}.distance`),
      };
    case "Courtier":
      return {
        ...base,
        type: "Courtier",
        role: input["role"] === undefined ? undefined : expectString(input["role"], `${path}.role`),
        drunkTimings:
          input["drunkTimings"] === undefined
            ? undefined
            : expectStringArray(input["drunkTimings"], `${path}.drunkTimings`),
      };
    case "Mathematician":
      return {
        ...base,
        type: "Mathematician",
        malfunctions:
          input["malfunctions"] === undefined
            ? undefined
            : validateMathematicianCounts(input["malfunctions"], `${path}.malfunctions`),
      };
    case "Town Crier": {
      const checks = input["checks"];
      if (!Array.isArray(checks)) throw new ValidationError(`Expected array`, `${path}.checks`);
      return {
        ...base,
        type: "Town Crier",
        checks: checks.map((entry, index) => {
          const entryPath = `${path}.checks[${index}]`;
          if (!isObject(entry)) throw new ValidationError(`Expected object`, entryPath);
          return {
            timing: expectString(entry["timing"], `${entryPath}.timing`),
            nominators: expectStringArray(entry["nominators"], `${entryPath}.nominators`),
            minionNominated: expectBool(entry["minionNominated"], `${entryPath}.minionNominated`),
          };
        }),
      };
    }
    case "Ravenkeeper":
      return {
        ...base,
        type: "Ravenkeeper",
        player: input["player"] === undefined ? undefined : expectString(input["player"], `${path}.player`),
        role: input["role"] === undefined ? undefined : expectString(input["role"], `${path}.role`),
      };
    case "Sage":
      return {
        ...base,
        type: "Sage",
        demonAmong:
          input["demonAmong"] === undefined ? undefined : expectStringArray(input["demonAmong"], `${path}.demonAmong`),
      };
    case "Slayer":
      return {
        ...base,
        type: "Slayer",
        target: input["target"] === undefined ? undefined : expectString(input["target"], `${path}.target`),
        killed: input["killed"] === undefined ? undefined : expectBool(input["killed"], `${path}.killed`),
        gameContinued:
          input["gameContinued"] === undefined
            ? undefined
            : expectBool(input["gameContinued"], `${path}.gameContinued`),
      };
    case "Snake Charmer": {
      const checks = input["checks"];
      if (!Array.isArray(checks)) throw new ValidationError(`Expected array`, `${path}.checks`);
      return {
        ...base,
        type: "Snake Charmer",
        checks: checks.map((c, i) => {
          if (!isObject(c)) throw new ValidationError(`Expected object`, `${path}.checks[${i}]`);
          return {
            player: expectString(c["player"], `${path}.checks[${i}].player`),
            demon: expectBool(c["demon"], `${path}.checks[${i}].demon`),
            timing: expectString(c["timing"], `${path}.checks[${i}].timing`),
          };
        }),
      };
    }
    case "VillageIdiot": {
      const checks = input["checks"];
      if (!Array.isArray(checks)) throw new ValidationError(`Expected array`, `${path}.checks`);
      return {
        ...base,
        type: "VillageIdiot",
        checks: checks.map((c, i) => {
          if (!isObject(c)) throw new ValidationError(`Expected object`, `${path}.checks[${i}]`);
          return {
            player: expectString(c["player"], `${path}.checks[${i}].player`),
            good: expectBool(c["good"], `${path}.checks[${i}].good`),
            timing: c["timing"] === undefined ? undefined : expectString(c["timing"], `${path}.checks[${i}].timing`),
          };
        }),
      };
    }
    case "Klutz":
      return {
        ...base,
        type: "Klutz",
        chosen: input["chosen"] === undefined ? undefined : expectString(input["chosen"], `${path}.chosen`),
      };
    case "Virgin":
      return {
        ...base,
        type: "Virgin",
        nominator: input["nominator"] === undefined ? undefined : expectString(input["nominator"], `${path}.nominator`),
        executed: input["executed"] === undefined ? undefined : expectBool(input["executed"], `${path}.executed`),
      };
    case "Balloonist": {
      const pairs = input["differentCharacterTypePairs"];
      if (!Array.isArray(pairs)) throw new ValidationError(`Expected array`, `${path}.differentCharacterTypePairs`);
      return {
        ...base,
        type: "Balloonist",
        differentCharacterTypePairs: pairs.map((p, i) => {
          if (!Array.isArray(p) || p.length !== 2)
            throw new ValidationError(`Expected [left, right]`, `${path}.differentCharacterTypePairs[${i}]`);
          return [
            expectString(p[0], `${path}.differentCharacterTypePairs[${i}][0]`),
            expectString(p[1], `${path}.differentCharacterTypePairs[${i}][1]`),
          ] as const;
        }),
      };
    }
    case "Savant": {
      const statements = input["statements"];
      if (!Array.isArray(statements)) throw new ValidationError(`Expected array`, `${path}.statements`);
      if (statements.length > 1)
        throw new ValidationError(`Savant claims must have exactly one statement`, `${path}.statements`);
      return {
        ...base,
        type: "Savant",
        statements: statements.map((statement, index) => {
          if (!isObject(statement)) throw new ValidationError(`Expected object`, `${path}.statements[${index}]`);
          return { options: expectStringArray(statement["options"], `${path}.statements[${index}].options`) };
        }),
      };
    }
    case "Nightwatchman":
      return {
        ...base,
        type: "Nightwatchman",
        chosen: input["chosen"] === undefined ? undefined : expectString(input["chosen"], `${path}.chosen`),
        learned: input["learned"] === undefined ? undefined : expectBool(input["learned"], `${path}.learned`),
        confirmedByChosen:
          input["confirmedByChosen"] === undefined
            ? undefined
            : expectBool(input["confirmedByChosen"], `${path}.confirmedByChosen`),
      };
    default:
      return { ...base, type: type as Claim["type"] } as Claim;
  }
}

function validateNightlyPlayerChoices(
  input: unknown,
  path: string,
): readonly { readonly player: string; readonly timing?: string }[] | undefined {
  if (input === undefined) return undefined;
  return expectArray(input, `${path}.choices`).map((entry, index) => {
    const choicePath = `${path}.choices[${index}]`;
    if (!isObject(entry)) throw new ValidationError(`Expected object`, choicePath);
    return {
      player: expectString(entry["player"], `${choicePath}.player`),
      timing: entry["timing"] === undefined ? undefined : expectString(entry["timing"], `${choicePath}.timing`),
    };
  });
}

function validateCustomInfo(input: unknown, path: string, claimType: string): Claim["info"] {
  if (claimType !== "Artist") throw new ValidationError(`Only Artist claims may use custom info expressions`, path);
  if (!Array.isArray(input)) throw new ValidationError(`Expected array`, path);
  return input.map((entry, index) => {
    const entryPath = `${path}[${index}]`;
    if (!isObject(entry)) throw new ValidationError(`Expected object`, entryPath);
    return {
      timing: entry["timing"] === undefined ? undefined : expectString(entry["timing"], `${entryPath}.timing`),
      role: entry["role"] === undefined ? undefined : expectString(entry["role"], `${entryPath}.role`),
      expression:
        entry["expression"] === undefined ? undefined : expectString(entry["expression"], `${entryPath}.expression`),
    };
  });
}

function validatePhilosopherSeamstress(
  input: unknown,
  path: string,
): NonNullable<Extract<Claim, { type: "Philosopher" }>["seamstress"]> {
  if (!isObject(input)) throw new ValidationError(`Expected object`, path);
  return {
    among: expectStringArray(input["among"], `${path}.among`),
    aligned: input["aligned"] === undefined ? undefined : expectBool(input["aligned"], `${path}.aligned`),
    timing: input["timing"] === undefined ? undefined : expectString(input["timing"], `${path}.timing`),
  };
}

function validatePair(input: unknown, path: string): [string, string] {
  if (!Array.isArray(input) || input.length !== 2) throw new ValidationError(`Expected [left, right]`, path);
  return [expectString(input[0], `${path}[0]`), expectString(input[1], `${path}[1]`)];
}

function expectPositiveInteger(v: unknown, path: string): number {
  const value = expectNumber(v, path);
  if (value <= 0) throw new ValidationError(`Expected positive integer`, path);
  return value;
}

function validateMathematicianCounts(input: unknown, path: string): Array<{ timing: string; count: number }> {
  if (!Array.isArray(input)) throw new ValidationError(`Expected array`, path);
  return input.map((entry, index) => {
    const entryPath = `${path}[${index}]`;
    if (!isObject(entry)) throw new ValidationError(`Expected object`, entryPath);
    const count = expectNumber(entry["count"], `${entryPath}.count`);
    if (count < 0) throw new ValidationError(`Expected non-negative integer`, `${entryPath}.count`);
    return {
      timing: expectString(entry["timing"], `${entryPath}.timing`),
      count,
    };
  });
}
