import { type Claim, type PuzzleDoc, SUPPORTED_CLAIM_TYPES } from "./puzzleDoc";

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

function expectBool(v: unknown, path: string): boolean {
  if (typeof v !== "boolean") throw new ValidationError(`Expected boolean`, path);
  return v;
}

function expectNumber(v: unknown, path: string): number {
  if (typeof v !== "number" || !Number.isInteger(v)) throw new ValidationError(`Expected integer`, path);
  return v;
}

export function validatePuzzleDoc(input: unknown): PuzzleDoc {
  if (!isObject(input)) throw new ValidationError(`Expected object`, "$");
  if (input["version"] !== 1) throw new ValidationError(`Unsupported version (expected 1)`, "$.version");
  const players = expectStringArray(input["players"], "$.players");
  const script = expectStringArray(input["script"], "$.script");
  const seating = input["seating"] === undefined ? undefined : expectStringArray(input["seating"], "$.seating");
  const claims = input["claims"];
  if (!Array.isArray(claims)) throw new ValidationError(`Expected array`, "$.claims");
  const validatedClaims = claims.map((c, i) => validateClaim(c, `$.claims[${i}]`));

  const setup = input["setup"];
  if (setup !== undefined && setup !== "standard" && setup !== "none")
    throw new ValidationError(`setup must be "standard" or "none"`, "$.setup");

  const title = input["title"] === undefined ? undefined : expectString(input["title"], "$.title");
  const uniqueCharacters =
    input["uniqueCharacters"] === undefined ? undefined : expectBool(input["uniqueCharacters"], "$.uniqueCharacters");
  const fixedRoles = input["fixedRoles"] === undefined ? undefined : validateFixedRoles(input["fixedRoles"]);

  return {
    version: 1,
    title,
    players,
    seating,
    script,
    setup,
    uniqueCharacters,
    fixedRoles,
    claims: validatedClaims,
  };
}

function validateFixedRoles(v: unknown): PuzzleDoc["fixedRoles"] {
  if (!Array.isArray(v)) throw new ValidationError(`Expected array`, "$.fixedRoles");
  return v.map((entry, i) => {
    const path = `$.fixedRoles[${i}]`;
    if (!isObject(entry)) throw new ValidationError(`Expected object`, path);
    return {
      name: expectString(entry["name"], `${path}.name`),
      roles: expectStringArray(entry["roles"], `${path}.roles`),
    };
  });
}

function validateClaim(input: unknown, path: string): Claim {
  if (!isObject(input)) throw new ValidationError(`Expected object`, path);
  const type = expectString(input["type"], `${path}.type`);
  if (!SUPPORTED_CLAIM_TYPES.has(type as Claim["type"]))
    throw new ValidationError(`Unsupported claim type '${type}'`, `${path}.type`);
  const name = expectString(input["name"], `${path}.name`);
  const timing = input["timing"] === undefined ? undefined : expectString(input["timing"], `${path}.timing`);
  const base = { name, timing };

  switch (type as Claim["type"]) {
    case "Investigator":
      return {
        ...base,
        type: "Investigator",
        minionRole: input["minionRole"] as string | undefined,
        role: input["role"] as string | undefined,
        among: expectStringArray(input["among"], `${path}.among`),
        registers: input["registers"] as boolean | undefined,
      };
    case "Librarian":
      return {
        ...base,
        type: "Librarian",
        role: input["role"] as string | undefined,
        outsiderCount: input["outsiderCount"] as number | undefined,
        among: input["among"] === undefined ? undefined : expectStringArray(input["among"], `${path}.among`),
        registers: input["registers"] as boolean | undefined,
      };
    case "Washerwoman":
      return {
        ...base,
        type: "Washerwoman",
        role: expectString(input["role"], `${path}.role`),
        among: expectStringArray(input["among"], `${path}.among`),
        registers: input["registers"] as boolean | undefined,
      };
    case "Chef":
      return {
        ...base,
        type: "Chef",
        count: expectNumber(input["count"], `${path}.count`),
        registers: input["registers"] as boolean | undefined,
      };
    case "Empath":
      return {
        ...base,
        type: "Empath",
        count: expectNumber(input["count"], `${path}.count`),
        player: input["player"] as string | undefined,
      };
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
            demonRole: c["demonRole"] as string | undefined,
            registers: c["registers"] as boolean | undefined,
            timing: c["timing"] as string | undefined,
          };
        }),
      };
    }
    case "Undertaker":
      return {
        ...base,
        type: "Undertaker",
        player: expectString(input["player"], `${path}.player`),
        role: expectString(input["role"], `${path}.role`),
      };
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
    case "Steward":
      return { ...base, type: "Steward", goodPlayer: expectString(input["goodPlayer"], `${path}.goodPlayer`) };
    case "Knight":
      return {
        ...base,
        type: "Knight",
        noDemonAmong: expectStringArray(input["noDemonAmong"], `${path}.noDemonAmong`),
      };
    case "Seamstress": {
      const among = expectStringArray(input["among"], `${path}.among`);
      if (among.length !== 2)
        throw new ValidationError(`Seamstress 'among' must have exactly two players`, `${path}.among`);
      return {
        ...base,
        type: "Seamstress",
        among: [among[0], among[1]] as readonly [string, string],
        aligned: expectBool(input["aligned"], `${path}.aligned`),
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
        player: expectString(input["player"], `${path}.player`),
        roles: expectStringArray(input["roles"], `${path}.roles`),
      };
    case "Shugenja": {
      const dir = expectString(input["evilDirection"], `${path}.evilDirection`);
      if (dir !== "clockwise" && dir !== "anticlockwise")
        throw new ValidationError(`evilDirection must be clockwise or anticlockwise`, `${path}.evilDirection`);
      return { ...base, type: "Shugenja", evilDirection: dir };
    }
    case "Clockmaker":
      return {
        ...base,
        type: "Clockmaker",
        demonNextToMinion: expectBool(input["demonNextToMinion"], `${path}.demonNextToMinion`),
      };
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
          };
        }),
      };
    }
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
      if (statements.length !== 1)
        throw new ValidationError(`Savant claims must have exactly one statement`, `${path}.statements`);
      const statement = statements[0];
      if (!isObject(statement)) throw new ValidationError(`Expected object`, `${path}.statements[0]`);
      return {
        ...base,
        type: "Savant",
        statements: [{ options: expectStringArray(statement["options"], `${path}.statements[0].options`) }],
      };
    }
    default:
      return { ...base, type: type as Claim["type"] } as Claim;
  }
}
