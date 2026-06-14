import { KNIGHT_NO_DEMON_AMONG_MAX, type Claim, type PuzzleDoc, SUPPORTED_CLAIM_TYPES } from "./puzzleDoc";

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
  const claims = input["claims"];
  if (!Array.isArray(claims)) throw new ValidationError(`Expected array`, "$.claims");
  const validatedClaims = claims.map((c, i) => validateClaim(c, `$.claims[${i}]`));

  const setup = input["setup"];
  if (setup !== undefined && setup !== "standard" && setup !== "none")
    throw new ValidationError(`setup must be "standard" or "none"`, "$.setup");

  const title = input["title"] === undefined ? undefined : expectString(input["title"], "$.title");
  const uniqueCharacters =
    input["uniqueCharacters"] === undefined ? undefined : expectBool(input["uniqueCharacters"], "$.uniqueCharacters");
  const fixedRoles =
    input["fixedRoles"] === undefined ? undefined : validateRoleConstraints(input["fixedRoles"], "$.fixedRoles");
  const forbiddenRoles =
    input["forbiddenRoles"] === undefined
      ? undefined
      : validateRoleConstraints(input["forbiddenRoles"], "$.forbiddenRoles");

  return {
    version: 1,
    title,
    players,
    script,
    setup,
    uniqueCharacters,
    fixedRoles,
    forbiddenRoles,
    claims: validatedClaims,
  };
}

function validateRoleConstraints(v: unknown, pathRoot: string): PuzzleDoc["fixedRoles"] {
  if (!Array.isArray(v)) throw new ValidationError(`Expected array`, pathRoot);
  return v.map((entry, i) => {
    const path = `${pathRoot}[${i}]`;
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
  const vortoxAffected =
    input["vortoxAffected"] === undefined ? undefined : expectBool(input["vortoxAffected"], `${path}.vortoxAffected`);
  const info = input["info"] === undefined ? undefined : validateCustomInfo(input["info"], `${path}.info`);
  const base = { name, timing, vortoxAffected, info };

  switch (type as Claim["type"]) {
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
        outsiderCount: input["outsiderCount"] as number | undefined,
        among: input["among"] === undefined ? undefined : expectStringArray(input["among"], `${path}.among`),
        registers: input["registers"] as boolean | undefined,
      };
    case "Washerwoman":
      return {
        ...base,
        type: "Washerwoman",
        role: input["role"] === undefined ? undefined : expectString(input["role"], `${path}.role`),
        among: input["among"] === undefined ? [] : expectStringArray(input["among"], `${path}.among`),
        registers: input["registers"] as boolean | undefined,
      };
    case "Chef":
      return {
        ...base,
        type: "Chef",
        count: input["count"] === undefined ? undefined : expectNumber(input["count"], `${path}.count`),
        registers: input["registers"] as boolean | undefined,
      };
    case "Empath":
      return {
        ...base,
        type: "Empath",
        count: input["count"] === undefined ? undefined : expectNumber(input["count"], `${path}.count`),
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
        player: input["player"] === undefined ? undefined : expectString(input["player"], `${path}.player`),
        role: input["role"] === undefined ? undefined : expectString(input["role"], `${path}.role`),
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
      return {
        ...base,
        type: "Steward",
        goodPlayer:
          input["goodPlayer"] === undefined ? undefined : expectString(input["goodPlayer"], `${path}.goodPlayer`),
      };
    case "Knight": {
      const noDemonAmong = expectStringArray(input["noDemonAmong"], `${path}.noDemonAmong`);
      if (noDemonAmong.length > KNIGHT_NO_DEMON_AMONG_MAX) {
        throw new ValidationError(
          `Knight 'noDemonAmong' must have at most ${KNIGHT_NO_DEMON_AMONG_MAX} players`,
          `${path}.noDemonAmong`,
        );
      }
      return {
        ...base,
        type: "Knight",
        noDemonAmong,
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
    case "Mathematician":
      return {
        ...base,
        type: "Mathematician",
        malfunctions:
          input["malfunctions"] === undefined
            ? undefined
            : validateMathematicianCounts(input["malfunctions"], `${path}.malfunctions`),
      };
    case "Sage":
      return {
        ...base,
        type: "Sage",
        demonAmong:
          input["demonAmong"] === undefined ? undefined : expectStringArray(input["demonAmong"], `${path}.demonAmong`),
      };
    case "Snake Charmer":
      return {
        ...base,
        type: "Snake Charmer",
        checked: input["checked"] === undefined ? undefined : expectString(input["checked"], `${path}.checked`),
        demon: input["demon"] === undefined ? undefined : expectBool(input["demon"], `${path}.demon`),
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
    default:
      return { ...base, type: type as Claim["type"] } as Claim;
  }
}

function validateCustomInfo(input: unknown, path: string): Claim["info"] {
  if (!Array.isArray(input)) throw new ValidationError(`Expected array`, path);
  return input.map((entry, index) => {
    const entryPath = `${path}[${index}]`;
    if (!isObject(entry)) throw new ValidationError(`Expected object`, entryPath);
    return {
      timing: entry["timing"] === undefined ? undefined : expectString(entry["timing"], `${entryPath}.timing`),
      expression:
        entry["expression"] === undefined ? undefined : expectString(entry["expression"], `${entryPath}.expression`),
      vortoxAffected:
        entry["vortoxAffected"] === undefined
          ? undefined
          : expectBool(entry["vortoxAffected"], `${entryPath}.vortoxAffected`),
    };
  });
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
