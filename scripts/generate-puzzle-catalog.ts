import { mkdirSync, readdirSync, readFileSync, renameSync, writeFileSync } from "node:fs";
import { basename, join } from "node:path";
import { pathToFileURL } from "node:url";
import type { Claim, FixedRoleConstraint, PuzzleDoc } from "../src/schema/puzzleDoc";
import { roleName, type RoleRef } from "../src/model/core";
import { playerNames, type Role } from "../src/model/characters";

interface PuzzleModule {
  readonly PLAYERS?: readonly Role[];
  readonly PLAYER_NAMES?: readonly string[];
  readonly LEFT_PLAYERS?: readonly Role[];
  readonly RIGHT_PLAYERS?: readonly Role[];
  readonly CHARACTERS?: readonly RoleRef[];
}

interface CatalogEntry {
  readonly id: string;
  readonly label: string;
  readonly doc: PuzzleDoc;
}

const PUZZLE_DIR = join(import.meta.dir, "..", "src", "model", "puzzles");
const OUTPUT_PATH = join(import.meta.dir, "..", "src", "examples", "puzzleCatalog.generated.json");
const OUTPUT_TMP_PATH = `${OUTPUT_PATH}.tmp`;

const SPECIAL_CLAIM_TYPES: Readonly<Record<string, Claim["type"]>> = {
  "Fortune Teller": "FortuneTeller",
  "Village Idiot": "VillageIdiot",
};

function clean<T extends Record<string, unknown>>(value: T): T {
  return Object.fromEntries(Object.entries(value).filter(([, entry]) => entry !== undefined)) as T;
}

function asStrings(value: unknown): string[] {
  return Array.isArray(value) ? value.filter((entry): entry is string => typeof entry === "string") : [];
}

function roleRefName(value: unknown): string | undefined {
  return value === undefined ? undefined : roleName(value as RoleRef);
}

function roleRefNames(value: unknown): string[] {
  return Array.isArray(value) ? value.map((entry) => roleName(entry as RoleRef)) : [];
}

function timing(role: Role): string | undefined {
  return role.timing;
}

function serializeGuesses(value: unknown): Record<string, string> {
  const entries =
    value instanceof Map ? [...value.entries()] : Object.entries((value ?? {}) as Record<string, unknown>);
  const guesses: Record<string, string> = {};
  for (const [player, guessedRole] of entries) guesses[player] = roleName(guessedRole as RoleRef);
  return guesses;
}

function serializeClaim(role: Role): Claim {
  const type = SPECIAL_CLAIM_TYPES[role.roleName] ?? (role.roleName as Claim["type"]);
  const base = { type, name: role.name, timing: timing(role) };
  const source = role as Role & Record<string, unknown>;

  switch (role.roleName) {
    case "Investigator":
      return clean({
        ...base,
        type: "Investigator",
        role: roleRefName(source["role"]),
        minionRole: roleRefName(source["minionRole"]),
        among: asStrings(source["among"]),
        registers: source["registers"] === false ? false : undefined,
      }) as Claim;
    case "Librarian":
      return clean({
        ...base,
        type: "Librarian",
        role: roleRefName(source["role"]),
        outsiderCount: source["outsiderCount"],
        among: asStrings(source["among"]),
        registers: source["registers"] === false ? false : undefined,
      }) as Claim;
    case "Washerwoman":
      return clean({
        ...base,
        type: "Washerwoman",
        role: roleRefName(source["role"]),
        among: asStrings(source["among"]),
        registers: source["registers"] === false ? false : undefined,
      }) as Claim;
    case "Chef":
      return clean({
        ...base,
        type: "Chef",
        count: source["count"],
        registers: source["registers"] === false ? false : undefined,
      }) as Claim;
    case "Empath":
      return clean({ ...base, type: "Empath", count: source["count"], player: source["player"] }) as Claim;
    case "Fortune Teller":
      return clean({
        ...base,
        type: "FortuneTeller",
        checks: Array.isArray(source["checks"])
          ? source["checks"].map((check) =>
              clean({
                left: (check as { left?: string }).left,
                right: (check as { right?: string }).right,
                yes: (check as { yes?: boolean }).yes ?? false,
                demonRole: roleRefName((check as { demonRole?: RoleRef }).demonRole),
                registers: (check as { registers?: boolean }).registers,
                timing: (check as { timing?: string }).timing,
              }),
            )
          : [],
      }) as Claim;
    case "Undertaker":
      return clean({
        ...base,
        type: "Undertaker",
        player: source["player"],
        role: roleRefName(source["role"]),
      }) as Claim;
    case "Noble":
      return clean({
        ...base,
        type: "Noble",
        oneEvilAmong: asStrings(source["oneEvilAmong"]),
        among: asStrings(source["among"]),
        evilCount: source["evilCount"],
      }) as Claim;
    case "Steward":
      return clean({ ...base, type: "Steward", goodPlayer: source["goodPlayer"] }) as Claim;
    case "Knight":
      return clean({ ...base, type: "Knight", noDemonAmong: asStrings(source["noDemonAmong"]) }) as Claim;
    case "Seamstress":
      return clean({
        ...base,
        type: "Seamstress",
        among: asStrings(source["among"]),
        aligned: source["aligned"],
      }) as Claim;
    case "Juggler":
      return clean({
        ...base,
        type: "Juggler",
        guesses: serializeGuesses(source["guesses"]),
        correctCount: source["correctCount"],
      }) as Claim;
    case "Dreamer":
      return clean({
        ...base,
        type: "Dreamer",
        player: source["player"],
        roles: roleRefNames(source["roles"]),
      }) as Claim;
    case "Shugenja":
      return clean({ ...base, type: "Shugenja", evilDirection: source["evilDirection"] }) as Claim;
    case "Clockmaker":
      return clean({
        ...base,
        type: "Clockmaker",
        distance: source["distance"],
      }) as Claim;
    case "Village Idiot":
      return clean({
        ...base,
        type: "VillageIdiot",
        checks: Array.isArray(source["checks"])
          ? source["checks"].map((check) => ({
              player: (check as { player?: string }).player ?? "",
              good: (check as { good?: boolean }).good ?? true,
            }))
          : [],
      }) as Claim;
    case "Balloonist":
      return clean({
        ...base,
        type: "Balloonist",
        differentCharacterTypePairs: Array.isArray(source["differentCharacterTypePairs"])
          ? source["differentCharacterTypePairs"]
          : [],
      }) as Claim;
    case "Savant":
      return clean({ ...base, type: "Savant", statements: [] }) as Claim;
    default:
      return clean(base) as Claim;
  }
}

function labelFromFilename(fileName: string): string {
  const match = /^puzzle-(\d+)([a-z]?)-(.+)\.ts$/.exec(fileName);
  if (match === null) throw new Error(`Unexpected puzzle filename: ${fileName}`);
  const [, rawNumber, suffix = "", rawTitle] = match;
  const number = String(Number(rawNumber));
  const title = rawTitle
    .split("-")
    .map((word) => word[0]?.toUpperCase() + word.slice(1))
    .join(" ");
  return `Puzzle ${number}${suffix} - ${title}`;
}

function roleNamesByIdentifier(characters: readonly RoleRef[]): ReadonlyMap<string, string> {
  const entries = characters.map((character) => {
    const name = roleName(character);
    const identifier = (character as { readonly name?: string }).name ?? name.replace(/[^A-Za-z0-9]+/g, "");
    return [identifier, name] as const;
  });
  return new Map(entries);
}

function fixedRolesFromSource(source: string, characters: readonly RoleRef[]): FixedRoleConstraint[] | undefined {
  const roleNames = roleNamesByIdentifier(characters);
  const byPlayer = new Map<string, string[]>();

  for (const match of source.matchAll(/game\.fixActual\("([^"]+)",\s*([A-Za-z0-9_]+)\)/g)) {
    const [, player, roleIdentifier] = match;
    const fixedRole = roleIdentifier === undefined ? undefined : roleNames.get(roleIdentifier);
    if (player !== undefined && fixedRole !== undefined) byPlayer.set(player, [fixedRole]);
  }

  for (const match of source.matchAll(/game\.setPossibleActualRoles\("([^"]+)",\s*\[([^\]]+)\]\)/g)) {
    const [, player, identifiers] = match;
    if (player === undefined || identifiers === undefined) continue;
    const roles = identifiers
      .split(",")
      .map((identifier) => roleNames.get(identifier.trim()))
      .filter((role): role is string => role !== undefined);
    if (roles.length > 0) byPlayer.set(player, roles);
  }

  return byPlayer.size === 0
    ? undefined
    : [...byPlayer.entries()].map(([name, roles]) => ({
        name,
        roles,
      }));
}

function buildEntry({
  id,
  label,
  players,
  characters,
  source,
}: {
  readonly id: string;
  readonly label: string;
  readonly players: readonly Role[];
  readonly characters: readonly RoleRef[];
  readonly source: string;
}): CatalogEntry {
  return {
    id,
    label,
    doc: clean({
      version: 1,
      title: label,
      players: playerNames(players),
      script: characters.map(roleName),
      fixedRoles: fixedRolesFromSource(source, characters),
      claims: players.map(serializeClaim),
    }) as unknown as PuzzleDoc,
  };
}

async function loadPuzzle(fileName: string): Promise<CatalogEntry[]> {
  const modulePath = join(PUZZLE_DIR, fileName);
  const mod = (await import(pathToFileURL(modulePath).href)) as PuzzleModule;
  if (mod.CHARACTERS === undefined) {
    throw new Error(`${fileName} does not export CHARACTERS.`);
  }

  const id = basename(fileName, ".ts");
  const label = labelFromFilename(fileName);
  const source = readFileSync(modulePath, "utf8");
  if (mod.PLAYERS !== undefined) {
    return [
      {
        id,
        label,
        doc: clean({
          version: 1,
          title: label,
          players: mod.PLAYER_NAMES ?? playerNames(mod.PLAYERS),
          script: mod.CHARACTERS.map(roleName),
          fixedRoles: fixedRolesFromSource(source, mod.CHARACTERS),
          claims: mod.PLAYERS.map(serializeClaim),
        }) as unknown as PuzzleDoc,
      },
    ];
  }

  if (mod.LEFT_PLAYERS !== undefined && mod.RIGHT_PLAYERS !== undefined) {
    return [
      buildEntry({
        id: `${id}-left`,
        label: `${label} (left game)`,
        players: mod.LEFT_PLAYERS,
        characters: mod.CHARACTERS,
        source,
      }),
      buildEntry({
        id: `${id}-right`,
        label: `${label} (right game)`,
        players: mod.RIGHT_PLAYERS,
        characters: mod.CHARACTERS,
        source,
      }),
    ];
  }

  throw new Error(`${fileName} does not export PLAYERS or LEFT_PLAYERS/RIGHT_PLAYERS.`);
}

const puzzleFiles = readdirSync(PUZZLE_DIR)
  .filter((fileName) => /^puzzle-\d+[a-z]?-.+\.ts$/.test(fileName))
  .filter((fileName) => fileName !== "puzzle-25-clockdoku.ts")
  .sort();

const entries = (await Promise.all(puzzleFiles.map(loadPuzzle))).flat();
mkdirSync(join(import.meta.dir, "..", "src", "examples"), { recursive: true });
writeFileSync(OUTPUT_TMP_PATH, `${JSON.stringify(entries, null, 2)}\n`);
renameSync(OUTPUT_TMP_PATH, OUTPUT_PATH);
