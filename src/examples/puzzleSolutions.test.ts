import { beforeAll, describe, expect, test } from "bun:test";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { buildFromDoc } from "../builders/buildFromDoc";
import type { Timing, World } from "../model/model";
import { KissatBackend, type SatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";
import { PUZZLE_EXAMPLES } from "./puzzleCatalog";

const SOLUTION_FILE_SUFFIX = ".solutions.json";
const EXAMPLES_DIR = fileURLToPath(new URL(".", import.meta.url));

interface SerializedWorld {
  readonly roles: Readonly<Record<string, string>>;
  readonly poisoned?: Readonly<Record<Timing, readonly string[]>>;
  readonly drunk?: readonly string[];
  readonly drunkByTiming?: Readonly<Record<Timing, readonly string[]>>;
}

interface PuzzleSolutionsFile {
  readonly solutions: readonly SerializedWorld[];
}

interface PuzzleSolutions extends PuzzleSolutionsFile {
  readonly id: string;
  readonly fileName: string;
}

interface PuzzleSolutionCase {
  readonly id: string;
  readonly data: unknown;
  readonly solutions: readonly SerializedWorld[];
}

const SOLUTION_TIMEOUT_MS = 120_000;

const PUZZLE_SOLUTIONS = loadPuzzleSolutions();
const SOLUTIONS_BY_ID = new Map(PUZZLE_SOLUTIONS.map((solutions) => [solutions.id, solutions]));

const PUZZLE_SOLUTION_CASES: PuzzleSolutionCase[] = PUZZLE_EXAMPLES.flatMap((example): PuzzleSolutionCase[] => {
  if (example.id === "intro") return [];
  const puzzleSolutions = SOLUTIONS_BY_ID.get(example.id);
  if (puzzleSolutions === undefined) throw new Error(`Missing solution file for ${example.id}`);
  return [{ id: example.id, data: example.data, solutions: puzzleSolutions.solutions }];
});

describe("JSON puzzle solutions", () => {
  let backend: SatBackend;

  beforeAll(async () => {
    backend = await KissatBackend.create();
  });

  test("every numbered JSON puzzle has solution coverage", () => {
    const catalogIds = PUZZLE_EXAMPLES.map((example) => example.id).filter((id) => id !== "intro");
    const solutionIds = PUZZLE_SOLUTIONS.map((solutions) => solutions.id);

    expect(new Set(catalogIds)).toEqual(new Set(solutionIds));
  });

  test("solution data is stably sorted", () => {
    for (const puzzleSolutions of PUZZLE_SOLUTIONS) {
      expect(JSON.stringify(puzzleSolutionsFile(puzzleSolutions)), puzzleSolutions.fileName).toBe(
        JSON.stringify(canonicalPuzzleSolutionsFile(puzzleSolutions)),
      );
    }
  });

  test.each(PUZZLE_SOLUTION_CASES)(
    "$id solution set comes from JSON doc",
    async ({ id, data, solutions }) => {
      const doc = validatePuzzleDoc(data);
      const worlds = await buildFromDoc(doc, backend).solveAll();

      expect(serializeWorlds(worlds, doc.players), id).toEqual(solutions);
    },
    SOLUTION_TIMEOUT_MS,
  );
});

function serializeWorlds(worlds: readonly World[], players: readonly string[]): readonly SerializedWorld[] {
  return worlds.map((world) => serializeWorld(world, players)).sort(compareSerializedWorlds);
}

function serializeWorld(world: World, players: readonly string[]): SerializedWorld {
  const poisoned = serializeTimedPlayers(world.poisonedByTiming, players);
  const drunkByTiming = serializeTimedPlayers(world.drunkByTiming, players);
  const drunk = players.filter((player) => world.drunk.has(player)).sort(compareStrings);

  return {
    roles: sortRecord(Object.fromEntries(players.map((player) => [player, world.actualRole(player)]))),
    ...(Object.keys(poisoned).length > 0 ? { poisoned } : {}),
    ...(drunk.length > 0 ? { drunk } : {}),
    ...(Object.keys(drunkByTiming).length > 0 ? { drunkByTiming } : {}),
  };
}

function serializeTimedPlayers(
  playersByTiming: ReadonlyMap<string, ReadonlySet<string>>,
  players: readonly string[],
): Record<Timing, readonly string[]> {
  return Object.fromEntries(
    [...playersByTiming.entries()]
      .filter(([, matchingPlayers]) => matchingPlayers.size > 0)
      .sort(([left], [right]) => compareTimings(left as Timing, right as Timing))
      .map(([timing, matchingPlayers]) => [timing, [...matchingPlayers].sort(compareStrings)]),
  ) as Record<Timing, readonly string[]>;
}

function loadPuzzleSolutions(): readonly PuzzleSolutions[] {
  return readdirSync(EXAMPLES_DIR)
    .filter((fileName) => fileName.endsWith(SOLUTION_FILE_SUFFIX))
    .sort((left, right) => left.localeCompare(right))
    .map((fileName) => {
      const id = fileName.slice(0, -SOLUTION_FILE_SUFFIX.length);
      const rawText = readFileSync(join(EXAMPLES_DIR, fileName), "utf8");
      const parsed = JSON.parse(rawText) as unknown;

      return {
        id,
        fileName,
        ...parsePuzzleSolutionsFile(parsed, fileName),
      };
    });
}

function puzzleSolutionsFile({ solutions }: PuzzleSolutionsFile): PuzzleSolutionsFile {
  return { solutions };
}

function parsePuzzleSolutionsFile(input: unknown, path: string): PuzzleSolutionsFile {
  const value = expectRecord(input, path);
  expectOnlyKeys(value, ["solutions"], path);
  const solutionsInput = value["solutions"];

  if (!Array.isArray(solutionsInput) || solutionsInput.length === 0) {
    throw new Error(`Expected non-empty array at ${path}.solutions`);
  }

  return {
    solutions: solutionsInput.map((solution, index) => parseSerializedWorld(solution, `${path}.solutions[${index}]`)),
  };
}

function parseSerializedWorld(input: unknown, path: string): SerializedWorld {
  const value = expectRecord(input, path);
  expectOnlyKeys(value, ["roles", "poisoned", "drunk", "drunkByTiming"], path);

  return {
    roles: parseStringRecord(value["roles"], `${path}.roles`),
    ...parseOptionalTimedPlayers(value["poisoned"], `${path}.poisoned`, "poisoned"),
    ...parseOptionalStringArray(value["drunk"], `${path}.drunk`, "drunk"),
    ...parseOptionalTimedPlayers(value["drunkByTiming"], `${path}.drunkByTiming`, "drunkByTiming"),
  };
}

function parseStringRecord(input: unknown, path: string): Record<string, string> {
  const value = expectRecord(input, path);
  for (const [key, entry] of Object.entries(value)) {
    if (typeof entry !== "string") throw new Error(`Expected string at ${path}.${key}`);
  }
  return value as Record<string, string>;
}

function parseOptionalTimedPlayers(
  input: unknown,
  path: string,
  field: "poisoned" | "drunkByTiming",
): Pick<SerializedWorld, typeof field> | Record<string, never> {
  if (input === undefined) return {};
  const value = expectRecord(input, path);
  const timings = Object.fromEntries(
    Object.entries(value).map(([timing, players]) => [
      expectTiming(timing, `${path}.${timing}`),
      expectStringArray(players, `${path}.${timing}`),
    ]),
  ) as Record<Timing, readonly string[]>;
  return { [field]: timings };
}

function parseOptionalStringArray(
  input: unknown,
  path: string,
  field: "drunk",
): Pick<SerializedWorld, "drunk"> | Record<string, never> {
  if (input === undefined) return {};
  return { [field]: expectStringArray(input, path) };
}

function canonicalPuzzleSolutionsFile(file: PuzzleSolutionsFile): PuzzleSolutionsFile {
  return { solutions: [...file.solutions].map(canonicalWorld).sort(compareSerializedWorlds) };
}

function canonicalWorld(world: SerializedWorld): SerializedWorld {
  return {
    roles: sortRecord(world.roles),
    ...(world.poisoned !== undefined ? { poisoned: sortTimedPlayers(world.poisoned) } : {}),
    ...(world.drunk !== undefined ? { drunk: [...world.drunk].sort(compareStrings) } : {}),
    ...(world.drunkByTiming !== undefined ? { drunkByTiming: sortTimedPlayers(world.drunkByTiming) } : {}),
  };
}

function sortRecord<T>(record: Readonly<Record<string, T>>): Record<string, T> {
  return Object.fromEntries(Object.entries(record).sort(([left], [right]) => left.localeCompare(right))) as Record<
    string,
    T
  >;
}

function sortTimedPlayers(record: Readonly<Record<Timing, readonly string[]>>): Record<Timing, readonly string[]> {
  return Object.fromEntries(
    Object.entries(record)
      .sort(([left], [right]) => compareTimings(left as Timing, right as Timing))
      .map(([timing, players]) => [timing, [...players].sort(compareStrings)]),
  ) as Record<Timing, readonly string[]>;
}

function compareSerializedWorlds(left: SerializedWorld, right: SerializedWorld): number {
  return JSON.stringify(left).localeCompare(JSON.stringify(right));
}

function compareTimings(left: Timing, right: Timing): number {
  return timingSortValue(left) - timingSortValue(right) || left.localeCompare(right);
}

function timingSortValue(timing: Timing): number {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) return Number.MAX_SAFE_INTEGER;

  return Number(match[2] ?? Number.MAX_SAFE_INTEGER) * 2 + (match[1] === "day" ? 1 : 0);
}

function compareStrings(left: string, right: string): number {
  return left.localeCompare(right);
}

function expectRecord(input: unknown, path: string): Record<string, unknown> {
  if (typeof input !== "object" || input === null || Array.isArray(input)) {
    throw new Error(`Expected object at ${path}`);
  }
  return input as Record<string, unknown>;
}

function expectOnlyKeys(input: Readonly<Record<string, unknown>>, allowedKeys: readonly string[], path: string): void {
  const extraKeys = Object.keys(input).filter((key) => !allowedKeys.includes(key));
  if (extraKeys.length > 0) throw new Error(`Unexpected key at ${path}: ${extraKeys[0]}`);
}

function expectStringArray(input: unknown, path: string): readonly string[] {
  if (!Array.isArray(input)) throw new Error(`Expected array at ${path}`);
  for (const [index, entry] of input.entries()) {
    if (typeof entry !== "string") throw new Error(`Expected string at ${path}[${index}]`);
  }
  return input;
}

function expectTiming(input: unknown, path: string): Timing {
  if (typeof input !== "string" || !/^(night|day)_\d+$/.test(input)) throw new Error(`Expected timing at ${path}`);
  return input as Timing;
}
