import { KissatBackend, type SatBackend, type Clause } from "../sat";

export const ROLES = [
  "Imp",
  "Baron",
  "Poisoner",
  "Saint",
  "Recluse",
  "Librarian",
  "Investigator",
  "Chef",
  "Empath",
  "Fortune Teller",
] as const;

export type ClockdokuRole = (typeof ROLES)[number];
export type ClockdokuGrid = ClockdokuRole[][];
type Cell = readonly [row: number, column: number];

export const GIVEN_GRID: Array<Array<ClockdokuRole | undefined>> = [
  [undefined, undefined, "Recluse", "Saint", undefined, undefined, "Chef"],
  ["Investigator", undefined, undefined, "Chef", "Fortune Teller", undefined, "Poisoner"],
  ["Librarian", undefined, undefined, undefined, "Saint", "Empath", undefined],
  [undefined, "Recluse", undefined, "Imp", undefined, "Fortune Teller", undefined],
  [undefined, "Chef", "Librarian", undefined, undefined, undefined, "Investigator"],
  ["Fortune Teller", undefined, "Baron", "Empath", undefined, undefined, "Librarian"],
  ["Poisoner", undefined, undefined, "Fortune Teller", "Investigator", undefined, undefined],
];

const GRID_SIZE = 7;
const VARIABLE_COUNT = GRID_SIZE * GRID_SIZE * ROLES.length;

export async function solve(backend?: SatBackend): Promise<ClockdokuGrid[]> {
  const satBackend = backend ?? (await KissatBackend.create());
  const problem = buildProblem();
  const clauses = [...problem.clauses];
  const solutions: ClockdokuGrid[] = [];

  while (true) {
    const result = await satBackend.solve({ variableCount: problem.variableCount, clauses });
    if (!result.sat) break;
    if (result.model === undefined) throw new Error("Kissat returned SAT without a model.");

    const solution = decodeModel(result.model);
    solutions.push(solution);
    clauses.push(
      solution.flatMap((row, rowIndex) => row.map((role, columnIndex) => -variableFor(rowIndex, columnIndex, role))),
    );
  }

  return solutions;
}

function buildProblem(): { readonly variableCount: number; readonly clauses: Clause[] } {
  const clauses: Clause[] = [];

  for (let row = 0; row < GRID_SIZE; row += 1) {
    for (let column = 0; column < GRID_SIZE; column += 1) {
      addExactlyOne(
        clauses,
        ROLES.map((role) => variableFor(row, column, role)),
      );
      const given = GIVEN_GRID[row]?.[column];
      if (given !== undefined) clauses.push([variableFor(row, column, given)]);
    }
  }

  for (let index = 0; index < GRID_SIZE; index += 1) {
    addLineConstraints(
      clauses,
      Array.from({ length: GRID_SIZE }, (_ignored, column) => [index, column] as const),
    );
    addLineConstraints(
      clauses,
      Array.from({ length: GRID_SIZE }, (_ignored, row) => [row, index] as const),
    );
  }

  return { variableCount: VARIABLE_COUNT, clauses };
}

function addLineConstraints(clauses: Clause[], cells: readonly Cell[]): void {
  for (const role of ROLES)
    addAtMostOne(
      clauses,
      cells.map(([row, column]) => variableFor(row, column, role)),
    );

  clauses.push(cells.map(([row, column]) => variableFor(row, column, "Imp")));

  const barons = cells.map(([row, column]) => variableFor(row, column, "Baron"));
  const poisoners = cells.map(([row, column]) => variableFor(row, column, "Poisoner"));
  const saints = cells.map(([row, column]) => variableFor(row, column, "Saint"));
  const recluses = cells.map(([row, column]) => variableFor(row, column, "Recluse"));

  clauses.push([...barons, ...poisoners]);
  for (const baron of barons) {
    for (const poisoner of poisoners) clauses.push([-baron, -poisoner]);
    clauses.push([-baron, ...saints]);
    clauses.push([-baron, ...recluses]);
  }

  for (const poisoner of poisoners) {
    for (const saint of saints) clauses.push([-poisoner, -saint]);
    for (const recluse of recluses) clauses.push([-poisoner, -recluse]);
  }
}

function addExactlyOne(clauses: Clause[], variables: readonly number[]): void {
  clauses.push([...variables]);
  addAtMostOne(clauses, variables);
}

function addAtMostOne(clauses: Clause[], variables: readonly number[]): void {
  for (let left = 0; left < variables.length; left += 1) {
    for (let right = left + 1; right < variables.length; right += 1) {
      clauses.push([-(variables[left] as number), -(variables[right] as number)]);
    }
  }
}

function decodeModel(model: ReadonlySet<number>): ClockdokuGrid {
  return Array.from({ length: GRID_SIZE }, (_ignored, row) =>
    Array.from({ length: GRID_SIZE }, (_alsoIgnored, column) => {
      const matching = ROLES.filter((role) => model.has(variableFor(row, column, role)));
      if (matching.length !== 1) throw new Error(`Expected exactly one role at ${row}, ${column}.`);
      return matching[0] as ClockdokuRole;
    }),
  );
}

function variableFor(row: number, column: number, role: ClockdokuRole): number {
  return (row * GRID_SIZE + column) * ROLES.length + roleIndex(role) + 1;
}

function roleIndex(role: ClockdokuRole): number {
  const index = ROLES.indexOf(role);
  if (index === -1) throw new Error(`Unknown role: ${role}`);
  return index;
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-25-clockdoku.ts")) {
  for (const solution of await solve()) console.log(solution.map((row) => row.join(" | ")).join("\n"));
}
