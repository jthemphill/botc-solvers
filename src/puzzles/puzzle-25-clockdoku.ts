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

export const GIVEN_GRID: Array<Array<ClockdokuRole | undefined>> = [
  [undefined, undefined, "Recluse", "Saint", undefined, undefined, "Chef"],
  ["Investigator", undefined, undefined, "Chef", "Fortune Teller", undefined, "Poisoner"],
  ["Librarian", undefined, undefined, undefined, "Saint", "Empath", undefined],
  [undefined, "Recluse", undefined, "Imp", undefined, "Fortune Teller", undefined],
  [undefined, "Chef", "Librarian", undefined, undefined, undefined, "Investigator"],
  ["Fortune Teller", undefined, "Baron", "Empath", undefined, undefined, "Librarian"],
  ["Poisoner", undefined, undefined, "Fortune Teller", "Investigator", undefined, undefined],
];

export function solve(): ClockdokuGrid[] {
  const grid = GIVEN_GRID.map((row) => [...row]);
  const solutions: ClockdokuGrid[] = [];
  search(grid, solutions);
  return solutions;
}

function search(grid: Array<Array<ClockdokuRole | undefined>>, solutions: ClockdokuGrid[]): void {
  const next = nextCell(grid);
  if (next === undefined) {
    if (isCompleteGrid(grid)) solutions.push(grid.map((row) => [...row] as ClockdokuRole[]));
    return;
  }

  const [row, column, domain] = next;
  for (const role of domain) {
    grid[row]![column] = role;
    search(grid, solutions);
    grid[row]![column] = undefined;
  }
}

function nextCell(grid: Array<Array<ClockdokuRole | undefined>>): [number, number, ClockdokuRole[]] | undefined {
  let best: [number, number, ClockdokuRole[]] | undefined;
  for (let row = 0; row < 7; row += 1) {
    for (let column = 0; column < 7; column += 1) {
      if (grid[row]?.[column] !== undefined) continue;
      const domain = ROLES.filter((role) => {
        grid[row]![column] = role;
        const valid = isValidLine(grid[row]!) && isValidLine(grid.map((candidateRow) => candidateRow[column]));
        grid[row]![column] = undefined;
        return valid;
      });
      if (domain.length === 0) return [row, column, []];
      if (best === undefined || domain.length < best[2].length) best = [row, column, domain];
    }
  }
  return best;
}

function isCompleteGrid(grid: Array<Array<ClockdokuRole | undefined>>): boolean {
  return (
    grid.every((row) => isValidLine(row, true)) &&
    Array.from({ length: 7 }, (_ignored, column) => grid.map((row) => row[column])).every((column) =>
      isValidLine(column, true),
    )
  );
}

function isValidLine(line: Array<ClockdokuRole | undefined>, complete = false): boolean {
  const counts = new Map<ClockdokuRole, number>(ROLES.map((role) => [role, 0]));
  for (const role of line) if (role !== undefined) counts.set(role, (counts.get(role) ?? 0) + 1);
  if ([...counts.values()].some((count) => count > 1)) return false;
  if ((counts.get("Imp") ?? 0) > 1) return false;
  if ((counts.get("Baron") ?? 0) + (counts.get("Poisoner") ?? 0) > 1) return false;
  if ((counts.get("Baron") ?? 0) > 0 && (counts.get("Poisoner") ?? 0) > 0) return false;
  if ((counts.get("Baron") ?? 0) > 0 && ((counts.get("Saint") ?? 0) > 1 || (counts.get("Recluse") ?? 0) > 1))
    return false;
  if ((counts.get("Poisoner") ?? 0) > 0 && ((counts.get("Saint") ?? 0) > 0 || (counts.get("Recluse") ?? 0) > 0))
    return false;
  if (!complete) return true;
  if ((counts.get("Imp") ?? 0) !== 1) return false;
  if ((counts.get("Baron") ?? 0) + (counts.get("Poisoner") ?? 0) !== 1) return false;
  if ((counts.get("Baron") ?? 0) > 0) return (counts.get("Saint") ?? 0) === 1 && (counts.get("Recluse") ?? 0) === 1;
  return (counts.get("Saint") ?? 0) === 0 && (counts.get("Recluse") ?? 0) === 0;
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-25-clockdoku.ts")) {
  for (const solution of solve()) console.log(solution.map((row) => row.join(" | ")).join("\n"));
}
