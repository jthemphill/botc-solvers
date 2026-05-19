export type Literal = number;
export type Clause = readonly Literal[];

export interface SatProblem {
  readonly variableCount: number;
  readonly clauses: readonly Clause[];
}

export interface SatResult {
  readonly sat: boolean;
  readonly model?: ReadonlySet<number>;
}

export interface SatBackend {
  solve(problem: SatProblem): Promise<SatResult>;
}

function litValue(lit: Literal, assignment: Int8Array): boolean | undefined {
  const value = assignment[Math.abs(lit)];
  if (value === 0) return undefined;
  return lit > 0 ? value === 1 : value === -1;
}

function chooseVariable(variableCount: number, assignment: Int8Array): number | undefined {
  for (let variable = 1; variable <= variableCount; variable += 1) {
    if (assignment[variable] === 0) return variable;
  }
  return undefined;
}

function propagate(clauses: readonly Clause[], assignment: Int8Array): boolean {
  let changed = true;
  while (changed) {
    changed = false;
    for (const clause of clauses) {
      let unassigned: Literal | undefined;
      let unassignedCount = 0;
      let satisfied = false;
      for (const lit of clause) {
        const value = litValue(lit, assignment);
        if (value === true) {
          satisfied = true;
          break;
        }
        if (value === undefined) {
          unassigned = lit;
          unassignedCount += 1;
        }
      }
      if (satisfied) continue;
      if (unassignedCount === 0) return false;
      if (unassignedCount === 1 && unassigned !== undefined) {
        assignment[Math.abs(unassigned)] = unassigned > 0 ? 1 : -1;
        changed = true;
      }
    }
  }
  return true;
}

function search(variableCount: number, clauses: readonly Clause[], assignment: Int8Array): Int8Array | undefined {
  if (!propagate(clauses, assignment)) return undefined;
  const variable = chooseVariable(variableCount, assignment);
  if (variable === undefined) return assignment;

  for (const value of [1, -1] as const) {
    const next = new Int8Array(assignment);
    next[variable] = value;
    const result = search(variableCount, clauses, next);
    if (result !== undefined) return result;
  }
  return undefined;
}

export class DpllBackend implements SatBackend {
  async solve(problem: SatProblem): Promise<SatResult> {
    const assignment = search(problem.variableCount, problem.clauses, new Int8Array(problem.variableCount + 1));
    if (assignment === undefined) return { sat: false };
    const model = new Set<number>();
    for (let variable = 1; variable <= problem.variableCount; variable += 1) {
      if (assignment[variable] === 1) model.add(variable);
    }
    return { sat: true, model };
  }
}

export function negate(lit: Literal): Literal {
  return -lit;
}

export function combinations<T>(items: readonly T[], size: number): T[][] {
  if (size < 0) return [];
  if (size === 0) return [[]];
  if (size > items.length) return [];
  const result: T[][] = [];
  const current: T[] = [];
  const visit = (start: number): void => {
    if (current.length === size) {
      result.push([...current]);
      return;
    }
    for (let index = start; index <= items.length - (size - current.length); index += 1) {
      current.push(items[index] as T);
      visit(index + 1);
      current.pop();
    }
  };
  visit(0);
  return result;
}
