export type Literal = number;
export type Clause = readonly Literal[];

export interface ConstraintOrigin {
  readonly kind: "rule" | "fact" | "assumption";
  readonly id: string;
  readonly expression?: string;
  readonly span?: { readonly start: number; readonly end: number };
  readonly source?: string;
}

export interface SatProblem {
  readonly variableCount: number;
  readonly clauses: readonly Clause[];
  readonly origins?: readonly ConstraintOrigin[];
}

export type SatResult =
  | { readonly status: "sat"; readonly sat: true; readonly model: ReadonlySet<number> }
  | { readonly status: "unsat"; readonly sat: false }
  | { readonly status: "unknown"; readonly sat: undefined; readonly reason: string };

export interface SatBackend {
  solve(problem: SatProblem): Promise<SatResult>;
}

interface KissatEmscriptenModule {
  calledRun?: boolean;
  _kissat_add(solverPtr: number, literalOrZero: number): void;
  _kissat_init(): number;
  _kissat_release(solverPtr: number): void;
  _kissat_solve(solverPtr: number): number;
  _kissat_value(solverPtr: number, variable: number): number;
  ccall(ident: string, returnType: "number", argTypes: readonly string[], args: readonly (number | string)[]): number;
  ccall(ident: string, returnType: null, argTypes: readonly string[], args: readonly (number | string)[]): null;
}

class KissatSolver {
  private readonly solverPtr: number;

  constructor(private readonly runtime: KissatEmscriptenModule) {
    this.solverPtr = runtime._kissat_init();
    this.setOption("quiet", 1);
  }

  addClause(clause: readonly number[]): void {
    for (const literal of clause) this.add(literal);
    this.add(0);
  }

  solve(): boolean | undefined {
    const result = this.runtime._kissat_solve(this.solverPtr);
    if (result === 10) return true;
    if (result === 20) return false;
    return undefined;
  }

  positiveModel(variableCount: number): ReadonlySet<number> {
    const model = new Set<number>();
    for (let variable = 1; variable <= variableCount; variable += 1) {
      if (this.runtime._kissat_value(this.solverPtr, variable) > 0) model.add(variable);
    }
    return model;
  }

  release(): void {
    this.runtime._kissat_release(this.solverPtr);
  }

  private add(literalOrZero: number): void {
    this.runtime._kissat_add(this.solverPtr, literalOrZero);
  }

  private setOption(name: string, value: number): void {
    this.runtime.ccall("kissat_set_option", null, ["number", "string", "number"], [this.solverPtr, name, value]);
  }
}

async function waitForRuntime(runtime: KissatEmscriptenModule): Promise<void> {
  while (runtime.calledRun !== true) {
    await new Promise((resolve) => setTimeout(resolve, 1));
  }
}

export class KissatBackend implements SatBackend {
  private constructor(private readonly runtime: KissatEmscriptenModule) {}

  static async create(): Promise<KissatBackend> {
    const runtime = (await import("../../vendor/kissat-js/kissat-emscripten")).default as KissatEmscriptenModule;
    await waitForRuntime(runtime);
    return new KissatBackend(runtime);
  }

  async solve(problem: SatProblem): Promise<SatResult> {
    const solver = new KissatSolver(this.runtime);
    try {
      for (const clause of problem.clauses) solver.addClause(clause);
      const sat = solver.solve();
      if (sat === undefined)
        return { status: "unknown", sat: undefined, reason: "Kissat did not complete the search." };
      if (!sat) return { status: "unsat", sat: false };
      return { status: "sat", sat: true, model: solver.positiveModel(problem.variableCount) };
    } finally {
      solver.release();
    }
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

/** Make sure that each clause in the supplied problem is true in the SAT witness. */
export function validateSatWitness(problem: SatProblem, model: ReadonlySet<number>): void {
  for (const variable of model)
    if (!Number.isInteger(variable) || variable < 1 || variable > problem.variableCount)
      throw new Error(`Backend returned an invalid variable: ${variable}.`);
  for (const [index, clause] of problem.clauses.entries()) {
    if (!clause.some((literal) => model.has(Math.abs(literal)) === literal > 0)) {
      const origin = problem.origins?.[index];
      throw new Error(`Invalid SAT witness at clause ${index + 1}${origin ? ` (${origin.kind}: ${origin.id})` : ""}.`);
    }
  }
}
