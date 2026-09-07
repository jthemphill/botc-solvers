import { validateSatWitness, type SatProblem, type SatBackend } from "./sat";
import { validateChoiceWitness } from "./actions";
import { validateTraceWitness } from "./trace";
import type { World } from "./world";

export interface SolveReport {
  readonly status: "sat" | "unsat" | "unknown";
  readonly complete: boolean;
  readonly stopped: "exhausted" | "limit" | "unknown";
  readonly reason?: string;
  readonly projection: "initialCharacters";
  readonly worlds: readonly World[];
  readonly metrics: {
    readonly variables: number;
    readonly clauses: number;
    readonly backendCalls: number;
    readonly finalizeMs: number;
    readonly solveMs: number;
  };
}

export async function enumerateWorlds(
  problem: SatProblem,
  backend: SatBackend,
  projection: readonly number[],
  decode: (model: ReadonlySet<number>) => World,
  finalizeMs: number,
  limit?: number,
): Promise<SolveReport> {
  const started = performance.now();
  const clauses = [...problem.clauses];
  const worlds: World[] = [];
  let backendCalls = 0;
  let stopped: SolveReport["stopped"] = "limit";
  let reason: string | undefined;
  while (limit === undefined || worlds.length < limit) {
    backendCalls += 1;
    const current = { ...problem, clauses };
    const result = await backend.solve(current);
    if (result.status === "unknown") {
      stopped = "unknown";
      reason = result.reason;
      break;
    }
    if (!result.sat) {
      stopped = "exhausted";
      break;
    }
    validateSatWitness(current, result.model);
    const world = decode(result.model);
    const errors = [...validateTraceWitness(world.trace!), ...world.actions.flatMap(validateChoiceWitness)];
    if (errors.length > 0) throw new Error(errors.join("\n"));
    worlds.push(world);
    clauses.push(projection.filter((variable) => result.model.has(variable)).map((variable) => -variable));
  }
  return {
    status: stopped === "unknown" ? "unknown" : worlds.length > 0 ? "sat" : "unsat",
    complete: stopped === "exhausted",
    stopped,
    reason,
    projection: "initialCharacters",
    worlds,
    metrics: {
      variables: problem.variableCount,
      clauses: problem.clauses.length,
      backendCalls,
      finalizeMs,
      solveMs: performance.now() - started,
    },
  };
}
