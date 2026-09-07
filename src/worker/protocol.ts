import type { SolveReport } from "../model/model";
import type { TraceWitness } from "../model/trace";
import type { ChoiceWitness } from "../model/actions";
import type { PuzzleDoc } from "../schema/puzzleDoc";

export interface SolveRequest {
  readonly type: "solve";
  readonly id: number;
  readonly doc: PuzzleDoc;
  readonly limit?: number;
}

export interface SerializableWorld {
  readonly trace?: TraceWitness;
  readonly actions?: readonly ChoiceWitness[];
  readonly actual: ReadonlyArray<readonly [string, string]>;
  readonly apparent: ReadonlyArray<readonly [string, string]>;
  readonly poisoned: readonly string[];
  readonly drunk: readonly string[];
}

export type SolveSummary = Omit<SolveReport, "worlds"> & {
  readonly buildMs: number;
};
export interface Solved {
  readonly worlds: readonly SerializableWorld[];
  readonly summary: SolveSummary;
}

export type SolveResponse =
  | ({ readonly type: "solved"; readonly id: number } & Solved)
  | { readonly type: "error"; readonly id: number; readonly message: string };
