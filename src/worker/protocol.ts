import type { PuzzleDoc } from "../schema/puzzleDoc";

export interface SolveRequest {
  readonly type: "solve";
  readonly id: number;
  readonly doc: PuzzleDoc;
  readonly limit?: number;
}

export interface SerializableWorld {
  readonly players: readonly string[];
  readonly actual: ReadonlyArray<readonly [string, string]>;
  readonly apparent: ReadonlyArray<readonly [string, string]>;
  readonly poisoned: readonly string[];
  readonly drunk: readonly string[];
}

export type SolveResponse =
  | { readonly type: "solved"; readonly id: number; readonly worlds: readonly SerializableWorld[] }
  | { readonly type: "error"; readonly id: number; readonly message: string };
