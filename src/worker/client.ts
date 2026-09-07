import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { Solved, SolveRequest, SolveResponse } from "./protocol";

export interface SolverWorker {
  onmessage: ((event: MessageEvent<SolveResponse>) => void) | null;
  onerror: ((event: ErrorEvent) => void) | null;
  postMessage(request: SolveRequest): void;
  terminate(): void;
}

/**
 * The WASM solver uses one synchronous call in the worker.
 * To stop a request, stop its worker.
 * Use a new worker for the next request.
 */
export class SolverClient {
  private worker: SolverWorker | undefined;
  private pending: { id: number; resolve: (result: Solved) => void; reject: (error: Error) => void } | undefined;
  private counter = 0;
  constructor(
    private readonly createWorker: () => SolverWorker,
    private readonly busy: (value: boolean) => void,
  ) {}

  cancel(): void {
    const pending = this.pending;
    this.pending = undefined;
    if (pending) {
      this.worker?.terminate();
      this.worker = undefined;
      pending.reject(new DOMException("The solve was superseded.", "AbortError"));
      this.busy(false);
    }
  }
  dispose(): void {
    this.cancel();
    this.worker?.terminate();
    this.worker = undefined;
  }
  solve(doc: PuzzleDoc, limit?: number): Promise<Solved> {
    this.cancel();
    this.worker ??= this.createWorker();
    const worker = this.worker;
    const id = ++this.counter;
    this.busy(true);
    return new Promise((resolve, reject) => {
      this.pending = { id, resolve, reject };
      worker.onmessage = ({ data }) => {
        if (worker !== this.worker || this.pending?.id !== data.id) return;
        const pending = this.pending;
        this.pending = undefined;
        this.busy(false);
        if (data.type === "solved") pending.resolve(data);
        else pending.reject(new Error(data.message));
      };
      worker.onerror = (event) => {
        if (worker !== this.worker || this.pending?.id !== id) return;
        const pending = this.pending;
        this.pending = undefined;
        this.busy(false);
        worker.terminate();
        this.worker = undefined;
        pending.reject(new Error(event.message || "Solver worker failed."));
      };
      try {
        worker.postMessage({ type: "solve", id, doc, limit });
      } catch (error) {
        this.pending = undefined;
        this.busy(false);
        worker.terminate();
        this.worker = undefined;
        reject(error);
      }
    });
  }
}
