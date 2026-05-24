import { useCallback, useEffect, useRef, useState } from "react";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { SerializableWorld, SolveRequest, SolveResponse } from "../worker/protocol";

interface Pending {
  readonly resolve: (worlds: readonly SerializableWorld[]) => void;
  readonly reject: (error: Error) => void;
}

export interface UseSolver {
  readonly busy: boolean;
  readonly solve: (doc: PuzzleDoc, limit?: number) => Promise<readonly SerializableWorld[]>;
}

export function useSolver(): UseSolver {
  const workerRef = useRef<Worker | null>(null);
  const pendingRef = useRef<Map<number, Pending>>(new Map());
  const counterRef = useRef(0);
  const [busy, setBusy] = useState(false);

  useEffect(() => {
    const worker = new Worker(new URL("../worker/solver.worker.ts", import.meta.url), { type: "module" });
    worker.onmessage = (ev: MessageEvent<SolveResponse>) => {
      const pending = pendingRef.current.get(ev.data.id);
      if (pending === undefined) return;
      pendingRef.current.delete(ev.data.id);
      if (ev.data.type === "solved") pending.resolve(ev.data.worlds);
      else pending.reject(new Error(ev.data.message));
      if (pendingRef.current.size === 0) setBusy(false);
    };
    workerRef.current = worker;
    return () => {
      worker.terminate();
      workerRef.current = null;
    };
  }, []);

  const solve = useCallback((doc: PuzzleDoc, limit?: number): Promise<readonly SerializableWorld[]> => {
    if (!workerRef.current) return Promise.reject(new Error("Worker not ready"));
    counterRef.current += 1;
    const id = counterRef.current;
    setBusy(true);
    return new Promise<readonly SerializableWorld[]>((resolve, reject) => {
      pendingRef.current.set(id, { resolve, reject });
      const req: SolveRequest = { type: "solve", id, doc, limit };
      workerRef.current?.postMessage(req);
    });
  }, []);

  return { busy, solve };
}
