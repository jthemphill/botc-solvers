import { useCallback, useEffect, useRef, useState } from "react";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { SolverClient } from "../worker/client";
import type { Solved } from "../worker/protocol";

export function useSolver() {
  const clientRef = useRef<SolverClient | null>(null);
  const [busy, setBusy] = useState(false);
  useEffect(() => {
    const client = new SolverClient(
      () => new Worker(new URL("../worker/solver.worker.ts", import.meta.url), { type: "module" }),
      setBusy,
    );
    clientRef.current = client;
    return () => {
      client.dispose();
      clientRef.current = null;
    };
  }, []);
  const solve = useCallback(
    (doc: PuzzleDoc, limit?: number): Promise<Solved> =>
      clientRef.current?.solve(doc, limit) ?? Promise.reject(new Error("Worker not ready")),
    [],
  );
  const cancel = useCallback(() => clientRef.current?.cancel(), []);
  return { busy, solve, cancel };
}
