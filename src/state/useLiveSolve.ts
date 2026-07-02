import { useEffect, useRef, useState, type Dispatch } from "react";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { SolveRequest, SolveResponse } from "../worker/protocol";
import type { PuzzleAction } from "./puzzleDoc";

export const LIVE_SOLVE_DEBOUNCE_MS = 400;
export const LIVE_SOLVE_WORLD_LIMIT = 200;

export interface LiveSolve {
  readonly solving: boolean;
  readonly ready: boolean;
}

function createWorker(): Worker {
  return new Worker(new URL("../worker/solver.worker.ts", import.meta.url), { type: "module" });
}

export function canSolve(doc: PuzzleDoc): boolean {
  return doc.players.length > 0 && doc.script.length > 0;
}

/**
 * Re-solves the puzzle whenever the doc settles for LIVE_SOLVE_DEBOUNCE_MS.
 * A solve that is superseded by a newer doc is cancelled by terminating the
 * worker (the SAT search blocks the worker thread, so termination is the only
 * way to interrupt it).
 */
export function useLiveSolve(doc: PuzzleDoc, dispatch: Dispatch<PuzzleAction>): LiveSolve {
  const workerRef = useRef<Worker | undefined>(undefined);
  const inFlightRef = useRef<number | undefined>(undefined);
  const counterRef = useRef(0);
  const [solving, setSolving] = useState(false);
  const ready = canSolve(doc);

  useEffect(() => {
    return () => {
      workerRef.current?.terminate();
      workerRef.current = undefined;
      inFlightRef.current = undefined;
    };
  }, []);

  useEffect(() => {
    if (!ready) {
      if (inFlightRef.current !== undefined) {
        workerRef.current?.terminate();
        workerRef.current = undefined;
        inFlightRef.current = undefined;
      }
      setSolving(false);
      return;
    }

    const timer = setTimeout(() => {
      if (inFlightRef.current !== undefined) {
        workerRef.current?.terminate();
        workerRef.current = undefined;
      }
      if (workerRef.current === undefined) workerRef.current = createWorker();
      workerRef.current.onmessage = (ev: MessageEvent<SolveResponse>) => {
        if (ev.data.id !== inFlightRef.current) return;
        inFlightRef.current = undefined;
        setSolving(false);
        if (ev.data.type === "solved") {
          dispatch({ type: "solve", status: "succeeded", doc, worlds: ev.data.worlds });
        } else {
          dispatch({ type: "solve", status: "failed", doc, message: ev.data.message });
        }
      };
      counterRef.current += 1;
      const id = counterRef.current;
      inFlightRef.current = id;
      setSolving(true);
      dispatch({ type: "solve", status: "started", doc });
      const req: SolveRequest = { type: "solve", id, doc, limit: LIVE_SOLVE_WORLD_LIMIT };
      workerRef.current.postMessage(req);
    }, LIVE_SOLVE_DEBOUNCE_MS);

    return () => clearTimeout(timer);
  }, [doc, dispatch, ready]);

  return { solving, ready };
}
