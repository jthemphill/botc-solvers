import { buildFromDoc } from "../builders/buildFromDoc";
import type { World } from "../model/model";
import type { SerializableWorld, SolveRequest, SolveResponse } from "./protocol";
import { loadKissat } from "./wasmLoader";

function serializeWorld(w: World): SerializableWorld {
  return {
    players: [...w.players],
    actual: [...w.actual.entries()],
    apparent: [...w.apparent.entries()],
    poisoned: [...w.poisoned],
    drunk: [...w.drunk],
  };
}

interface WorkerSelf {
  onmessage: ((ev: MessageEvent<SolveRequest>) => void) | null;
  postMessage(data: SolveResponse): void;
}

const worker = globalThis as unknown as WorkerSelf;

worker.onmessage = async (ev: MessageEvent<SolveRequest>) => {
  const { id, doc, limit } = ev.data;
  try {
    const backend = await loadKissat();
    const game = buildFromDoc(doc, backend);
    const worlds = await game.solveAll({ limit });
    const payload: SolveResponse = { type: "solved", id, worlds: worlds.map(serializeWorld) };
    worker.postMessage(payload);
  } catch (e) {
    const message = e instanceof Error ? `${e.message}\n${e.stack ?? ""}` : String(e);
    worker.postMessage({ type: "error", id, message } satisfies SolveResponse);
  }
};
