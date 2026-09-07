import { expect, test } from "bun:test";
import { SolverClient, type SolverWorker } from "./client";
import type { Solved, SolveRequest, SolveResponse } from "./protocol";
const doc = { players: ["A"], script: ["Chef"], claims: [] };
const result: Solved = {
  worlds: [],
  summary: {
    status: "unsat",
    complete: true,
    stopped: "exhausted",
    projection: "initialCharacters",
    buildMs: 0,
    metrics: { variables: 0, clauses: 1, backendCalls: 1, finalizeMs: 0, solveMs: 0 },
  },
};
class FakeWorker implements SolverWorker {
  onmessage: SolverWorker["onmessage"] = null;
  onerror: SolverWorker["onerror"] = null;
  stopped = false;
  request?: SolveRequest;
  postMessage(request: SolveRequest) {
    this.request = request;
  }
  terminate() {
    this.stopped = true;
  }
  complete() {
    this.onmessage?.({ data: { type: "solved", id: this.request!.id, ...result } } as MessageEvent<SolveResponse>);
  }
}
test("superseding a synchronous WASM job terminates it and ignores its stale reply", async () => {
  const workers: FakeWorker[] = [],
    busy: boolean[] = [];
  const client = new SolverClient(
    () => {
      const worker = new FakeWorker();
      workers.push(worker);
      return worker;
    },
    (value) => busy.push(value),
  );
  const first = client.solve(doc).catch((error: Error) => error.name);
  const second = client.solve(doc);
  expect(await first).toBe("AbortError");
  expect(workers[0]!.stopped).toBe(true);
  workers[0]!.complete();
  expect(busy.at(-1)).toBe(true);
  workers[1]!.complete();
  expect(await second).toMatchObject(result);
  expect(busy.at(-1)).toBe(false);
  client.dispose();
  expect(workers[1]!.stopped).toBe(true);
});
test("worker failure rejects the request and the next solve can recover", async () => {
  const workers: FakeWorker[] = [];
  const client = new SolverClient(
    () => {
      const worker = new FakeWorker();
      workers.push(worker);
      return worker;
    },
    () => {},
  );
  const failure = client.solve(doc).catch((error: Error) => error.message);
  workers[0]!.onerror?.({ message: "runtime failure" } as ErrorEvent);
  expect(await failure).toBe("runtime failure");
  expect(workers[0]!.stopped).toBe(true);
  const next = client.solve(doc);
  workers[1]!.complete();
  await next;
  client.dispose();
});
