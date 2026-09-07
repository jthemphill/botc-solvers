import { beforeAll, expect, test } from "bun:test";
import { BOTCModel } from "./model";
import { roleByName } from "./roleRegistry";
import { KissatBackend, type SatBackend, validateSatWitness } from "./sat";
let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});
const gameWith = (solver: SatBackend) =>
  new BOTCModel(["A"], { characters: ["Chef", "Artist"].map(roleByName), backend: solver });

test("unknown is not reported as unsatisfiable", async () => {
  const game = gameWith({ solve: async () => ({ status: "unknown", sat: undefined, reason: "interrupted" }) });
  expect(await game.solve()).toMatchObject({ status: "unknown", complete: false, reason: "interrupted", worlds: [] });
  await expect(game.solveAll()).rejects.toThrow("interrupted");
});
test("bounded enumeration reports its projection and completion honestly", async () => {
  const game = gameWith(backend);
  expect(await game.solve({ limit: 1 })).toMatchObject({
    status: "sat",
    complete: false,
    stopped: "limit",
    projection: "initialCharacters",
  });
  const all = await game.solve();
  expect(all).toMatchObject({ status: "sat", complete: true, stopped: "exhausted", metrics: { backendCalls: 3 } });
  expect(all.worlds).toHaveLength(2);
  expect(game.finalize()).toBe(game.finalize());
  expect(() => game.fixActual("A", "Chef")).toThrow("finalized");
  expect(() => game.addTimedDrunkSource("A", ["night_3"], 1)).toThrow("finalized");
  expect(() => game.newBool("too_late")).toThrow("finalized");
});
test("invalid backend witnesses fail with clause provenance", () => {
  expect(() =>
    validateSatWitness(
      { variableCount: 1, clauses: [[1]], origins: [{ kind: "fact", id: "observed-role" }] },
      new Set(),
    ),
  ).toThrow("observed-role");
});
test("sequential direct cardinality stays polynomial", () => {
  const game = gameWith(backend);
  const values = Array.from({ length: 20 }, (_, i) => game.newBool(`x${i}`));
  game.addExactlyN(values, 10);
  expect(game.finalize().clauses.length).toBeLessThan(1500);
});
