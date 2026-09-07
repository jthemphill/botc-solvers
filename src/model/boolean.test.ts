import { beforeAll, expect, test } from "bun:test";
import { BooleanConstraints } from "./boolean";
import { select } from "./actions";
import { KissatBackend, validateSatWitness } from "./sat";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

test("shared selection requires one active target and no inactive targets", async () => {
  for (const active of [false, true])
    for (let mask = 0; mask < 8; mask += 1) {
      const game = new BooleanConstraints();
      const targets = select(game, ["A", "B", "C"], game.constantBool(active, "active"), "target", 1);
      [...targets.values()].forEach((target, index) => game.addTruth(mask & (1 << index) ? target : target.not()));
      const selected = [0, 1, 2].filter((bit) => (mask & (1 << bit)) !== 0).length;
      expect((await backend.solve(game.finalize())).sat).toBe(selected === (active ? 1 : 0));
    }
});

test("constraint snapshots retain nested origins and reject later writes", () => {
  const game = new BooleanConstraints();
  const value = game.newBool("value");
  game.withProvenance({ kind: "fact", id: "outer" }, () => {
    game.withProvenance({ kind: "rule", id: "inner" }, () => game.addTruth(value));
    game.addFalse(value);
  });
  const problem = game.finalize();
  expect(problem.origins?.map((origin) => origin.id)).toEqual(["inner", "outer"]);
  expect(() => validateSatWitness(problem, new Set())).toThrow("inner");
  expect(() => game.addTruth(value)).toThrow("finalized");
  expect(game.finalize()).toBe(problem);
});
