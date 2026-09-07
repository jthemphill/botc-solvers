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

test("finalized clauses stay immutable and do not share the caller's array", () => {
  class Constraints extends BooleanConstraints {
    addInput(clause: number[]): void {
      this.addClause(clause);
    }
  }
  const game = new Constraints();
  const variable = game.newBool("input");
  const input = [variable.lit];
  game.addInput(input);
  input[0] = variable.not();
  const problem = game.finalize();
  expect(problem.clauses).toEqual([[variable.lit]]);
  expect(Object.isFrozen(problem)).toBe(true);
  expect(Object.isFrozen(problem.clauses)).toBe(true);
  expect(Object.isFrozen(problem.clauses[0])).toBe(true);
  expect(Object.isFrozen(problem.origins)).toBe(true);
  expect(Object.isFrozen(input)).toBe(false);
});

test("reified counts agree with arithmetic in both directions", async () => {
  for (const inputs of [[], [1], [1, 2, 3, 4], [1, -2, 1, 3, -3, 2, 1]]) {
    for (let count = -1; count <= inputs.length + 1; count += 1) {
      const game = new BooleanConstraints();
      const variables = Array.from({ length: 4 }, (_, i) => game.newBool(`input_${i}`));
      const result = game.boolSumEquals(inputs, count, "count");
      const problem = game.finalize();
      for (let mask = 0; mask < 16; mask += 1) {
        const value = (literal: number) => Boolean(mask & (1 << (Math.abs(literal) - 1))) === literal > 0;
        const expected = inputs.filter(value).length === count;
        const fixed = variables.map(({ lit }) => [value(lit) ? lit : -lit]);
        for (const asserted of [false, true]) {
          const current = {
            ...problem,
            clauses: [...problem.clauses, ...fixed, [asserted ? result.lit : result.not()]],
          };
          const witness = await backend.solve(current);
          expect(witness.sat).toBe(asserted === expected);
          if (witness.sat) validateSatWitness(current, witness.model);
        }
      }
    }
  }
});

test("boundary counts use a single gate", () => {
  for (const count of [0, 20]) {
    const game = new BooleanConstraints();
    const inputs = Array.from({ length: 20 }, (_, i) => game.newBool(`input_${i}`));
    game.boolSumEquals(inputs, count, "boundary");
    expect(game.finalize().variableCount).toBe(21);
    expect(game.finalize().clauses).toHaveLength(21);
  }
});

test("complementary counts have the same counter size", () => {
  const size = (count: number) => {
    const game = new BooleanConstraints();
    const inputs = Array.from({ length: 20 }, (_, i) => game.newBool(`input_${i}`));
    game.boolSumEquals(inputs, count, "count");
    return game.finalize().variableCount;
  };
  expect(size(19)).toBe(size(1));
});
