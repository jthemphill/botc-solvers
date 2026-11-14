import { expect, test } from "bun:test";
import { simplify } from "./simplify";
import type { Clause } from "./sat";

/** Give each assignment of variables 1..count that makes all clauses true. */
function models(count: number, clauses: readonly Clause[]): string[] {
  const result: string[] = [];
  for (let mask = 0; mask < 1 << count; mask += 1) {
    const holds = (literal: number) => ((mask >> (Math.abs(literal) - 1)) & 1) === (literal > 0 ? 1 : 0);
    if (clauses.every((clause) => clause.some(holds)))
      result.push(Array.from({ length: count }, (_, index) => (mask >> index) & 1).join(""));
  }
  return result;
}

test("fixed and equal variables leave the problem and return in the expanded model", () => {
  const { problem, projection, expand } = simplify(
    { variableCount: 4, clauses: [[1, 2, 3], [-1, 4], [1, -4], [-2]], origins: ["a", "b", "c", "d"].map(origin) },
    [1, 2, 4],
  );
  expect(problem).toEqual({ variableCount: 2, clauses: [[1, 2]], origins: [origin("a")] });
  expect(projection).toEqual([1]);
  expect([...expand(new Set([1]))]).toEqual([1, 4]);
  expect([...expand(new Set([2]))]).toEqual([3]);
});

test("a contradiction gives an unsatisfiable problem", () => {
  for (const clauses of [
    [[1], [-1]],
    [
      [1, 2],
      [-1, -2],
      [1, -2],
      [-1, 2],
    ],
    [[1, -2], [-1, 2], [1], [-2]],
  ])
    expect(simplify({ variableCount: 2, clauses }, [1]).problem.clauses).toEqual([[]]);
});

test("a variable that is only in the projection stays free", () => {
  const { problem, projection } = simplify(
    {
      variableCount: 3,
      clauses: [
        [1, -2],
        [-1, 2],
      ],
    },
    [2, 3],
  );
  expect(problem.clauses).toEqual([]);
  expect(projection).toEqual([1, 2]);
});

test("each small formula keeps its models", () => {
  let seed = 7;
  const random = (limit: number) => (seed = (seed * 1103515245 + 12345) % 2 ** 31) % limit;
  for (let sample = 0; sample < 300; sample += 1) {
    const count = 6;
    const clauses = Array.from({ length: 3 + random(8) }, () =>
      Array.from({ length: 1 + random(3) }, () => (1 + random(count)) * (random(2) ? 1 : -1)),
    );
    const { problem, expand } = simplify({ variableCount: count, clauses }, []);
    const expected = models(count, clauses);
    // A free variable of the initial problem can have the two values. Compare with the fixed choice of `expand`.
    const expanded = models(problem.variableCount, problem.clauses).map((model) => {
      const positive = new Set([...model].flatMap((bit, index) => (bit === "1" ? [index + 1] : [])));
      const all = expand(positive);
      return Array.from({ length: count }, (_, index) => (all.has(index + 1) ? 1 : 0)).join("");
    });
    for (const model of expanded) expect(expected).toContain(model);
    expect(expanded.length > 0).toBe(expected.length > 0);
    expect(new Set(expanded).size).toBe(expanded.length);
  }
});

function origin(id: string) {
  return { kind: "rule" as const, id };
}
