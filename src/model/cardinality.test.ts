import { beforeAll, expect, test } from "bun:test";
import { atMostClauses } from "./cardinality";
import { KissatBackend, type Literal } from "./sat";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

test("cardinality agrees with arithmetic for signed and repeated inputs, including disabled constraints", async () => {
  for (const inputs of [
    [1, 2, 3, 4, 5, 6, 7],
    [1, -2, 1, 3, -3, 2, 1],
  ]) {
    for (const count of [-1, 0, 1, 2, 3, 6, 7, 8]) {
      let variables = 8;
      const clauses = atMostClauses(inputs, count, () => ++variables).map((clause) => [-8, ...clause]);
      for (let bits = 0; bits < 128; bits++) {
        const value = (literal: Literal) => (((bits >> (Math.abs(literal) - 1)) & 1) === 1) === literal > 0;
        const fixed = Array.from({ length: 7 }, (_, i) => [value(i + 1) ? i + 1 : -(i + 1)]);
        for (const enabled of [false, true]) {
          const result = await backend.solve({
            variableCount: variables,
            clauses: [...clauses, ...fixed, [enabled ? 8 : -8]],
          });
          expect(result.sat).toBe(!enabled || inputs.filter(value).length <= count);
        }
      }
    }
  }
});

test("middle cardinalities have polynomial size", () => {
  let variables = 20;
  const clauses = atMostClauses(
    Array.from({ length: 20 }, (_, i) => i + 1),
    10,
    () => ++variables,
  );
  expect(clauses.length).toBeLessThan(500);
  expect(variables).toBeLessThan(250);
});
