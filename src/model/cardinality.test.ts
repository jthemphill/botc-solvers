import { beforeAll, expect, test } from "bun:test";
import { BooleanConstraints } from "./boolean";
import { KissatBackend, type Literal } from "./sat";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

/** Make seven inputs and one condition. Variables 1 to 7 are the inputs. Variable 8 is the condition. */
function constraints() {
  const game = new BooleanConstraints();
  for (let variable = 1; variable <= 8; variable += 1) game.newBool();
  return game;
}

test("cardinality agrees with arithmetic for signed and repeated inputs, including disabled constraints", async () => {
  const bounds = {
    addEnforcedAtMostN: (sum: number, count: number) => sum <= count,
    addEnforcedAtLeastN: (sum: number, count: number) => sum >= count,
    addEnforcedExactlyN: (sum: number, count: number) => sum === count,
  };
  for (const [method, holds] of Object.entries(bounds) as [keyof typeof bounds, (typeof bounds)[keyof typeof bounds]][])
    for (const inputs of [
      [1, 2, 3, 4, 5, 6, 7],
      [1, -2, 1, 3, -3, 2, 1],
    ]) {
      for (const count of [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8]) {
        const game = constraints();
        game[method](inputs, count, 8);
        const problem = game.finalize();
        for (let bits = 0; bits < 128; bits++) {
          const value = (literal: Literal) => (((bits >> (Math.abs(literal) - 1)) & 1) === 1) === literal > 0;
          const fixed = Array.from({ length: 7 }, (_, i) => [value(i + 1) ? i + 1 : -(i + 1)]);
          for (const enabled of [false, true]) {
            const result = await backend.solve({
              ...problem,
              clauses: [...problem.clauses, ...fixed, [enabled ? 8 : -8]],
            });
            expect(result.sat).toBe(!enabled || holds(inputs.filter(value).length, count));
          }
        }
      }
    }
});

test("an all-but-one bound uses one clause and no auxiliary variables", () => {
  const inputs = [1, -2, 1, 3, -3, 2, 1];
  const game = constraints();
  game.addEnforcedAtMostN(inputs, inputs.length - 1, 8);
  expect(game.finalize()).toMatchObject({ variableCount: 8, clauses: [[-8, ...inputs.map((literal) => -literal)]] });
});

test("an at-most-one bound on many inputs uses a logarithmic number of auxiliary variables", () => {
  const game = new BooleanConstraints();
  game.addExactlyOne(Array.from({ length: 20 }, () => game.newBool()));
  expect(game.finalize().variableCount).toBe(25);
});

test("middle cardinalities have polynomial size", () => {
  const game = new BooleanConstraints();
  game.addEnforcedExactlyN(
    Array.from({ length: 20 }, () => game.newBool()),
    10,
    game.newBool(),
  );
  expect(game.finalize().clauses.length).toBeLessThan(600);
  expect(game.finalize().variableCount).toBeLessThan(250);
});
