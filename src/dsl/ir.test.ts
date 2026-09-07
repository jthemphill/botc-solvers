import { beforeAll, expect, test } from "bun:test";
import { BOTCModel } from "../model/model";
import { roleByName } from "../model/roleRegistry";
import { KissatBackend } from "../model/sat";
import { compile, prepare } from "./compile";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});
const ctx = { players: ["A"], script: ["Chef", "Artist"], nameRoot: "dsl_fact", timing: "day_2" as const };
const model = () => new BOTCModel(ctx.players, { characters: ctx.script.map(roleByName), backend });

test("a type error does not partially mutate the solver", () => {
  const game = model();
  expect(() => compile("(A.role == Chef) && 3", game, ctx)).toThrow();
  expect(game.finalize()).toEqual(model().finalize());
});

test("typed operations retain source spans despite whitespace", () => {
  const program = prepare("malfunctions (night_2, 0) && A.role == Artist", ctx);
  for (const node of program.nodes) {
    expect(node.span.end).toBeGreaterThan(node.span.start);
    expect(node.span.end).toBeLessThanOrEqual(program.source.length);
  }
});

test("current and initial properties, forward joins and inverse joins share time semantics", async () => {
  const game = model();
  game.fixActual("A", "Chef");
  game.addRoleAt("A", "Artist", "night_2");
  game.addTruth(
    compile(
      "A.initial_role == Chef && A.role == Artist && some Artist.~role && no Artist.~initial_role && players.initial_role == {Chef} && A.initial_type == Townsfolk",
      game,
      ctx,
    ),
  );
  expect(await game.solveAll()).toHaveLength(1);
  expect(game.finalize().origins?.some((origin) => origin.id === "dsl_fact" && origin.span !== undefined)).toBe(true);
});
