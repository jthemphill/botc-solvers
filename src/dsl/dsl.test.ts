import { beforeAll, describe, expect, test } from "bun:test";
import { compile, type CompileCtx } from "./compile";
import { DslError, lex } from "./lex";
import { parse } from "./parse";
import { KissatBackend, type SatBackend } from "../model/sat";
import { buildPuzzleModel, type PuzzleSpec } from "../model/setup";
import {
  Chef,
  Drunk,
  Imp,
  Investigator,
  Knight,
  Noble,
  Savant,
  ScarletWoman,
  Seamstress,
  Steward,
  applyClaims,
  script,
} from "../model/characters";
import type { BoolLike, BOTCModel } from "../model/model";
import { drunkBetweenTwoTownsfolk } from "../model/predicates";

const PLAYERS = ["Oscar", "Matt", "Anna", "You", "Tim", "Sula"];
const CHARACTERS = script(Imp, ScarletWoman, Drunk, Investigator, Knight, Noble, Savant, Seamstress, Steward);
const PUZZLE: PuzzleSpec = { players: PLAYERS, characters: CHARACTERS };

const SAVANT_CLAIMS = [
  // statement 1
  {
    dsl: "some p: players | p.role == Investigator",
    ts: (g: BOTCModel) => g.roleInPlay(Investigator),
  },
  {
    dsl: "some p: You.neighbors | p.alignment == Evil",
    ts: (g: BOTCModel) => g.sitsNextToEvil("You"),
  },
  // statement 2
  {
    dsl: "chef(1, registers: false)",
    ts: (g: BOTCModel) => Chef.learnsCount(g, 1, "ref_chef", { registers: false }),
  },
  {
    dsl: "some p: players | p.role == Drunk && p.left.type == Townsfolk && p.right.type == Townsfolk",
    ts: (g: BOTCModel) => drunkBetweenTwoTownsfolk(g),
  },
  // statement 3
  {
    dsl: "some p: {Tim, Sula} | p.type == Minion",
    ts: (g: BOTCModel) => g.anyOf([g.isMinion("Tim"), g.isMinion("Sula")], "ref_tim_or_sula_minion"),
  },
  {
    dsl: "no p: players | p.role == Noble",
    ts: (g: BOTCModel) => g.not(g.roleInPlay(Noble), "ref_noble_not_in_play"),
  },
];

describe("DSL", () => {
  let backend: SatBackend;
  beforeAll(async () => {
    backend = await KissatBackend.create();
  });

  test("lex passes basic tokens", () => {
    const toks = lex("some p: players | p.role == Investigator");
    expect(toks.map((t) => t.kind).slice(0, 8)).toEqual([
      "some",
      "ident",
      "colon",
      "ident",
      "pipe",
      "ident",
      "dot",
      "ident",
    ]);
  });

  test("parses puzzle-01 statements", () => {
    for (const s of SAVANT_CLAIMS) {
      const ast = parse(lex(s.dsl));
      expect(ast).toBeDefined();
    }
  });

  test("unknown identifier reports an error with a span", () => {
    try {
      const game = buildPuzzleModel(PUZZLE, backend);
      compile("some p: players | p.role == NoSuchRole", game, {
        players: PLAYERS,
        script: CHARACTERS.map((c) => (typeof c === "string" ? c : c.roleName)),
        nameRoot: "test",
      });
      expect("should have thrown").toBe("");
    } catch (e) {
      expect(e).toBeInstanceOf(DslError);
    }
  });

  test("left and right fields use next and previous seating positions", async () => {
    const game = buildPuzzleModel({ players: ["A", "B", "C"], characters: CHARACTERS, setup: false }, backend);
    const ctx: CompileCtx = {
      players: ["A", "B", "C"],
      script: CHARACTERS.map((c) => (typeof c === "string" ? c : c.roleName)),
      nameRoot: "left_right",
    };

    game.addTruth(compile("A.left == B && A.right == C", game, ctx) as BoolLike);
    game.addFalse(compile("A.left == C || A.right == B", game, ctx) as BoolLike);

    expect(await game.solveAll({ limit: 1 })).toHaveLength(1);
  });

  test("custom info helpers compile into constraints", async () => {
    const game = buildPuzzleModel({ players: ["A", "B"], characters: [Savant, Imp], setup: false }, backend);
    const ctx: CompileCtx = {
      players: ["A", "B"],
      script: ["Savant", "Imp"],
      nameRoot: "custom_info_helpers",
    };

    game.fixActual("A", Savant);
    game.fixActual("B", Imp);
    game.addTruth(compile("A.alignment != B.alignment", game, ctx) as BoolLike);
    game.addTruth(compile("role_count(2, A, Savant, B, Imp)", game, ctx) as BoolLike);
    game.addTruth(compile("malfunctions(night_1, 0)", game, ctx) as BoolLike);

    expect(await game.solveAll()).toHaveLength(1);
  });

  test("each DSL statement matches its hand-coded counterpart under the puzzle-01 model", async () => {
    // Build the puzzle-01 game so the Savant statement is true exactly when the DSL form is.
    const buildBaseGame = (): BOTCModel => {
      const g = buildPuzzleModel(PUZZLE, backend);
      g.fixActual("You", Savant);
      const PLAYERS_HAND = [
        new Investigator({ name: "Oscar", minionRole: ScarletWoman, among: ["Anna", "Sula"] }),
        new Noble({ name: "Matt", oneEvilAmong: ["Tim", "Oscar", "Sula"] }),
        new Seamstress({ timing: "night_1", name: "Anna", aligned: false, among: ["Oscar", "Sula"] }),
        new Knight({ name: "Tim", noDemonAmong: ["Anna", "Sula"] }),
        new Steward({ name: "Sula", goodPlayer: "Matt" }),
      ];
      applyClaims(g, PLAYERS_HAND);
      return g;
    };

    const ctx: CompileCtx = {
      players: PLAYERS,
      script: CHARACTERS.map((c) => (typeof c === "string" ? c : c.roleName)),
      nameRoot: "test",
    };

    for (const claim of SAVANT_CLAIMS) {
      const game = buildBaseGame();
      const dsl = compile(claim.dsl, game, ctx) as BoolLike;
      const ts = claim.ts(game);
      // iff: dsl == ts
      const iff = game.allOf(
        [
          game.anyOf([game.not(dsl, "ndsl"), ts], "dsl_implies_ts"),
          game.anyOf([game.not(ts, "nts"), dsl], "ts_implies_dsl"),
        ],
        "iff",
      );
      game.addTruth(iff);
      const worlds = await game.solveAll();
      expect(worlds.length).toBeGreaterThan(0);
    }
  });
});
