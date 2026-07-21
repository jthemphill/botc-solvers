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
  Clockmaker,
  FortuneTeller,
  Goon,
  Goblin,
  Klutz,
  Legion,
  Leviathan,
  VillageIdiot,
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
    dsl: "chef(1)",
    ts: (g: BOTCModel) => Chef.learnsCount(g, 1, "ref_chef"),
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
    game.addTruth(compile("registers_as(B, Imp)", game, ctx) as BoolLike);

    expect(await game.solveAll()).toHaveLength(1);
  });

  test("timed alignment expressions use a Goon's current alignment", async () => {
    const game = buildPuzzleModel({ players: ["A", "B"], characters: [Goon, Imp], setup: false }, backend);
    game.fixActual("A", Goon);
    game.fixActual("B", Imp);
    game.setGoodAt("A", "day_2", game.constantBool(false, "a_is_evil_on_day_2"));

    game.addTruth(
      compile("A.alignment == Evil", game, {
        players: ["A", "B"],
        script: ["Goon", "Imp"],
        nameRoot: "timed_alignment",
        timing: "day_2",
      }) as BoolLike,
    );
    game.addTruth(
      compile("A.alignment == Good", game, {
        players: ["A", "B"],
        script: ["Goon", "Imp"],
        nameRoot: "base_alignment",
      }) as BoolLike,
    );

    expect(await game.solveAll({ limit: 1 })).toHaveLength(1);
  });

  test("cardinality comprehensions count roles in play", async () => {
    const game = buildPuzzleModel(
      { players: ["A", "B", "C"], characters: [Imp, Savant, Clockmaker, Klutz], setup: false },
      backend,
    );
    const ctx: CompileCtx = {
      players: ["A", "B", "C"],
      script: ["Imp", "Savant", "Clockmaker", "Klutz"],
      nameRoot: "cardinality_comprehension",
    };

    game.fixActual("A", Imp);
    game.fixActual("B", Savant);
    game.fixActual("C", Clockmaker);
    game.addTruth(compile("#{r : {Clockmaker, Klutz} | some p : players | p.role == r} == 1", game, ctx) as BoolLike);
    game.addTruth(compile("#{p : players | some (p.role & {Clockmaker, Klutz})} == 1", game, ctx) as BoolLike);
    game.addFalse(compile("#{r : {Clockmaker, Klutz} | some p : players | p.role == r} == 2", game, ctx) as BoolLike);

    expect(await game.solveAll()).toHaveLength(1);
  });

  test("static character-type role sets contain the matching script roles", async () => {
    const game = buildPuzzleModel(PUZZLE, backend);
    const ctx: CompileCtx = {
      players: PLAYERS,
      script: CHARACTERS.map((character) => (typeof character === "string" ? character : character.roleName)),
      nameRoot: "character_type_role_sets",
    };

    game.addTruth(compile("#townsfolk = 6 && #outsiders = 1 && #minions = 1 && #demons = 1", game, ctx) as BoolLike);
    game.addTruth(compile("some r : townsfolk + outsiders | some p : players | p.role = r", game, ctx) as BoolLike);

    expect(await game.solveAll({ limit: 1 })).toHaveLength(1);
  });

  test("inverse role joins expose role holders and cardinalities support numeric set membership", async () => {
    const players = ["A", "B", "C", "D", "E", "F"];
    const game = buildPuzzleModel({ players, characters: [Legion, Savant], setup: false }, backend);
    const ctx: CompileCtx = {
      players,
      script: ["Legion", "Savant"],
      nameRoot: "inverse_role",
    };

    for (const player of players.slice(0, 5)) game.fixActual(player, Legion);
    game.fixActual("F", Savant);
    game.addTruth(compile("#Legion.~role in {0, 5, 6}", game, ctx) as BoolLike);
    game.addTruth(compile("one townsfolk.~role", game, ctx) as BoolLike);
    game.addTruth(compile("#Evil.~alignment = 5 && #Townsfolk.~type = 1", game, ctx) as BoolLike);
    game.addTruth(compile("F.role in townsfolk", game, ctx) as BoolLike);
    game.addFalse(compile("lone demons.~role", game, ctx) as BoolLike);

    expect(await game.solveAll()).toHaveLength(1);
  });

  test("Alloy-style joins expose distinct character types in a player set", async () => {
    const game = buildPuzzleModel(
      { players: ["A", "B", "C", "D"], characters: [Imp, Savant, Clockmaker, Goblin], setup: false },
      backend,
    );
    const ctx: CompileCtx = {
      players: ["A", "B", "C", "D"],
      script: ["Imp", "Savant", "Clockmaker", "Goblin"],
      nameRoot: "set_join_type",
    };

    game.fixActual("A", Savant);
    game.fixActual("B", Clockmaker);
    game.fixActual("C", Imp);
    game.fixActual("D", Goblin);
    game.addTruth(compile("#((A + B + C + D).type) = 3", game, ctx) as BoolLike);
    game.addTruth(compile("#({A, B, C, D}.type) == 3", game, ctx) as BoolLike);
    game.addTruth(compile("Townsfolk in {A, B, C, D}.type", game, ctx) as BoolLike);
    game.addTruth(compile("Townsfolk in A.type", game, ctx) as BoolLike);
    game.addFalse(compile("#((A + B + C + D).type) = 2", game, ctx) as BoolLike);
    game.addFalse(compile("Demon in A.type", game, ctx) as BoolLike);

    expect(await game.solveAll()).toHaveLength(1);
  });

  test("role_distance matches exact circular seating distance", async () => {
    const game = buildPuzzleModel(
      { players: ["A", "B", "C", "D"], characters: [Leviathan, Goblin, Savant, Clockmaker], setup: false },
      backend,
    );
    const ctx: CompileCtx = {
      players: ["A", "B", "C", "D"],
      script: ["Leviathan", "Goblin", "Savant", "Clockmaker"],
      nameRoot: "role_distance",
    };

    game.fixActual("A", Leviathan);
    game.fixActual("B", Savant);
    game.fixActual("C", Goblin);
    game.fixActual("D", Clockmaker);
    game.addTruth(compile("role_distance(2, Leviathan, Goblin)", game, ctx) as BoolLike);
    game.addFalse(compile("role_distance(1, Leviathan, Goblin)", game, ctx) as BoolLike);

    expect(await game.solveAll()).toHaveLength(1);
  });

  test("fortune_teller_red_herring, globally_drunk, and poisoned expose model state", async () => {
    const game = buildPuzzleModel(
      { players: ["FT", "Red", "VI", "Demon"], characters: [FortuneTeller, Leviathan, VillageIdiot], setup: false },
      backend,
    );
    const ctx: CompileCtx = {
      players: ["FT", "Red", "VI", "Demon"],
      script: ["Fortune Teller", "Leviathan", "Village Idiot"],
      nameRoot: "ft_red_herring_drunk",
    };

    game.fixActual("FT", FortuneTeller);
    game.fixActual("Red", VillageIdiot);
    game.fixActual("VI", VillageIdiot);
    game.fixActual("Demon", Leviathan);
    game.addVillageIdiotDrunking();
    game.addTruth(game.fortuneTellerRedHerring("FT", "Red"));
    game.addTruth(game.globalDrunk("VI"));
    game.fixPoisoned("Red", true, "night_1");
    game.addTruth(compile("fortune_teller_red_herring(FT, Red)", game, ctx) as BoolLike);
    game.addTruth(compile("globally_drunk(VI)", game, ctx) as BoolLike);
    game.addTruth(compile("poisoned(Red, night_1)", game, ctx) as BoolLike);
    game.addFalse(compile("fortune_teller_red_herring(FT, VI)", game, ctx) as BoolLike);
    game.addFalse(compile("globally_drunk(Red)", game, ctx) as BoolLike);
    game.addFalse(compile("poisoned(FT, night_1)", game, ctx) as BoolLike);

    expect(await game.solveAll()).toHaveLength(1);
  });

  test("role_at exposes timed role state", async () => {
    const game = buildPuzzleModel({ players: ["A", "B"], characters: script(Imp, Chef), setup: false }, backend);
    const ctx: CompileCtx = {
      players: ["A", "B"],
      script: ["Imp", "Chef"],
      nameRoot: "role_at",
    };

    game.fixActual("A", Chef);
    game.fixActual("B", Imp);
    game.addRoleAt("A", Imp, "night_2");
    game.addTruth(compile("role_at(A, Imp, night_2)", game, ctx) as BoolLike);
    game.addFalse(compile("role_at(A, Imp, night_1)", game, ctx) as BoolLike);

    expect(await game.solveAll()).toHaveLength(1);
  });

  test("townsfolk_chain_length matches circular adjacent Townsfolk chains", async () => {
    const game = buildPuzzleModel(
      { players: ["A", "B", "C", "D"], characters: [Imp, Savant, Clockmaker, Klutz], setup: false },
      backend,
    );
    const ctx: CompileCtx = {
      players: ["A", "B", "C", "D"],
      script: ["Imp", "Savant", "Clockmaker", "Klutz"],
      nameRoot: "townsfolk_chain_length",
    };

    game.fixActual("A", Clockmaker);
    game.fixActual("B", Savant);
    game.fixActual("C", Imp);
    game.fixActual("D", Klutz);
    game.addTruth(compile("townsfolk_chain_length(2)", game, ctx) as BoolLike);
    game.addFalse(compile("townsfolk_chain_length(3)", game, ctx) as BoolLike);

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
