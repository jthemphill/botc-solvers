import { describe, expect, test } from "bun:test";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { SerializableWorld } from "../worker/protocol";
import { docReducer as reducer, reducer as puzzleReducer } from "./puzzleDoc";

describe("puzzle document reducer", () => {
  test("claim roles are added to the protected script", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: [],
      claims: [],
    };

    const withClaim = reducer(doc, {
      type: "addClaim",
      claim: { type: "Investigator", name: "A", minionRole: "Poisoner", among: ["B", "C"] },
    });
    const withCourtier = reducer(doc, {
      type: "addClaim",
      claim: { type: "Courtier", name: "A", role: "Vortox", drunkTimings: ["night_1"] },
    });

    expect(withClaim.script).toContain("Investigator");
    expect(withClaim.script).toContain("Poisoner");
    expect(withCourtier.script).toContain("Courtier");
    expect(withCourtier.script).toContain("Vortox");
  });

  test("setScript cannot remove roles referenced by claims or role constraints", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: ["Imp", "Juggler", "Savant"],
      constraints: [{ expression: "A.role == Savant" }, { expression: "C.role != Vortox" }],
      claims: [{ type: "Juggler", name: "B", possibleActualRoles: ["Juggler", "Drunk"], guesses: { A: "Imp" } }],
    };

    const next = reducer(doc, { type: "setScript", script: ["Drunk"] });

    expect(next.script).toEqual(["Drunk", "Juggler", "Imp", "Savant", "Vortox"]);
  });

  test("savant DSL role identifiers protect matching script roles", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B"],
      script: [],
      claims: [
        {
          type: "Savant",
          name: "A",
          statements: [{ options: ["some p: players | p.role == ScarletWoman", "B.role == `No Dashii`"] }],
        },
      ],
    };

    const loaded = reducer(doc, { type: "load", doc });

    expect(loaded.script).toContain("Savant");
    expect(loaded.script).toContain("Scarlet Woman");
    expect(loaded.script).toContain("No Dashii");
  });

  test("savant DSL function names do not protect matching role names", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B"],
      script: [],
      claims: [
        {
          type: "Savant",
          name: "A",
          statements: [{ options: ["chef(1)", "B.role == Empath"] }],
        },
      ],
    };

    const loaded = reducer(doc, { type: "load", doc });

    expect(loaded.script).not.toContain("Chef");
    expect(loaded.script).toContain("Empath");
  });

  test("custom info DSL role identifiers protect matching script roles", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B"],
      script: [],
      claims: [
        {
          type: "Sage",
          name: "A",
          info: [{ timing: "night_1", expression: "B.role == `No Dashii`" }],
        },
      ],
    };

    const loaded = reducer(doc, { type: "load", doc });

    expect(loaded.script).toContain("Sage");
    expect(loaded.script).toContain("No Dashii");
  });

  test("load sorts timeline events", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: [],
      timeline: [
        { timing: "night_2", type: "nightDeath", players: ["B"] },
        { timing: "day_1", type: "execution", players: ["A"] },
        { timing: "night_1", type: "nightDeath", players: ["C"] },
      ],
      claims: [],
    };

    const loaded = reducer(doc, { type: "load", doc });

    expect(loaded.timeline).toEqual([
      { timing: "night_1", type: "nightDeath", players: ["C"] },
      { timing: "day_1", type: "execution", players: ["A"] },
      { timing: "night_2", type: "nightDeath", players: ["B"] },
    ]);
  });

  test("Fortune Teller checks normalize into one claim per night", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: [],
      claims: [
        {
          type: "FortuneTeller",
          name: "A",
          checks: [
            { left: "B", right: "C", yes: true, timing: "night_1" },
            { left: "A", right: "B", yes: false, timing: "night_2" },
          ],
        },
      ],
    };

    const loaded = reducer(doc, { type: "load", doc });

    expect(loaded.claims).toEqual([
      {
        type: "FortuneTeller",
        name: "A",
        checks: [{ left: "B", right: "C", yes: true, timing: "night_1" }],
      },
      {
        type: "FortuneTeller",
        name: "A",
        checks: [{ left: "A", right: "B", yes: false, timing: "night_2" }],
      },
    ]);
  });

  test("Snake Charmer checks normalize into one claim per night", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: [],
      claims: [
        {
          type: "Snake Charmer",
          name: "A",
          checks: [
            { player: "B", demon: false, timing: "night_1" },
            { player: "C", demon: true, timing: "night_2" },
          ],
          evilTwin: { player: "C", timing: "night_1" },
        },
      ],
    };

    const loaded = reducer(doc, { type: "load", doc });

    expect(loaded.claims).toEqual([
      {
        type: "Snake Charmer",
        name: "A",
        checks: [{ player: "B", demon: false, timing: "night_1" }],
        evilTwin: { player: "C", timing: "night_1" },
      },
      {
        type: "Snake Charmer",
        name: "A",
        checks: [{ player: "C", demon: true, timing: "night_2" }],
      },
    ]);
  });

  test("setPlayerCount removes affected player references", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: ["Investigator"],
      timeline: [
        { timing: "day_1", type: "execution", players: ["B"] },
        { timing: "day_1", type: "doomsayerDeath", players: ["B"], caller: "C" },
        { timing: "night_2", type: "nightDeath", players: ["C"], caller: "C" },
      ],
      claims: [{ type: "Investigator", name: "A", among: ["B", "C"] }],
    };

    const next = reducer(doc, { type: "setPlayerCount", count: 2 });

    expect(next.players).toEqual(["A", "B"]);
    expect(next.timeline).toEqual([
      { timing: "day_1", type: "execution", players: ["B"] },
      { timing: "day_1", type: "doomsayerDeath", players: ["B"], caller: undefined },
    ]);
    expect(next.claims).toEqual([{ type: "Investigator", name: "A", among: ["B"] }]);
  });

  test("renamePlayer updates timeline references", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: [],
      timeline: [
        { timing: "day_1", type: "doomsayerDeath", players: ["B"], caller: "C" },
        { timing: "day_1", type: "doomsayerDeath", players: ["C"], caller: "B" },
      ],
      claims: [{ type: "Chambermaid", name: "A", checks: [{ left: "B", right: "C", count: 1 }] }],
    };

    const next = reducer(doc, { type: "renamePlayer", index: 1, name: "Bea" });

    expect(next.players).toEqual(["A", "Bea", "C"]);
    expect(next.timeline).toEqual([
      { timing: "day_1", type: "doomsayerDeath", players: ["Bea"], caller: "C" },
      { timing: "day_1", type: "doomsayerDeath", players: ["C"], caller: "Bea" },
    ]);
    expect(next.claims).toEqual([{ type: "Chambermaid", name: "A", checks: [{ left: "Bea", right: "C", count: 1 }] }]);
  });

  test("renamePlayer updates Slayer targets", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B"],
      script: ["Slayer"],
      claims: [{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: false }],
    };

    const next = reducer(doc, { type: "renamePlayer", index: 1, name: "Bea" });

    expect(next.claims).toEqual([{ type: "Slayer", name: "A", timing: "day_1", target: "Bea", killed: false }]);
  });

  test("removePlayer removes empty timeline events", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B"],
      script: [],
      timeline: [{ timing: "night_2", type: "nightDeath", players: ["B"] }],
      claims: [],
    };

    const next = reducer(doc, { type: "removePlayer", index: 1 });

    expect(next.players).toEqual(["A"]);
    expect(next.timeline).toEqual([]);
  });

  test("setTimeline records manual deaths and executions", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: [],
      claims: [],
    };

    const next = reducer(doc, {
      type: "setTimeline",
      timeline: [
        { timing: "day_1", type: "execution", players: ["A"] },
        { timing: "night_2", type: "nightDeath", players: ["B", "C"] },
      ],
    });

    expect(next.timeline).toEqual([
      { timing: "day_1", type: "execution", players: ["A"] },
      { timing: "night_2", type: "nightDeath", players: ["B", "C"] },
    ]);
  });

  test("setTimeline sorts modified events by timing", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: [],
      claims: [],
    };

    const next = reducer(doc, {
      type: "setTimeline",
      timeline: [
        { timing: "night_2", type: "nightDeath", players: ["B"] },
        { timing: "day_1", type: "execution", players: ["A"] },
        { timing: "day_1", type: "doomsayerDeath", players: ["C"], caller: "D" },
        { timing: "night_1", type: "nightDeath", players: ["D"] },
      ],
    });

    expect(next.timeline).toEqual([
      { timing: "night_1", type: "nightDeath", players: ["D"] },
      { timing: "day_1", type: "execution", players: ["A"] },
      { timing: "day_1", type: "doomsayerDeath", players: ["C"], caller: "D" },
      { timing: "night_2", type: "nightDeath", players: ["B"] },
    ]);
  });

  test("setTimeline normalizes invalid and empty events", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: [],
      claims: [],
    };

    const next = reducer(doc, {
      type: "setTimeline",
      timeline: [
        { timing: "day_1", type: "execution", players: ["A", "B"] },
        { timing: "night_2", type: "nightDeath", players: ["B", "Z", "B"] },
        { timing: "day_2", type: "execution", players: ["Z"] },
      ],
    });

    expect(next.timeline).toEqual([
      { timing: "day_1", type: "execution", players: ["A"] },
      { timing: "night_2", type: "nightDeath", players: ["B"] },
    ]);

    const cleared = reducer(next, { type: "setTimeline", timeline: [] });
    expect(cleared.timeline).toBeUndefined();
  });

  test("killed Slayer claims maintain a matching timeline event", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C"],
      script: ["Slayer"],
      claims: [],
    };

    const withKill = reducer(doc, {
      type: "addClaim",
      claim: { type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true, gameContinued: true },
    });

    expect(withKill.claims).toEqual([{ type: "Slayer", name: "A", timing: "day_1", target: "B", killed: true }]);
    expect(withKill.timeline).toEqual([{ timing: "day_1", type: "slayerShot", players: ["B"] }]);

    const withChangedKill = reducer(withKill, {
      type: "updateClaim",
      index: 0,
      claim: { type: "Slayer", name: "A", timing: "day_2", target: "C", killed: true },
    });

    expect(withChangedKill.timeline).toEqual([{ timing: "day_2", type: "slayerShot", players: ["C"] }]);

    const withNoKill = reducer(withChangedKill, {
      type: "updateClaim",
      index: 0,
      claim: { type: "Slayer", name: "A", timing: "day_2", target: "C", killed: false },
    });

    expect(withNoKill.timeline).toBeUndefined();
  });

  test("movePlayerTo reorders players without changing claims", () => {
    const doc: PuzzleDoc = {
      players: ["A", "B", "C", "D"],
      script: ["Investigator"],
      claims: [{ type: "Investigator", name: "A", among: ["B", "C"] }],
    };

    const next = reducer(doc, { type: "movePlayerTo", fromIndex: 0, toIndex: 2 });

    expect(next.players).toEqual(["B", "C", "A", "D"]);
    expect(next.claims).toEqual(doc.claims);
  });

  test("solve action stores current results and ignores stale completions", () => {
    const doc: PuzzleDoc = {
      title: "First",
      players: ["A"],
      script: ["Imp"],
      claims: [],
    };
    const nextDoc: PuzzleDoc = {
      ...doc,
      title: "Second",
      players: ["B"],
    };
    const worlds: readonly SerializableWorld[] = [
      {
        actual: [["A", "Imp"]],
        apparent: [["A", "Imp"]],
        poisoned: [],
        drunk: [],
      },
    ];

    const solving = puzzleReducer({ doc }, { type: "solve", status: "started", doc });
    const solved = puzzleReducer(solving, { type: "solve", status: "succeeded", doc, worlds });

    expect(solved.solveResult).toBe(worlds);
    expect(solved.solveError).toBeUndefined();

    const loaded = puzzleReducer(solving, { type: "load", doc: nextDoc });
    const staleCompletion = puzzleReducer(loaded, { type: "solve", status: "succeeded", doc, worlds });

    expect(staleCompletion.doc.title).toBe("Second");
    expect(staleCompletion.solveResult).toBeUndefined();
    expect(staleCompletion.solveError).toBeUndefined();
  });
});
