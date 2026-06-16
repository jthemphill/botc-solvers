import { describe, expect, test } from "bun:test";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { reducer } from "./puzzleDoc";

describe("puzzle document reducer", () => {
  test("claim roles are added to the protected script", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B", "C"],
      script: [],
      claims: [],
    };

    const withClaim = reducer(doc, {
      type: "addClaim",
      claim: { type: "Investigator", name: "A", minionRole: "Poisoner", among: ["B", "C"] },
    });

    expect(withClaim.script).toContain("Investigator");
    expect(withClaim.script).toContain("Poisoner");
  });

  test("setScript cannot remove roles referenced by claims or role constraints", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B", "C"],
      script: ["Imp", "Juggler", "Savant"],
      fixedRoles: [{ name: "A", roles: ["Savant"] }],
      forbiddenRoles: [{ name: "C", roles: ["Vortox"] }],
      claims: [{ type: "Juggler", name: "B", guesses: { A: "Imp" } }],
    };

    const next = reducer(doc, { type: "setScript", script: ["Drunk"] });

    expect(next.script).toEqual(["Drunk", "Juggler", "Imp", "Savant", "Vortox"]);
  });

  test("savant DSL role identifiers protect matching script roles", () => {
    const doc: PuzzleDoc = {
      version: 1,
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

  test("custom info DSL role identifiers protect matching script roles", () => {
    const doc: PuzzleDoc = {
      version: 1,
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

  test("setPlayerCount removes affected player references", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B", "C"],
      script: ["Investigator"],
      fixedRoles: [{ name: "C", roles: ["Investigator"] }],
      forbiddenRoles: [{ name: "C", roles: ["Imp"] }],
      timeline: [
        { timing: "day_1", type: "execution", players: ["B"] },
        { timing: "night_2", type: "nightKill", players: ["C"] },
      ],
      claims: [{ type: "Investigator", name: "A", among: ["B", "C"] }],
    };

    const next = reducer(doc, { type: "setPlayerCount", count: 2 });

    expect(next.players).toEqual(["A", "B"]);
    expect(next.fixedRoles).toEqual([]);
    expect(next.forbiddenRoles).toEqual([]);
    expect(next.timeline).toEqual([{ timing: "day_1", type: "execution", players: ["B"] }]);
    expect(next.claims).toEqual([{ type: "Investigator", name: "A", among: ["B"] }]);
  });

  test("renamePlayer updates timeline references", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B", "C"],
      script: [],
      timeline: [{ timing: "day_1", type: "execution", players: ["B"] }],
      claims: [
        { type: "Chambermaid", name: "A", checks: [{ left: "B", right: "C", count: 1 }] },
        { type: "Oracle", name: "A", count: 1, deadPlayers: ["B"] },
      ],
    };

    const next = reducer(doc, { type: "renamePlayer", index: 1, name: "Bea" });

    expect(next.players).toEqual(["A", "Bea", "C"]);
    expect(next.timeline).toEqual([{ timing: "day_1", type: "execution", players: ["Bea"] }]);
    expect(next.claims).toEqual([
      { type: "Chambermaid", name: "A", checks: [{ left: "Bea", right: "C", count: 1 }] },
      { type: "Oracle", name: "A", count: 1, deadPlayers: ["Bea"] },
    ]);
  });

  test("removePlayer removes empty timeline events", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B"],
      script: [],
      timeline: [{ timing: "night_2", type: "nightKill", players: ["B"] }],
      claims: [],
    };

    const next = reducer(doc, { type: "removePlayer", index: 1 });

    expect(next.players).toEqual(["A"]);
    expect(next.timeline).toEqual([]);
  });

  test("movePlayerTo reorders players without changing claims", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B", "C", "D"],
      script: ["Investigator"],
      claims: [{ type: "Investigator", name: "A", among: ["B", "C"] }],
    };

    const next = reducer(doc, { type: "movePlayerTo", fromIndex: 0, toIndex: 2 });

    expect(next.players).toEqual(["B", "C", "A", "D"]);
    expect(next.claims).toEqual(doc.claims);
  });

  test("Knight claims are capped at two no-demon players", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B", "C"],
      script: ["Knight"],
      claims: [],
    };

    const next = reducer(doc, {
      type: "addClaim",
      claim: { type: "Knight", name: "A", noDemonAmong: ["A", "B", "C"] },
    });

    expect(next.claims).toEqual([{ type: "Knight", name: "A", noDemonAmong: ["A", "B"] }]);
  });

  test("Investigator claims discard legacy registration overrides", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B"],
      script: ["Investigator"],
      claims: [
        { type: "Investigator", name: "A", among: ["B"], registers: false } as unknown as PuzzleDoc["claims"][number],
      ],
    };

    const loaded = reducer(doc, { type: "load", doc });
    const added = reducer(
      { ...doc, claims: [] },
      { type: "addClaim", claim: doc.claims[0] as PuzzleDoc["claims"][number] },
    );

    expect(loaded.claims).toEqual([{ type: "Investigator", name: "A", among: ["B"] }]);
    expect(added.claims).toEqual([{ type: "Investigator", name: "A", among: ["B"] }]);
  });
});
