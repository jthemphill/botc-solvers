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

  test("setScript cannot remove roles referenced by claims or fixed roles", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B", "C"],
      script: ["Imp", "Juggler", "Savant"],
      fixedRoles: [{ name: "A", roles: ["Savant"] }],
      claims: [{ type: "Juggler", name: "B", guesses: { A: "Imp" } }],
    };

    const next = reducer(doc, { type: "setScript", script: ["Drunk"] });

    expect(next.script).toEqual(["Drunk", "Juggler", "Imp", "Savant"]);
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

  test("setPlayerCount removes affected player references", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["A", "B", "C"],
      script: ["Investigator"],
      fixedRoles: [{ name: "C", roles: ["Investigator"] }],
      claims: [{ type: "Investigator", name: "A", among: ["B", "C"] }],
    };

    const next = reducer(doc, { type: "setPlayerCount", count: 2 });

    expect(next.players).toEqual(["A", "B"]);
    expect(next.fixedRoles).toEqual([]);
    expect(next.claims).toEqual([{ type: "Investigator", name: "A", among: ["B"] }]);
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
