import { describe, expect, test } from "bun:test";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { jugglerGuessRoleOptions } from "./scriptRoles";

describe("script role helpers", () => {
  test("orders juggler guesses by claimed role, hidden roles, then remaining script roles", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["Alice", "Bob"],
      script: ["Chef", "Imp", "Empath", "Poisoner", "Drunk", "Juggler", "Knight"],
      claims: [
        { type: "Empath", name: "Alice", count: 1 },
        { type: "Juggler", name: "Bob", guesses: {} },
      ],
    };

    expect(jugglerGuessRoleOptions(doc, "Alice")).toEqual([
      "Empath",
      "Imp",
      "Poisoner",
      "Drunk",
      "Chef",
      "Juggler",
      "Knight",
    ]);
  });

  test("limits juggler guess roles to the script", () => {
    const doc: PuzzleDoc = {
      version: 1,
      players: ["Alice"],
      script: ["Imp", "Drunk", "Chef"],
      claims: [{ type: "Empath", name: "Alice", count: 1 }],
    };

    expect(jugglerGuessRoleOptions(doc, "Alice")).toEqual(["Imp", "Drunk", "Chef"]);
  });
});
