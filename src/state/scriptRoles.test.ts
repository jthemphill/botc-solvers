import { describe, expect, test } from "bun:test";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { hiddenScriptRoleOptions, jugglerGuessRoleOptions } from "./scriptRoles";

describe("script role helpers", () => {
  test("lists evil and special good hidden roles for the script palette", () => {
    const options = hiddenScriptRoleOptions();

    expect(options).toContain("Imp");
    expect(options).toContain("Poisoner");
    expect(options).toContain("Widow");
    expect(options).toContain("Damsel");
    expect(options).toContain("Drunk");
    expect(options).toContain("Mutant");
    expect(options).not.toContain("Chef");
  });

  test("orders juggler guesses by claimed role, hidden roles, then remaining script roles", () => {
    const doc: PuzzleDoc = {
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
      players: ["Alice"],
      script: ["Imp", "Drunk", "Chef"],
      claims: [{ type: "Empath", name: "Alice", count: 1 }],
    };

    expect(jugglerGuessRoleOptions(doc, "Alice")).toEqual(["Imp", "Drunk", "Chef"]);
  });
});
