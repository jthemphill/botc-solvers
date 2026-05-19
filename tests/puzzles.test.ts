import { describe, expect, test } from "bun:test";
import { solve as solve01 } from "../src/puzzles/puzzle-01-sober-savant";
import { solve as solve02 } from "../src/puzzles/puzzle-02-come-fly-with-me";
import { solve as solve03a } from "../src/puzzles/puzzle-03a-not-throwing-away-my-shot";
import { solve as solve03b } from "../src/puzzles/puzzle-03b-not-throwing-away-my-shot";
import { MINION_ROLES, solve as solve04 } from "../src/puzzles/puzzle-04-the-many-headed-monster";

describe("ported puzzles", () => {
  test("sober savant has unique solution", async () => {
    const worlds = await solve01();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Anna");
    expect(worlds[0]?.holder("Scarlet Woman")).toBe("Tim");
    expect(worlds[0]?.holder("Drunk")).toBe("Oscar");
  });

  test("come fly with me has unique solution", async () => {
    const worlds = await solve02();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Goblin")).toBe("Sarah");
    expect(worlds[0]?.holder("Leviathan")).toBe("Matthew");
    expect(worlds[0]?.holder("Drunk")).toBe("You");
  });

  test("not throwing away my shot 3a has unique solution", async () => {
    const worlds = await solve03a();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Matthew");
    expect(worlds[0]?.holder("Baron")).toBe("Aoife");
    expect(worlds[0]?.holder("Drunk")).toBe("Oscar");
    expect(worlds[0]?.holder("Recluse")).toBe("Tom");
  });

  test("not throwing away my shot 3b has unique solution", async () => {
    const worlds = await solve03b();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Spy")).toBe("Hannah");
    expect(worlds[0]?.holder("Imp")).toBe("Sarah");
    expect(worlds[0]?.holder("Drunk")).toBeUndefined();
  });

  test("many headed monster forced demon and minion team", async () => {
    const worlds = await solve04();
    expect(worlds.length).toBeGreaterThan(0);
    expect(new Set(worlds.map((world) => world.holder("Lord of Typhon")))).toEqual(new Set(["Fraser"]));
    expect(
      new Set(worlds.map((world) => JSON.stringify(MINION_ROLES.flatMap((role) => world.holder(role) ?? []).sort()))),
    ).toEqual(new Set([JSON.stringify(["Dan", "Sarah"])]));
    expect(
      new Set(worlds.map((world) => JSON.stringify([world.holder("Marionette"), world.holder("Poisoner")]))),
    ).toEqual(new Set([JSON.stringify(["Sarah", "Dan"]), JSON.stringify(["Dan", "Sarah"])]));
  });
});
