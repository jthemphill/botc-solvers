import { describe, expect, test } from "bun:test";
import { solve as solve01 } from "../src/puzzles/puzzle-01-sober-savant";
import { solve as solve02 } from "../src/puzzles/puzzle-02-come-fly-with-me";
import { solve as solve03a } from "../src/puzzles/puzzle-03a-not-throwing-away-my-shot";
import { solve as solve03b } from "../src/puzzles/puzzle-03b-not-throwing-away-my-shot";
import { MINION_ROLES, solve as solve04 } from "../src/puzzles/puzzle-04-the-many-headed-monster";
import { possibleAlsaahirGuesses, solve as solve05a } from "../src/puzzles/puzzle-05a-you-only-guess-twice";
import { possibleJuggles, solve as solve05b } from "../src/puzzles/puzzle-05b-you-only-guess-twice";
import { solve as solve06 } from "../src/puzzles/puzzle-06-super-marionette-bros";
import { solve as solve07 } from "../src/puzzles/puzzle-07-the-savant-strikes-back";
import { solve as solve08 } from "../src/puzzles/puzzle-08-the-stitch-up";
import { solve as solve09 } from "../src/puzzles/puzzle-09-the-new-acrobat";
import { solve as solve10 } from "../src/puzzles/puzzle-10-dont-overcook-it";

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

  test("you only guess twice 5a has two worlds and either Alsaahir guess resolves it", async () => {
    const worlds = await solve05a();
    expect(worlds).toHaveLength(2);
    expect(new Set(worlds.map((world) => world.holder("Leviathan")))).toEqual(new Set(["Oscar", "Hannah"]));
    expect(new Set(worlds.map((world) => world.holder("Goblin")))).toEqual(new Set(["Anna", "Oscar"]));
    expect(possibleAlsaahirGuesses(worlds)).toEqual([
      { demon: "Oscar", minion: "Anna", ifWrongDemon: "Hannah", ifWrongMinion: "Oscar" },
      { demon: "Hannah", minion: "Oscar", ifWrongDemon: "Oscar", ifWrongMinion: "Anna" },
    ]);
  });

  test("you only guess twice 5b has four worlds and a three-guess juggle resolves it", async () => {
    const worlds = await solve05b();
    expect(worlds).toHaveLength(4);
    expect(new Set(worlds.map((world) => `${world.holder("Leviathan")}/${world.holder("Goblin")}`))).toEqual(
      new Set(["Matthew/Steph", "Aoife/Steph", "Aoife/Sarah", "Sarah/Steph"]),
    );
    const [juggle] = possibleJuggles(worlds, { limit: 1 });
    expect(juggle?.guesses).toEqual([
      { player: "Matthew", role: "Leviathan" },
      { player: "Steph", role: "Goblin" },
      { player: "Aoife", role: "Noble" },
    ]);
    expect([...(juggle?.outcomes.entries() ?? [])].sort(([left], [right]) => left - right)).toEqual([
      [0, { demon: "Aoife", minion: "Sarah" }],
      [1, { demon: "Aoife", minion: "Steph" }],
      [2, { demon: "Sarah", minion: "Steph" }],
      [3, { demon: "Matthew", minion: "Steph" }],
    ]);
  });

  test("super marionette bros has unique solution", async () => {
    const worlds = await solve06();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Vortox")).toBe("Matthew");
    expect(worlds[0]?.holder("Marionette")).toBe("You");
    expect(worlds[0]?.holder("Drunk")).toBe("Steph");
  });

  test("the savant strikes back has unique solution", async () => {
    const worlds = await solve07();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Leviathan")).toBe("Anna");
    expect(worlds[0]?.holder("Goblin")).toBe("Oscar");
    expect(worlds[0]?.holder("Mutant")).toBe("Steph");
  });

  test("the stitch up forces the evil team", async () => {
    const worlds = await solve08();
    expect(worlds).toHaveLength(2);
    expect(new Set(worlds.map((world) => JSON.stringify([world.holder("Imp"), world.holder("Poisoner")])))).toEqual(
      new Set([JSON.stringify(["Josh", "Steph"]), JSON.stringify(["Steph", "Josh"])]),
    );
  });

  test("the new acrobat has a starpass solution", async () => {
    const worlds = await solve09();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Anna");
    expect(worlds[0]?.holder("Goblin")).toBe("Hannah");
    expect(worlds[0]?.holder("Drunk")).toBe("Josh");
  });

  test("dont overcook it has unique solution", async () => {
    const worlds = await solve10();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Dan");
    expect(worlds[0]?.holder("Poisoner")).toBe("Fraser");
  });
});
