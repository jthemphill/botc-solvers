import { describe, expect, test } from "bun:test";
import { solve as solve01 } from "./puzzle-01-sober-savant";
import { solve as solve02 } from "./puzzle-02-come-fly-with-me";
import { solve as solve03a } from "./puzzle-03a-not-throwing-away-my-shot";
import { solve as solve03b } from "./puzzle-03b-not-throwing-away-my-shot";
import { MINION_ROLES, solve as solve04 } from "./puzzle-04-the-many-headed-monster";
import { possibleAlsaahirGuesses, solve as solve05a } from "./puzzle-05a-you-only-guess-twice";
import { possibleJuggles, solve as solve05b } from "./puzzle-05b-you-only-guess-twice";
import { solve as solve06 } from "./puzzle-06-super-marionette-bros";
import { solve as solve07 } from "./puzzle-07-the-savant-strikes-back";
import { solve as solve08 } from "./puzzle-08-the-stitch-up";
import { solve as solve09 } from "./puzzle-09-the-new-acrobat";
import { solve as solve10 } from "./puzzle-10-dont-overcook-it";
import { solve as solve11 } from "./puzzle-11-false-is-the-new-black";
import { solve as solve12a } from "./puzzle-12a-thunderstruck";
import { solve as solve12b } from "./puzzle-12b-thunderstruck";
import { solve as solve13 } from "./puzzle-13-clockblocking";
import { solve as solve14 } from "./puzzle-14-new-super-marionette-bros";
import { solve as solve15 } from "./puzzle-15-wake-up-and-choose-violets";
import { solve as solve16 } from "./puzzle-16-who-watches-the-watchmen";
import { puzzlemasterDrunkTargets, solve as solve17 } from "./puzzle-17-the-missing-piece";
import { forcedX, solve as solve18 } from "./puzzle-18-x-and-the-city";
import { solve as solve19 } from "./puzzle-19-he-could-be-you-he-could-be-me";
import { solve as solve20 } from "./puzzle-20-the-three-wise-men";
import { solve as solve21 } from "./puzzle-21-eight-jugglers-juggling";
import { solve as solve22 } from "./puzzle-22-one-in-the-chamber";
import { solve as solve23 } from "./puzzle-23-goblincore";
import { solve as solve24 } from "./puzzle-24-the-ultimate-blunder";
import { solve as solve25 } from "./puzzle-25-clockdoku";
import { solve as solve26 } from "./puzzle-26-a-major-problem";
import { solve as solve27 } from "./puzzle-27-is-this-a-legion-game";
import { solve as solve28 } from "./puzzle-28-a-study-in-scarlet";
import { solve as solve29 } from "./puzzle-29-a-dreamer-im-not-the-only-one";
import { solve as solve30 } from "./puzzle-30-the-babel-fish-is-a-dead-giveaway";
import { solve as solve31 } from "./puzzle-31-no-your-other-left";
import { solve as solve32 } from "./puzzle-32-prepare-for-juggle-and-make-it-double";
import { solve as solve33 } from "./puzzle-33-twice-is-coincidence-thrice-is-proof";
import { solve as solve34 } from "./puzzle-34-the-vortox-conjecture";
import { solve as solve35 } from "./puzzle-35-typhon-season";
import { solve as solve36 } from "./puzzle-36-what-is-your-weapon-of-choice";
import { solve as solve37 } from "./puzzle-37-new-super-marionette-bros-u";
import { solve as solve38 } from "./puzzle-38-snakes-on-a-plane";
import { solve as solve39 } from "./puzzle-39-squid-game";
import { solve as solve40 } from "./puzzle-40-nine-lives";

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

  test("the savant strikes back has two worlds that differ only by Steph's outsider role", async () => {
    const worlds = await solve07();
    expect(worlds).toHaveLength(2);
    expect(new Set(worlds.map((world) => world.holder("Leviathan")))).toEqual(new Set(["Anna"]));
    expect(new Set(worlds.map((world) => world.holder("Goblin")))).toEqual(new Set(["Oscar"]));
    expect(new Set(worlds.map((world) => world.actualRole("Steph")))).toEqual(new Set(["Drunk", "Mutant"]));
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

  test("false is the new black forces demon and minion players", async () => {
    const worlds = await solve11();
    expect(worlds).toHaveLength(4);
    expect(new Set(worlds.map((world) => world.holder("Vortox")))).toEqual(new Set(["Aoife"]));
    expect(new Set(worlds.map((world) => world.holder("Cerenovus") ?? world.holder("Pit-Hag")))).toEqual(
      new Set(["Tom"]),
    );
  });

  test("thunderstruck 12a has unique solution", async () => {
    const worlds = await solve12a();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Vortox")).toBe("Jasmine");
    expect(worlds[0]?.holder("Spy")).toBe("Sarah");
    expect(worlds[0]?.holder("Lunatic")).toBe("Fraser");
  });

  test("thunderstruck 12b has unique solution", async () => {
    const worlds = await solve12b();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Vortox")).toBe("Oscar");
    expect(worlds[0]?.holder("Scarlet Woman")).toBe("Steph");
    expect(worlds[0]?.holder("Lunatic")).toBe("Anna");
  });

  test("clockblocking has unique solution", async () => {
    const worlds = await solve13();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Fraser");
    expect(worlds[0]?.holder("Baron")).toBe("Oscar");
    expect(worlds[0]?.holder("Drunk")).toBe("Tim");
  });

  test("new super marionette bros has unique solution", async () => {
    const worlds = await solve14();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Lav");
    expect(worlds[0]?.holder("Poisoner")).toBe("Lydia");
  });

  test("wake up and choose violets has unique solution", async () => {
    const worlds = await solve15();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Vortox")).toBe("Adam");
    expect(worlds[0]?.holder("Evil Twin")).toBe("Jasmine");
    expect(worlds[0]?.holder("Klutz")).toBe("Oscar");
  });

  test("who watches the watchmen has unique solution", async () => {
    const worlds = await solve16();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Oscar");
    expect(worlds[0]?.holder("Poisoner")).toBe("Fraser");
  });

  test("the missing piece forces the Puzzlemaster drunk target", async () => {
    const worlds = await solve17();
    expect(worlds).toHaveLength(4);
    expect(puzzlemasterDrunkTargets(worlds)).toEqual(["Steph"]);
  });

  test("x and the city has unique solution", async () => {
    const worlds = await solve18();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Leviathan")).toBe("Fraser");
    expect(worlds[0]?.holder("Xaan")).toBe("Olivia");
    expect(forcedX(worlds)).toBe(3);
  });

  test("he could be you he could be me has unique solution", async () => {
    const worlds = await solve19();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Olivia");
    expect(worlds[0]?.holder("Spy")).toBe("Fraser");
  });

  test("the three wise men has unique solution", async () => {
    const worlds = await solve20();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Balthazar");
    expect(worlds[0]?.holder("Baron")).toBe("Mary");
    expect(worlds[0]?.holder("Drunk")).toBe("Gabriel");
  });

  test("eight jugglers juggling has unique solution", async () => {
    const worlds = await solve21();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Leviathan")).toBe("Oscar");
    expect(worlds[0]?.holder("Goblin")).toBe("Tim");
    expect(worlds[0]?.holder("Drunk")).toBe("Aoife");
  });

  test("one in the chamber has unique solution", async () => {
    const worlds = await solve22();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Sarah");
    expect(worlds[0]?.holder("Baron")).toBe("Steph");
    expect(worlds[0]?.holder("Drunk")).toBe("You");
  });

  test("goblincore has unique solution", async () => {
    const worlds = await solve23();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Sula");
    expect(worlds[0]?.holder("Goblin")).toBe("Aoife");
    expect(worlds[0]?.holder("Lunatic")).toBe("Fraser");
  });

  test("the ultimate blunder has unique solution", async () => {
    const worlds = await solve24();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Adam");
    expect(worlds[0]?.holder("Poisoner")).toBe("Josh");
    expect(worlds[0]?.holder("Klutz")).toBe("Olivia");
  });

  test("clockdoku has unique solution", () => {
    const grids = solve25();
    expect(grids).toHaveLength(1);
    expect(grids[0]).toEqual([
      ["Empath", "Imp", "Recluse", "Saint", "Librarian", "Baron", "Chef"],
      ["Investigator", "Librarian", "Empath", "Chef", "Fortune Teller", "Imp", "Poisoner"],
      ["Librarian", "Baron", "Imp", "Recluse", "Saint", "Empath", "Fortune Teller"],
      ["Chef", "Recluse", "Saint", "Imp", "Baron", "Fortune Teller", "Empath"],
      ["Imp", "Chef", "Librarian", "Baron", "Recluse", "Saint", "Investigator"],
      ["Fortune Teller", "Saint", "Baron", "Empath", "Imp", "Recluse", "Librarian"],
      ["Poisoner", "Empath", "Chef", "Fortune Teller", "Investigator", "Librarian", "Imp"],
    ]);
  });

  test("a major problem forces the evil team", async () => {
    const worlds = await solve26();
    expect(worlds).toHaveLength(8);
    expect(new Set(worlds.map((world) => world.holder("Imp")))).toEqual(new Set(["Tom"]));
    expect(new Set(worlds.map((world) => world.holder("Poisoner")))).toEqual(new Set(["Matthew"]));
  });

  test("is this a legion game has unique solution", async () => {
    const worlds = await solve27();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Adam");
    expect(worlds[0]?.holder("Poisoner")).toBe("Fraser");
  });

  test("a study in scarlet has unique solution", async () => {
    const worlds = await solve28();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("No Dashii")).toBe("Olivia");
    expect(worlds[0]?.holder("Scarlet Woman")).toBe("Fraser");
    expect(worlds[0]?.holder("Drunk")).toBe("Matt");
  });

  test("a dreamer im not the only one has unique solution", async () => {
    const worlds = await solve29();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Adam");
    expect(worlds[0]?.holder("Poisoner")).toBe("Jasmine");
    expect(worlds[0]?.holder("Drunk")).toBe("Hannah");
  });

  test("the babel fish is a dead giveaway has unique paired solution", async () => {
    const solutions = await solve30();
    expect(solutions).toHaveLength(1);
    expect(solutions[0]?.atheistGame).toBe("left");
    expect(solutions[0]?.world.holder("Imp")).toBe("Owen");
    expect(solutions[0]?.world.holder("Spy")).toBe("Louisa");
    expect(solutions[0]?.world.holder("Drunk")).toBe("Finn");
  });

  test("no your other left has unique solution", async () => {
    const worlds = await solve31();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Adam");
    expect(worlds[0]?.holder("Baron")).toBe("Sarah");
    expect(worlds[0]?.holder("Drunk")).toBe("Tim");
    expect(worlds[0]?.holder("Recluse")).toBe("Fraser");
  });

  test("prepare for juggle and make it double has unique solution", async () => {
    const worlds = await solve32();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Olivia");
    expect(worlds[0]?.holder("Poisoner")).toBe("Matthew");
    expect(worlds[0]?.holder("Saint")).toBe("Fraser");
    expect(worlds[0]?.holder("Drunk")).toBeUndefined();
  });

  test("twice is coincidence thrice is proof has unique solution", async () => {
    const worlds = await solve33();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Tom");
    expect(worlds[0]?.holder("Poisoner")).toBe("Sula");
    expect(worlds[0]?.holder("Recluse")).toBe("Olivia");
    expect(worlds[0]?.holder("Drunk")).toBeUndefined();
  });

  test("the vortox conjecture has unique solution", async () => {
    const worlds = await solve34();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Vortox")).toBe("Sula");
    expect(worlds[0]?.holder("Witch")).toBe("Sarah");
  });

  test("typhon season has unique solution", async () => {
    const worlds = await solve35();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Lord of Typhon")).toBe("Olivia");
    expect(worlds[0]?.holder("Poisoner")).toBe("Sarah");
    expect(worlds[0]?.holder("Spy")).toBe("Oscar");
    expect(worlds[0]?.holder("Drunk")).toBe("Jasmine");
  });

  test("what is your weapon of choice has unique solution", async () => {
    const worlds = await solve36();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Fraser");
    expect(worlds[0]?.holder("Poisoner")).toBe("Oscar");
    expect(worlds[0]?.holder("Drunk")).toBeUndefined();
  });

  test("new super marionette bros u has unique solution", async () => {
    const worlds = await solve37();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Fraser");
    expect(worlds[0]?.holder("Poisoner")).toBe("Jasmine");
    expect(worlds[0]?.holder("Drunk")).toBe("Adam");
  });

  test("snakes on a plane has unique solution", async () => {
    const worlds = await solve38();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Dan");
    expect(worlds[0]?.holder("Baron")).toBe("Tim");
    expect(worlds[0]?.holder("Drunk")).toBe("Hannah");
  });

  test("squid game has unique solution", async () => {
    const worlds = await solve39();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("No Dashii")).toBe("Jasmine");
    expect(worlds[0]?.holder("Witch")).toBe("Hannah");
    expect(worlds[0]?.holder("Mutant")).toBe("Matt");
  });

  test("nine lives has unique solution", async () => {
    const worlds = await solve40();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.holder("Imp")).toBe("Adam");
    expect(worlds[0]?.holder("Baron")).toBe("Tim");
    expect(worlds[0]?.holder("Drunk")).toBe("Jasmine");
  });
});
