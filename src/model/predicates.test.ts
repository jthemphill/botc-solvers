import { day } from "./model";
import { beforeAll, describe, expect, test } from "bun:test";
import { CharacterType } from "./core";
import { formatSolution, forcedRole } from "./display";
import { BOTCModel } from "./model";
import {
  Artist,
  Baron,
  Chef,
  Clockmaker,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Juggler,
  Knight,
  Librarian,
  NoDashii,
  Noble,
  Poisoner,
  Recluse,
  Savant,
  ScarletWoman,
  Seamstress,
  SnakeCharmer,
  Spy,
  VillageIdiot,
  Vortox,
  Witch,
  applyClaims,
  script,
} from "./characters";
import { chefCountRegistersAs, drunkBetweenTwoTownsfolk, registersAsRoleAmong } from "./predicates";
import { World, night } from "./model";
import { KissatBackend, type SatBackend } from "./sat";

const TEST_CHARACTERS = script(Imp, ScarletWoman, Drunk, Recluse, Investigator, Noble);
const POISON_CHARACTERS = script(Imp, Poisoner, Investigator);
const REGISTRATION_CHARACTERS = script(Imp, Spy, Poisoner, Drunk, Recluse, Chef, Librarian);

describe("predicates and helpers", () => {
  let backend: SatBackend;

  beforeAll(async () => {
    backend = await KissatBackend.create();
  });

  test("left neighbor is the next seated player", () => {
    const game = new BOTCModel(["A", "B", "C", "D"], {
      characters: TEST_CHARACTERS,
      backend,
    });

    expect(game.neighbors("A")).toEqual(["B", "D"]);
    expect(game.neighbors("C")).toEqual(["D", "B"]);
  });

  test("drunk can think they are townsfolk, not outsider", async () => {
    const valid = new BOTCModel(["A", "B"], { characters: TEST_CHARACTERS, backend });
    valid.addRoleClaim({ player: "A", apparentRole: "Investigator" });
    valid.fixActual("A", "Drunk");
    valid.fixActual("B", "Imp");
    expect(await valid.solveAll({ limit: 1 })).toHaveLength(1);

    const invalid = new BOTCModel(["A", "B"], { characters: TEST_CHARACTERS, backend });
    invalid.addRoleClaim({ player: "A", apparentRole: "Recluse" });
    invalid.fixActual("A", "Drunk");
    invalid.fixActual("B", "Imp");
    expect(await invalid.solveAll({ limit: 1 })).toEqual([]);
  });

  test("evil role claims exclude the exact apparent evil role", async () => {
    const valid = new BOTCModel(["A", "B", "C"], { characters: script(Imp, ScarletWoman, Chef), backend });
    valid.addRoleClaim({ player: "A", apparentRole: "Imp" });
    valid.fixActual("A", ScarletWoman);
    valid.fixActual("B", Imp);
    valid.fixActual("C", Chef);
    expect(await valid.solveAll({ limit: 1 })).toHaveLength(1);

    const invalid = new BOTCModel(["A", "B", "C"], { characters: script(Imp, ScarletWoman, Chef), backend });
    invalid.addRoleClaim({ player: "A", apparentRole: "Imp" });
    invalid.fixActual("A", Imp);
    invalid.fixActual("B", ScarletWoman);
    invalid.fixActual("C", Chef);
    expect(await invalid.solveAll({ limit: 1 })).toEqual([]);
  });

  test("actual Drunk is an info malfunction source", async () => {
    const drunk = new BOTCModel(["A", "B", "C"], { characters: script(Imp, Drunk, Empath, Chef), backend });
    drunk.fixActual("A", Drunk);
    drunk.fixActual("B", Imp);
    drunk.fixActual("C", Chef);
    applyClaims(drunk, [new Empath({ name: "A", count: 0 })]);
    expect(await drunk.solveAll({ limit: 1 })).toHaveLength(1);

    const sober = new BOTCModel(["A", "B", "C"], { characters: script(Imp, Drunk, Empath), backend });
    sober.fixActual("A", Empath);
    sober.fixActual("B", Imp);
    sober.fixActual("C", Drunk);
    applyClaims(sober, [new Empath({ name: "A", count: 0 })]);
    expect(await sober.solveAll({ limit: 1 })).toEqual([]);
  });

  test("poisoning is scoped and truthful claims use matching timing", async () => {
    const game = new BOTCModel(["A", "B", "C"], { characters: POISON_CHARACTERS, backend });
    game.fixActual("A", "Poisoner");
    game.fixActual("B", "Imp");
    game.fixActual("C", "Investigator");
    game.addPoisonerEffect(day(1));
    game.addPoisonerEffect(day(2));
    game.fixPoisoned("B", true, day(1));
    game.fixPoisoned("C", true, day(2));
    const worlds = await game.solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("B", day(1))).toBe(true);
    expect(worlds[0]?.isPoisoned("B", day(2))).toBe(false);
    expect(worlds[0]?.isPoisoned("C", day(2))).toBe(true);
    expect(worlds[0]?.isPoisoned("B")).toBe(false);

    const claim = new BOTCModel(["A", "B", "C"], { characters: POISON_CHARACTERS, backend });
    claim.fixActual("A", "Investigator");
    claim.fixActual("B", "Imp");
    claim.fixActual("C", "Poisoner");
    claim.fixPoisoned("A", true, day(1));
    claim.fixPoisoned("A", false, day(2));
    claim.addTruthfulInfoClaim("A", "Investigator", claim.actualIs("B", "Investigator"), {
      timing: "day_2",
    });
    expect(await claim.solveAll({ limit: 1 })).toEqual([]);
  });

  test("registration remains separate from actual worlds", async () => {
    const spy = new BOTCModel(["A", "B"], { characters: REGISTRATION_CHARACTERS, backend });
    spy.fixActual("A", "Spy");
    spy.fixActual("B", "Imp");
    spy.addTruth(spy.registersAsRole("A", "Drunk", "librarian"));
    spy.addFalse(spy.roleInPlay("Drunk"));
    expect((await spy.solveAll())[0]?.holder("Spy")).toBe("A");

    const recluse = new BOTCModel(["A", "B", "C"], { characters: REGISTRATION_CHARACTERS, backend });
    recluse.fixActual("A", "Recluse");
    recluse.fixActual("B", "Chef");
    recluse.fixActual("C", "Librarian");
    recluse.addTruth(registersAsRoleAmong(recluse, ["A", "B"], "Imp", "investigator"));
    recluse.addFalse(recluse.roleInPlay("Imp"));
    expect((await recluse.solveAll())[0]?.holder("Recluse")).toBe("A");

    const dedup = new BOTCModel(["A", "B"], { characters: REGISTRATION_CHARACTERS, backend });
    dedup.fixActual("A", "Spy");
    dedup.fixActual("B", "Imp");
    dedup.addTruth(
      dedup.anyOf(
        [dedup.registersAsRole("A", "Drunk", "librarian"), dedup.registersAsRole("A", "Chef", "washerwoman")],
        "at_least_one_registration_choice",
      ),
    );
    expect(await dedup.solveAll()).toHaveLength(1);
  });

  test("model-owned sober and healthy checks include No Dashii adjacency", async () => {
    const poisonedInfo = new BOTCModel(["A", "B", "C", "D"], {
      characters: script(NoDashii, Chef, Empath, Investigator),
      backend,
    });
    poisonedInfo.fixActual("A", NoDashii);
    poisonedInfo.fixActual("B", Chef);
    poisonedInfo.fixActual("C", Empath);
    poisonedInfo.fixActual("D", Investigator);
    poisonedInfo.addTruthfulInfoClaim("B", Chef, poisonedInfo.actualIs("C", NoDashii), {
      timing: "night_1",
    });
    expect(await poisonedInfo.solveAll()).toHaveLength(1);

    const soberInfo = new BOTCModel(["A", "B", "C", "D"], {
      characters: script(NoDashii, Chef, Empath, Investigator),
      backend,
    });
    soberInfo.fixActual("A", NoDashii);
    soberInfo.fixActual("B", Chef);
    soberInfo.fixActual("C", Empath);
    soberInfo.fixActual("D", Investigator);
    soberInfo.addTruthfulInfoClaim("C", Empath, soberInfo.actualIs("B", NoDashii), {
      timing: "night_1",
    });
    expect(await soberInfo.solveAll()).toEqual([]);
  });

  test("timing role state can add and remove roles", async () => {
    const game = new BOTCModel(["A", "B", "C"], { characters: script(Chef, Imp, ScarletWoman), backend });
    game.fixActual("A", Chef);
    game.fixActual("B", Imp);
    game.fixActual("C", ScarletWoman);
    game.addTruth(game.hasRoleAt("B", Imp, night(1)));
    game.removeRoleAt("B", Imp, night(2));
    game.addRoleAt("C", Imp, night(2));
    game.addTruth(game.isDemonAt("C", night(2)));
    game.addFalse(game.isDemonAt("B", night(2)));
    expect(await game.solveAll({ limit: 1 })).toHaveLength(1);
  });

  test("role timing defaults infer setup and nightly claim timing", async () => {
    const setupInfo = new BOTCModel(["A", "B", "C"], {
      characters: script(Chef, Imp, Poisoner),
      backend,
    });
    setupInfo.fixActual("A", Chef);
    setupInfo.fixActual("B", Imp);
    setupInfo.fixActual("C", Poisoner);
    setupInfo.fixPoisoned("A", true, night(1));
    applyClaims(setupInfo, [new Chef({ name: "A", count: 0 })]);
    expect(await setupInfo.solveAll({ limit: 1 })).toHaveLength(1);

    const recurringInfo = new BOTCModel(["A", "B", "C"], {
      characters: script(FortuneTeller, Imp, Poisoner),
      backend,
    });
    recurringInfo.fixActual("A", FortuneTeller);
    recurringInfo.fixActual("B", Imp);
    recurringInfo.fixActual("C", Poisoner);
    recurringInfo.fixPoisoned("A", true, night(2));
    applyClaims(recurringInfo, [
      new FortuneTeller({
        name: "A",
        checks: [
          { left: "B", right: "C", yes: true },
          { left: "B", right: "C", yes: false },
        ],
      }),
    ]);
    expect(await recurringInfo.solveAll({ limit: 1 })).toHaveLength(1);
  });

  test("Fortune Teller checks share a single red herring", async () => {
    const game = new BOTCModel(["FT", "Red", "Demon", "Other"], {
      characters: script(FortuneTeller, Imp, Chef, Investigator),
      backend,
    });
    game.fixActual("FT", FortuneTeller);
    game.fixActual("Red", Chef);
    game.fixActual("Demon", Imp);
    game.fixActual("Other", Investigator);
    applyClaims(game, [
      new FortuneTeller({
        name: "FT",
        checks: [
          { left: "Red", right: "Other", yes: true },
          { left: "FT", right: "Other", yes: false },
        ],
      }),
    ]);

    expect(await game.solveAll({ limit: 1 })).toHaveLength(1);
  });

  test("ambiguous one-shot information requires explicit timing", () => {
    const game = new BOTCModel(["A", "B", "C"], { characters: script(Seamstress, Imp, Chef), backend });
    expect(() => applyClaims(game, [new Seamstress({ name: "A", aligned: true, among: ["B", "C"] })])).toThrow(
      "A's Seamstress info claim needs an explicit night or day.",
    );
  });

  test("Knight claims cannot include more than two no-demon players", () => {
    expect(() => new Knight({ name: "A", noDemonAmong: ["A", "B", "C"] })).toThrow(
      "Knight claims can include at most 2 non-Demon players.",
    );
  });

  test("character helper claims", async () => {
    const game = new BOTCModel(["A", "B", "C", "D"], {
      characters: script(Imp, ScarletWoman, Chef, Empath),
      backend,
    });
    game.fixActual("A", Imp);
    game.fixActual("B", ScarletWoman);
    game.fixActual("C", Chef);
    game.fixActual("D", Empath);
    game.addTruth(Chef.learnsCount(game, 1, "chef"));
    game.addTruth(Empath.learnsCount(game, "D", 1, "empath"));
    expect(await game.solveAll()).toHaveLength(1);

    const clockmakerScript = script(Imp, ScarletWoman, Baron, Clockmaker, Chef);
    const nearestTwo = new BOTCModel(["Demon", "Townsfolk", "Minion A", "Minion B", "Clockmaker"], {
      characters: clockmakerScript,
      backend,
    });
    nearestTwo.fixActual("Demon", Imp);
    nearestTwo.fixActual("Townsfolk", Chef);
    nearestTwo.fixActual("Minion A", ScarletWoman);
    nearestTwo.fixActual("Minion B", Baron);
    nearestTwo.fixActual("Clockmaker", Clockmaker);
    nearestTwo.addTruth(Clockmaker.learnsDemonMinionDistance(nearestTwo, 2, "clockmaker_two"));
    expect(await nearestTwo.solveAll({ limit: 1 })).toHaveLength(1);

    const closerMinion = new BOTCModel(["Demon", "Minion A", "Townsfolk", "Minion B", "Clockmaker"], {
      characters: clockmakerScript,
      backend,
    });
    closerMinion.fixActual("Demon", Imp);
    closerMinion.fixActual("Minion A", ScarletWoman);
    closerMinion.fixActual("Townsfolk", Chef);
    closerMinion.fixActual("Minion B", Baron);
    closerMinion.fixActual("Clockmaker", Clockmaker);
    closerMinion.addTruth(Clockmaker.learnsDemonMinionDistance(closerMinion, 2, "clockmaker_two"));
    expect(await closerMinion.solveAll({ limit: 1 })).toEqual([]);

    const claims = [
      new Savant({
        timing: "day_1",
        name: "A",
        statements: [(model) => [model.actualIs("B", Imp), model.actualIs("C", Imp)]],
      }),
    ];
    const savant = new BOTCModel(["A", "B", "C"], {
      characters: script(Imp, Drunk, Savant),
      uniqueCharacters: false,
      backend,
    });
    applyClaims(savant, claims);
    savant.fixActual("A", Savant);
    savant.fixActual("B", Imp);
    savant.fixActual("C", Imp);
    expect(await savant.solveAll({ limit: 1 })).toEqual([]);
  });

  test("Vortox automatically falsifies Townsfolk information except Snake Charmer", async () => {
    const characters = script(Vortox, Witch, Clockmaker, Artist, SnakeCharmer);
    const makeGame = () => {
      const game = new BOTCModel(["Clockmaker", "Demon", "Minion", "Artist", "Snake Charmer"], {
        characters,
        backend,
      });
      game.fixActual("Clockmaker", Clockmaker);
      game.fixActual("Demon", Vortox);
      game.fixActual("Minion", Witch);
      game.fixActual("Artist", Artist);
      game.fixActual("Snake Charmer", SnakeCharmer);
      return game;
    };

    const falseClockmakerInfo = makeGame();
    applyClaims(falseClockmakerInfo, [
      new Clockmaker({ name: "Clockmaker", distance: 2 }),
      new SnakeCharmer({ name: "Snake Charmer", checked: "Demon", demon: true }),
    ]);
    expect(await falseClockmakerInfo.solveAll({ limit: 1 })).toHaveLength(1);

    const trueClockmakerInfo = makeGame();
    applyClaims(trueClockmakerInfo, [new Clockmaker({ name: "Clockmaker", distance: 1 })]);
    expect(await trueClockmakerInfo.solveAll({ limit: 1 })).toEqual([]);

    const falseSnakeCharmerCheck = makeGame();
    applyClaims(falseSnakeCharmerCheck, [new SnakeCharmer({ name: "Snake Charmer", checked: "Demon", demon: false })]);
    expect(await falseSnakeCharmerCheck.solveAll({ limit: 1 })).toEqual([]);
  });

  test("village idiot can have up to three copies under default uniqueness", async () => {
    const threeVillageIdiots = new BOTCModel(["A", "B", "C", "D"], {
      characters: script(Imp, VillageIdiot, Chef, Empath),
      backend,
    });
    threeVillageIdiots.fixActual("A", VillageIdiot);
    threeVillageIdiots.fixActual("B", VillageIdiot);
    threeVillageIdiots.fixActual("C", VillageIdiot);
    threeVillageIdiots.fixActual("D", Imp);
    expect(await threeVillageIdiots.solveAll({ limit: 1 })).toHaveLength(1);

    const fourVillageIdiots = new BOTCModel(["A", "B", "C", "D"], {
      characters: script(Imp, VillageIdiot, Chef, Empath),
      backend,
    });
    for (const player of fourVillageIdiots.players) fourVillageIdiots.fixActual(player, VillageIdiot);
    expect(await fourVillageIdiots.solveAll({ limit: 1 })).toEqual([]);
  });

  test("display formatting", () => {
    const world = new World(
      new Map([
        ["Alice", "Imp"],
        ["Bob", "Drunk"],
      ]),
      new Map([
        ["Alice", "Fortune Teller"],
        ["Bob", "Drunk"],
      ]),
      new Set(),
      new Map([[day(1), new Set(["Bob"])]]),
    );
    expect(
      formatSolution([world], ["Alice", "Bob"], {
        timing: day(1),
        forcedRoles: [forcedRole("Demon", "Imp", { includeRole: true }), "Drunk"],
      }),
    ).toBe(
      "1 satisfying world(s)\n\nWorld 1\n  Alice: 👹 Imp (appears as 🔮 Fortune Teller)\n  Bob: 🍺 Drunk poisoned\n\nForced facts\n  Demon: Alice (👹 Imp)\n  🍺 Drunk: Bob",
    );
    const alternateDemon = new World(
      new Map([
        ["Alice", "Po"],
        ["Bob", "Drunk"],
      ]),
      new Map(),
      new Set(),
    );
    expect(
      formatSolution([world, alternateDemon], ["Alice", "Bob"], {
        forcedRoles: [forcedRole("Demon", ["Imp", "Po"])],
      })
        .split("\n")
        .at(-1),
    ).toBe("  Demon: Alice");
  });
});
