import { beforeAll, describe, expect, test } from "bun:test";
import { CharacterType } from "../src/core";
import { formatSolution, forcedRole } from "../src/display";
import { BOTCModel } from "../src/model";
import {
  Chef,
  Drunk,
  Empath,
  Imp,
  Investigator,
  Juggler,
  Librarian,
  Noble,
  Poisoner,
  Recluse,
  Savant,
  ScarletWoman,
  Spy,
  VillageIdiot,
  applyClaims,
  script,
} from "../src/characters";
import { chefCountRegistersAs, drunkBetweenTwoTownsfolk, registersAsRoleAmong } from "../src/predicates";
import { World } from "../src/model";
import { KissatBackend, type SatBackend } from "../src/sat";

const TEST_CHARACTERS = script(Imp, ScarletWoman, Drunk, Recluse, Investigator, Noble);
const POISON_CHARACTERS = script(Imp, Poisoner, Investigator);
const REGISTRATION_CHARACTERS = script(Imp, Spy, Poisoner, Drunk, Recluse, Chef, Librarian);

describe("predicates and helpers", () => {
  let backend: SatBackend;

  beforeAll(async () => {
    backend = await KissatBackend.create();
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

  test("poisoning is scoped and truthful claims use matching context", async () => {
    const game = new BOTCModel(["A", "B", "C"], { characters: POISON_CHARACTERS, backend });
    game.fixActual("A", "Poisoner");
    game.fixActual("B", "Imp");
    game.fixActual("C", "Investigator");
    game.addPoisonerEffect("day_1");
    game.addPoisonerEffect("day_2");
    game.fixPoisoned("B", true, "day_1");
    game.fixPoisoned("C", true, "day_2");
    const worlds = await game.solveAll();
    expect(worlds).toHaveLength(1);
    expect(worlds[0]?.isPoisoned("B", "day_1")).toBe(true);
    expect(worlds[0]?.isPoisoned("B", "day_2")).toBe(false);
    expect(worlds[0]?.isPoisoned("C", "day_2")).toBe(true);
    expect(worlds[0]?.isPoisoned("B")).toBe(false);

    const claim = new BOTCModel(["A", "B", "C"], { characters: POISON_CHARACTERS, backend });
    claim.fixActual("A", "Investigator");
    claim.fixActual("B", "Imp");
    claim.fixActual("C", "Poisoner");
    claim.fixPoisoned("A", true, "day_1");
    claim.fixPoisoned("A", false, "day_2");
    claim.addTruthfulInfoClaim("A", "Investigator", claim.actualIs("B", "Investigator"), { poisonContext: "day_2" });
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

  test("character helper claims", async () => {
    const game = new BOTCModel(["A", "B", "C", "D"], {
      characters: script(Imp, ScarletWoman, Chef, Empath),
      seating: ["A", "B", "C", "D"],
      backend,
    });
    game.fixActual("A", Imp);
    game.fixActual("B", ScarletWoman);
    game.fixActual("C", Chef);
    game.fixActual("D", Empath);
    game.addTruth(Chef.learnsCount(game, 1, "chef"));
    game.addTruth(Empath.learnsCount(game, "D", 1, "empath"));
    expect(await game.solveAll()).toHaveLength(1);

    const claims = [
      new Savant({ name: "A", statements: [(model) => [model.actualIs("B", Imp), model.actualIs("C", Imp)]] }),
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
      ["Alice", "Bob"],
      new Map([["day_1", new Set(["Bob"])]]),
    );
    expect(
      formatSolution([world], ["Alice", "Bob"], {
        poisonContext: "day_1",
        forcedRoles: [forcedRole("Demon", "Imp", { includeRole: true }), "Drunk"],
      }),
    ).toBe(
      "1 satisfying world(s)\n\nWorld 1\n  Alice: Imp (appears as Fortune Teller)\n  Bob: Drunk poisoned\n\nForced facts\n  Demon: Alice (Imp)\n  Drunk: Bob",
    );
    const alternateDemon = new World(
      new Map([
        ["Alice", "Po"],
        ["Bob", "Drunk"],
      ]),
      new Map(),
      new Set(),
      ["Alice", "Bob"],
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
