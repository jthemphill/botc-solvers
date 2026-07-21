import { beforeAll, describe, expect, test } from "bun:test";
import { CharacterType, type RoleRef, roleCharacterType, roleName } from "./core";
import type { World } from "./model";
import { KissatBackend, type SatBackend } from "./sat";
import { buildPuzzleModel, standardSetupCounts } from "./setup";
import {
  Balloonist,
  Baron,
  Butler,
  Chef,
  Drunk,
  Empath,
  FangGu,
  Fool,
  Godfather,
  Goon,
  Imp,
  Investigator,
  Klutz,
  Librarian,
  Leviathan,
  LordOfTyphon,
  Mutant,
  Marionette,
  Poisoner,
  Professor,
  Recluse,
  Saint,
  ScarletWoman,
  Slayer,
  Spy,
  Washerwoman,
  Vortox,
  Vigormortis,
  Witch,
  Xaan,
  script,
} from "./characters";

describe("standard setup lowering", () => {
  let backend: SatBackend;

  beforeAll(async () => {
    backend = await KissatBackend.create();
  });

  test("exposes the standard player count table", () => {
    expect(standardSetupCounts(5)).toEqual({
      [CharacterType.Townsfolk]: 3,
      [CharacterType.Outsider]: 0,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });
    expect(standardSetupCounts(15)).toEqual({
      [CharacterType.Townsfolk]: 9,
      [CharacterType.Outsider]: 2,
      [CharacterType.Minion]: 3,
      [CharacterType.Demon]: 1,
    });
  });

  test("rejects unsupported standard setup player counts", () => {
    expect(() =>
      buildPuzzleModel({ players: players(4), characters: script(Imp, ScarletWoman, Chef, Empath) }, backend),
    ).toThrow("Standard setup is only defined for 5-15 players");
  });

  test("applies standard type counts without setup modifiers", async () => {
    const characters = script(Imp, ScarletWoman, Drunk, Recluse, Chef, Empath, Investigator, Librarian, Slayer);
    const game = buildPuzzleModel({ players: players(7), characters }, backend);
    const [world] = await game.solveAll({ limit: 1 });
    expect(world).toBeDefined();
    expect(characterTypeCounts(world as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 0,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });
  });

  test("conditions Baron outsider modification on Baron being in play", async () => {
    const characters = script(
      Imp,
      Baron,
      ScarletWoman,
      Drunk,
      Recluse,
      Saint,
      Chef,
      Empath,
      Investigator,
      Librarian,
      Slayer,
      Washerwoman,
    );

    const withBaron = buildPuzzleModel({ players: players(7), characters }, backend);
    withBaron.fixActual("A", Baron);
    expect(characterTypeCounts((await withBaron.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 3,
      [CharacterType.Outsider]: 2,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });

    const withoutBaron = buildPuzzleModel({ players: players(7), characters }, backend);
    withoutBaron.addFalse(withoutBaron.roleInPlay(Baron));
    expect(characterTypeCounts((await withoutBaron.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 0,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });
  });

  test("conditions Fang Gu outsider modification on Fang Gu being in play", async () => {
    const characters = script(
      FangGu,
      Vortox,
      Witch,
      Mutant,
      Klutz,
      Chef,
      Empath,
      Investigator,
      Librarian,
      Slayer,
      Washerwoman,
    );

    const withFangGu = buildPuzzleModel({ players: players(8), characters }, backend);
    withFangGu.fixActual("A", FangGu);
    expect(characterTypeCounts((await withFangGu.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 4,
      [CharacterType.Outsider]: 2,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });

    const withoutFangGu = buildPuzzleModel({ players: players(8), characters }, backend);
    withoutFangGu.addFalse(withoutFangGu.roleInPlay(FangGu));
    expect(characterTypeCounts((await withoutFangGu.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 1,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });
  });

  test("conditions Vigormortis outsider modification on Vigormortis being in play", async () => {
    const characters = script(
      Vigormortis,
      Vortox,
      Witch,
      Mutant,
      Klutz,
      Chef,
      Empath,
      Investigator,
      Librarian,
      Slayer,
      Washerwoman,
    );

    const withVigormortis = buildPuzzleModel({ players: players(8), characters }, backend);
    withVigormortis.fixActual("A", Vigormortis);
    expect(characterTypeCounts((await withVigormortis.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 6,
      [CharacterType.Outsider]: 0,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });

    const withoutVigormortis = buildPuzzleModel({ players: players(8), characters }, backend);
    withoutVigormortis.addFalse(withoutVigormortis.roleInPlay(Vigormortis));
    expect(characterTypeCounts((await withoutVigormortis.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 1,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });
  });

  test("conditions Godfather outsider modification on Godfather being in play", async () => {
    const characters = script(
      Imp,
      Godfather,
      Poisoner,
      Goon,
      Drunk,
      Professor,
      Fool,
      Chef,
      Empath,
      Investigator,
      Librarian,
      Slayer,
      Washerwoman,
    );

    const withGodfather = buildPuzzleModel({ players: players(8), characters }, backend);
    withGodfather.fixActual("A", Godfather);
    expect(characterTypeCounts((await withGodfather.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 4,
      [CharacterType.Outsider]: 2,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });

    const withoutGodfather = buildPuzzleModel({ players: players(8), characters }, backend);
    withoutGodfather.addFalse(withoutGodfather.roleInPlay(Godfather));
    expect(characterTypeCounts((await withoutGodfather.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 1,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });
  });

  test("allows Balloonist in play with or without the outsider modification", async () => {
    const characters = script(
      Imp,
      ScarletWoman,
      Drunk,
      Recluse,
      Saint,
      Balloonist,
      Chef,
      Empath,
      Investigator,
      Librarian,
      Slayer,
    );

    const modified = buildPuzzleModel({ players: players(8), characters }, backend);
    modified.fixActual("A", Balloonist);
    modified.addTruth(modified.outsiderCountIs(2));
    expect(characterTypeCounts((await modified.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 4,
      [CharacterType.Outsider]: 2,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });

    const unmodified = buildPuzzleModel({ players: players(8), characters }, backend);
    unmodified.fixActual("A", Balloonist);
    unmodified.addTruth(unmodified.outsiderCountIs(1));
    expect(characterTypeCounts((await unmodified.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 1,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });

    const absent = buildPuzzleModel({ players: players(8), characters }, backend);
    absent.addFalse(absent.roleInPlay(Balloonist));
    expect(characterTypeCounts((await absent.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 1,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });
  });

  test("combines Baron and Balloonist outsider modifications", async () => {
    const characters = script(
      Imp,
      Baron,
      ScarletWoman,
      Drunk,
      Recluse,
      Saint,
      Butler,
      Balloonist,
      Chef,
      Empath,
      Investigator,
      Librarian,
    );
    const game = buildPuzzleModel({ players: players(8), characters }, backend);
    game.fixActual("A", Baron);
    game.fixActual("B", Balloonist);
    game.addTruth(game.outsiderCountIs(4));
    expect(characterTypeCounts((await game.solveAll({ limit: 1 }))[0] as World, characters)).toEqual({
      [CharacterType.Townsfolk]: 2,
      [CharacterType.Outsider]: 4,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });
  });

  test("Lord of Typhon setup allows extra outsiders and adds a minion", async () => {
    const characters = script(
      Imp,
      LordOfTyphon,
      Poisoner,
      Spy,
      Drunk,
      Recluse,
      Saint,
      Butler,
      Chef,
      Empath,
      Investigator,
      Librarian,
      Slayer,
    );
    const game = buildPuzzleModel({ players: players(8), characters }, backend);
    game.fixActual("A", LordOfTyphon);
    game.addTruth(game.outsiderCountIs(2));

    const world = (await game.solveAll({ limit: 1 }))[0] as World;

    expect(world).toBeDefined();
    expect(characterTypeCounts(world, characters)).toEqual({
      [CharacterType.Townsfolk]: 3,
      [CharacterType.Outsider]: 2,
      [CharacterType.Minion]: 2,
      [CharacterType.Demon]: 1,
    });
  });

  test("Lord of Typhon with two minions sits between them", async () => {
    const characters = script(
      Imp,
      LordOfTyphon,
      Poisoner,
      Spy,
      Drunk,
      Recluse,
      Saint,
      Butler,
      Chef,
      Empath,
      Investigator,
      Librarian,
      Slayer,
    );
    const valid = buildPuzzleModel({ players: players(8), characters }, backend);
    valid.fixActual("A", LordOfTyphon);
    valid.fixActual("B", Poisoner);
    valid.fixActual("H", Spy);
    expect(await valid.solveAll({ limit: 1 })).toHaveLength(1);

    const invalid = buildPuzzleModel({ players: players(8), characters }, backend);
    invalid.fixActual("A", LordOfTyphon);
    invalid.fixActual("C", Poisoner);
    invalid.fixActual("D", Spy);
    expect(await invalid.solveAll({ limit: 1 })).toEqual([]);
  });

  test("Lord of Typhon keeps three minions in one continuous line", async () => {
    const characters = script(
      LordOfTyphon,
      Poisoner,
      Spy,
      Baron,
      Drunk,
      Recluse,
      Saint,
      Chef,
      Empath,
      Investigator,
      Librarian,
    );
    const game = buildPuzzleModel({ players: players(10), characters }, backend);
    game.fixActual("A", LordOfTyphon);
    game.fixActual("C", Poisoner);
    game.fixActual("E", Spy);
    game.fixActual("G", Baron);

    expect(await game.solveAll({ limit: 1 })).toEqual([]);
  });

  test("Xaan setup allows the Outsider count to define X", async () => {
    const characters = script(Leviathan, Xaan, Drunk, Recluse, Saint, Chef, Empath, Investigator, Librarian);
    const game = buildPuzzleModel({ players: players(8), characters }, backend);
    game.fixActual("A", Xaan);
    game.addTruth(game.outsiderCountIs(3));

    const world = (await game.solveAll({ limit: 1 }))[0] as World;

    expect(world).toBeDefined();
    expect(characterTypeCounts(world, characters)).toEqual({
      [CharacterType.Townsfolk]: 3,
      [CharacterType.Outsider]: 3,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    });
  });

  test("Marionette neighbors the Demon", async () => {
    const characters = script(Imp, Marionette, Drunk, Recluse, Saint, Chef, Empath, Investigator, Librarian, Slayer);

    const valid = buildPuzzleModel({ players: players(7), characters }, backend);
    valid.fixActual("A", Marionette);
    valid.fixActual("B", Imp);
    expect(await valid.solveAll({ limit: 1 })).toHaveLength(1);

    const invalid = buildPuzzleModel({ players: players(7), characters }, backend);
    invalid.fixActual("A", Marionette);
    invalid.fixActual("C", Imp);
    expect(await invalid.solveAll({ limit: 1 })).toEqual([]);
  });
});

function players(count: number): string[] {
  return Array.from({ length: count }, (_ignored, index) => String.fromCharCode("A".charCodeAt(0) + index));
}

function characterTypeCounts(world: World, characters: readonly RoleRef[]): Record<CharacterType, number> {
  const types = new Map(characters.map((character) => [roleName(character), roleCharacterType(character)]));
  const result = {
    [CharacterType.Townsfolk]: 0,
    [CharacterType.Outsider]: 0,
    [CharacterType.Minion]: 0,
    [CharacterType.Demon]: 0,
  };
  for (const actualRole of world.actual.values()) {
    const characterType = types.get(actualRole);
    if (characterType === undefined) throw new Error(`Unknown role in world: ${actualRole}`);
    result[characterType] += 1;
  }
  return result;
}
