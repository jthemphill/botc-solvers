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
  Imp,
  Investigator,
  Librarian,
  Recluse,
  Saint,
  ScarletWoman,
  Slayer,
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
