import { type RoleRef, roleCharacterType, roleName } from "./core";
import type { BoolVar, BOTCModel, Timing } from "./model";

export function exactlyNRegisteredEvil(game: BOTCModel, players: readonly string[], count: number): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.registersAsEvil(player)),
    count,
  );
}

export function differentAlignments(game: BOTCModel, left: string, right: string): BoolVar {
  return game.xor(game.registersAsEvil(left), game.registersAsEvil(right));
}

export function sameAlignment(game: BOTCModel, left: string, right: string): BoolVar {
  return game.not(differentAlignments(game, left, right));
}

export function differentAlignmentsAt(game: BOTCModel, left: string, right: string, timing: Timing): BoolVar {
  const registersAsEvilAt = (player: string) =>
    game.hasAlignmentOverrideAt(player, timing) ? game.isEvilAt(player, timing) : game.registersAsEvil(player);
  return game.xor(registersAsEvilAt(left), registersAsEvilAt(right));
}

export function sameAlignmentAt(game: BOTCModel, left: string, right: string, timing: Timing): BoolVar {
  return game.not(differentAlignmentsAt(game, left, right, timing));
}

export function differentCharacterTypes(game: BOTCModel, left: string, right: string): BoolVar {
  const sameTypeOptions: BoolVar[] = [];
  const types = new Set([...game.characters.values()].map(roleCharacterType));
  for (const characterType of types) {
    sameTypeOptions.push(
      game.allOf([game.hasCharacterType(left, characterType), game.hasCharacterType(right, characterType)]),
    );
  }
  return game.not(game.anyOf(sameTypeOptions));
}

export function chefCountRegistersAs(game: BOTCModel, count: number): BoolVar {
  const evilPairs = game
    .adjacentPairs()
    .map(([left, right]) => game.allOf([game.registersAsEvil(left), game.registersAsEvil(right)]));
  return game.boolSumEquals(evilPairs, count);
}

export function registersAsRoleAmong(game: BOTCModel, players: readonly string[], role: RoleRef): BoolVar {
  const roleRef = roleName(role);
  return game.anyOf(players.map((player) => game.registersAsRole(player, roleRef)));
}

export function drunkBetweenTwoTownsfolk(game: BOTCModel): BoolVar {
  const possibilities = game.players.map((player) => {
    const [left, right] = game.neighbors(player);
    return game.allOf([game.actualIs(player, "Drunk"), game.isTownsfolk(left), game.isTownsfolk(right)]);
  });
  return game.anyOf(possibilities);
}
