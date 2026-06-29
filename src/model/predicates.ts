import { CharacterType, type RoleRef, roleCharacterType, roleName } from "./core";
import type { BoolVar, BOTCModel } from "./model";

export function exactlyNEvil(game: BOTCModel, players: readonly string[], count: number): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.isEvil(player)),
    count,
    `exactly_${count}_evil_among_${players.join("_")}`,
  );
}

export function exactlyNRegisteredEvil(game: BOTCModel, players: readonly string[], count: number): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.registersAsEvil(player, `registered_evil_${players.join("_")}`)),
    count,
    `exactly_${count}_registered_evil_among_${players.join("_")}`,
  );
}

export function differentAlignments(game: BOTCModel, left: string, right: string): BoolVar {
  return game.xor(
    game.registersAsEvil(left, `${left}_${right}_different_alignments_left`),
    game.registersAsEvil(right, `${left}_${right}_different_alignments_right`),
    `${left}_${right}_different_alignments`,
  );
}

export function sameAlignment(game: BOTCModel, left: string, right: string): BoolVar {
  return game.not(differentAlignments(game, left, right), `${left}_${right}_same_alignment`);
}

export function differentCharacterTypes(game: BOTCModel, left: string, right: string): BoolVar {
  const sameTypeOptions: BoolVar[] = [];
  const types = new Set([...game.characters.values()].map(roleCharacterType));
  for (const characterType of types) {
    sameTypeOptions.push(
      game.allOf(
        [game.hasCharacterType(left, characterType), game.hasCharacterType(right, characterType)],
        `${left}_${right}_both_${characterType}`,
      ),
    );
  }
  return game.not(
    game.anyOf(sameTypeOptions, `${left}_${right}_same_character_type`),
    `${left}_${right}_different_character_types`,
  );
}

export function chefCountIs(game: BOTCModel, count: number): BoolVar {
  const evilPairs = game
    .adjacentPairs()
    .map(([left, right]) => game.allOf([game.isEvil(left), game.isEvil(right)], `${left}_${right}_evil_pair`));
  return game.boolSumEquals(evilPairs, count, `chef_count_is_${count}`);
}

export function chefCountRegistersAs(game: BOTCModel, count: number, name: string): BoolVar {
  const evilPairs = game
    .adjacentPairs()
    .map(([left, right]) =>
      game.allOf(
        [
          game.registersAsEvil(left, `${name}_${left}_${right}_left`),
          game.registersAsEvil(right, `${name}_${left}_${right}_right`),
        ],
        `${name}_${left}_${right}_evil_pair`,
      ),
    );
  return game.boolSumEquals(evilPairs, count, `${name}_chef_count_is_${count}`);
}

export function registersAsRoleAmong(
  game: BOTCModel,
  players: readonly string[],
  role: RoleRef,
  name: string,
): BoolVar {
  const roleRef = roleName(role);
  return game.anyOf(
    players.map((player) => game.registersAsRole(player, roleRef, name)),
    `${name}_${players.join("_")}_registers_as_${roleRef}`,
  );
}

export function sitsNextToEvil(game: BOTCModel, player: string): BoolVar {
  return game.sitsNextToEvil(player);
}

export function drunkBetweenTwoTownsfolk(game: BOTCModel): BoolVar {
  const possibilities = game.players.map((player) => {
    const [left, right] = game.neighbors(player);
    return game.allOf(
      [game.actualIs(player, "Drunk"), game.isTownsfolk(left), game.isTownsfolk(right)],
      `${player}_drunk_between_two_townsfolk`,
    );
  });
  return game.anyOf(possibilities, "drunk_between_two_townsfolk");
}

export { CharacterType };
