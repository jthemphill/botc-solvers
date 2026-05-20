import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { differentAlignments } from "../predicates";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Artist,
  Juggler,
  Klutz,
  Mathematician,
  Mutant,
  NoDashii,
  Oracle,
  Philosopher,
  Sage,
  Seamstress,
  Witch,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const PLAYERS = ["Fraser", "Tom", "Sula", "Hannah", "You", "Jasmine", "Matt", "Aoife"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const EVIL_ROLES = [NoDashii, Witch];
export const CHARACTERS = script(
  NoDashii,
  Witch,
  Mutant,
  Klutz,
  Artist,
  Juggler,
  Mathematician,
  Oracle,
  Philosopher,
  Sage,
  Seamstress,
);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(NoDashii, 1);
  game.setCharacterCount(Witch, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    1,
  );
  game.fixNotActual("You", NoDashii);
  game.fixNotActual("You", Witch);
  game.fixNotActual("You", Mutant);
  for (const deadBeforeFinalNight of ["Tom", "Aoife", "Fraser", "Sula"])
    game.fixNotActual(deadBeforeFinalNight, NoDashii);
  for (const deadPlayer of ["Tom", "Aoife", "Fraser"]) game.fixNotActual(deadPlayer, Mutant);

  addClaim(game, "Fraser", Sage, [Sage, NoDashii, Witch]);
  addClaim(game, "Tom", Artist, [Artist, NoDashii, Witch]);
  addClaim(game, "Sula", Mathematician, [Mathematician, NoDashii, Witch]);
  addClaim(game, "Hannah", Klutz, [Klutz, NoDashii, Witch]);
  addClaim(game, "You", Oracle, [Oracle, Klutz]);
  addClaim(game, "Jasmine", Juggler, [Juggler, Mutant, NoDashii, Witch]);
  addClaim(game, "Matt", Philosopher, [Philosopher, Mutant, NoDashii, Witch]);
  addClaim(game, "Aoife", Seamstress, [Seamstress, NoDashii, Witch]);

  const aoifeInfo = differentAlignments(game, "Matt", "Hannah");
  const fraserInfo = game.anyOf(
    [game.actualIs("Jasmine", NoDashii), game.actualIs("Matt", NoDashii)],
    "fraser_sage_demon_pair",
  );
  const tomInfo = game.anyOf(
    [game.actualIs("Jasmine", Mutant), game.actualIs("Matt", Mutant), game.actualIs("Aoife", Mutant)],
    "tom_artist_mutant_yes",
  );
  const youInfo = game.boolSumEquals(
    ["Tom", "Aoife", "Fraser"].map((player) => game.isEvil(player)),
    1,
    "you_oracle_one_dead_evil",
  );

  const nightOneMalfunctions = [
    addInfo(game, "Aoife", Seamstress, aoifeInfo, NIGHT_1),
    addInfo(game, "Fraser", Sage, fraserInfo, NIGHT_1),
  ];
  const nightTwoMalfunctions = [
    addInfo(game, "You", Oracle, youInfo, NIGHT_2),
    addInfo(
      game,
      "Jasmine",
      Juggler,
      Juggler.learnsCorrectCount(
        game,
        { You: Witch, Aoife: Witch, Tom: Witch, Fraser: Sage, Hannah: Klutz },
        3,
        "jasmine_juggler_count",
      ),
      NIGHT_2,
    ),
  ];

  addInfo(game, "Tom", Artist, tomInfo, NIGHT_1);
  addInfo(game, "Matt", Philosopher, differentAlignments(game, "Aoife", "Tom"), NIGHT_1);
  addMathematicianInfo(game, nightOneMalfunctions, 0, NIGHT_1);
  addMathematicianInfo(game, nightTwoMalfunctions, 1, NIGHT_2);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addClaim(game: BOTCModel, player: string, apparentRole: RoleRef, possibleRoles: readonly RoleRef[]): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, possibleRoles);
}

function addInfo(game: BOTCModel, player: string, role: RoleRef, reportedInfo: BoolLike, name: string): BoolVar {
  const active = game.actualIs(player, role);
  const poisoned = noDashiiPoisoned(game, player);
  game.addImplication(game.allOf([active, poisoned.not()], `${player}_${name}_sober_info`), reportedInfo);
  return game.allOf(
    [active, poisoned, game.not(reportedInfo, `${player}_${name}_false_info`)],
    `${player}_${name}_malfunction`,
  );
}

function addMathematicianInfo(game: BOTCModel, malfunctions: readonly BoolLike[], count: number, name: string): void {
  game.addImplication(
    game.allOf(
      [game.actualIs("Sula", Mathematician), noDashiiPoisoned(game, "Sula").not()],
      `sula_mathematician_${name}_active`,
    ),
    game.boolSumEquals(malfunctions, count, `sula_mathematician_${name}_${count}`),
  );
}

function noDashiiPoisoned(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.flatMap((demon) => [
      closestTownfolkInDirectionIs(game, demon, player, 1),
      closestTownfolkInDirectionIs(game, demon, player, -1),
    ]),
    `${player}_poisoned_by_no_dashii`,
  );
}

function closestTownfolkInDirectionIs(game: BOTCModel, demon: string, target: string, direction: 1 | -1): BoolVar {
  const demonIndex = PLAYER_NAMES.indexOf(demon);
  const targetIndex = PLAYER_NAMES.indexOf(target);
  const distance =
    (direction === 1 ? targetIndex - demonIndex : demonIndex - targetIndex + PLAYER_NAMES.length) % PLAYER_NAMES.length;
  if (distance <= 0) return game.constantBool(false, `${demon}_${target}_not_in_direction_${direction}`);
  const between = Array.from({ length: distance - 1 }, (_ignored, offset) => {
    const index = (demonIndex + direction * (offset + 1) + PLAYER_NAMES.length) % PLAYER_NAMES.length;
    return PLAYER_NAMES[index] as string;
  });
  return game.allOf(
    [
      game.actualIs(demon, NoDashii),
      game.hasCharacterType(target, CharacterType.Townsfolk),
      ...between.map((betweenPlayer) => game.hasCharacterType(betweenPlayer, CharacterType.Townsfolk).not()),
    ],
    `${target}_closest_townsfolk_${direction}_of_${demon}`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-39-squid-game.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", NoDashii, { includeRole: true }),
      forcedRole("Minion", Witch),
      forcedRole("Outsider", [Klutz, Mutant], { includeRole: true }),
    ],
  });
