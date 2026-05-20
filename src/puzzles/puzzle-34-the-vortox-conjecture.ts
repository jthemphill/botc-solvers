import { CharacterType, type RoleRef, roleName } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Artist,
  Clockmaker,
  Juggler,
  Mathematician,
  NoDashii,
  Sage,
  Seamstress,
  SnakeCharmer,
  Vortox,
  Witch,
  playerNames,
  script,
} from "../characters";
import { sameAlignment } from "../predicates";

export const PLAYERS = ["Sula", "Sarah", "Josh", "Aoife", "You", "Fraser", "Steph"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  NoDashii,
  Vortox,
  Witch,
  Artist,
  Clockmaker,
  Juggler,
  Mathematician,
  Sage,
  Seamstress,
  SnakeCharmer,
);

type MathPeriod = "night_1" | "night_2";

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isDemon(player)),
    1,
  );
  game.setCharacterCount(Witch, 1);
  game.fixActual("You", Mathematician);

  addClaim(game, "Sula", Clockmaker);
  addClaim(game, "Sarah", Seamstress);
  addClaim(game, "Josh", Juggler);
  addClaim(game, "Aoife", SnakeCharmer);
  addClaim(game, "Fraser", Sage);
  addClaim(game, "Steph", Artist);

  for (const deadBeforeNightTwo of ["Steph", "Aoife", "Fraser", "You"]) {
    game.fixNotActual(deadBeforeNightTwo, NoDashii);
    game.fixNotActual(deadBeforeNightTwo, Vortox);
  }

  addSnakeCharmerClaim(game, "Aoife", "Josh");

  const nightOneMalfunctions = [
    addInfoClaim(game, "Sula", Clockmaker, demonSitsStepsFromMinion(game, 3), "night_1"),
    addInfoClaim(game, "Sarah", Seamstress, sameAlignment(game, "Steph", "Aoife"), "night_1"),
    snakeCharmerMalfunction(game, "Aoife", "night_1"),
  ];
  const nightTwoMalfunctions = [
    addInfoClaim(game, "Steph", Artist, game.actualIs("Aoife", NoDashii), "night_2"),
    addInfoClaim(
      game,
      "Josh",
      Juggler,
      Juggler.learnsCorrectCount(game, { Steph: Artist, Sula: Clockmaker }, 0, "josh_juggle_zero"),
      "night_2",
    ),
    addInfoClaim(
      game,
      "Fraser",
      Sage,
      game.anyOf([game.isDemon("Sarah"), game.isDemon("Josh")], "fraser_sage_pair_has_demon"),
      "night_2",
    ),
  ];

  addMathematicianClaim(game, nightOneMalfunctions, 1, "night_1");
  addMathematicianClaim(game, nightTwoMalfunctions, 0, "night_2");

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addClaim(game: BOTCModel, player: string, apparentRole: RoleRef): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, [apparentRole, NoDashii, Vortox, Witch]);
}

function addInfoClaim(
  game: BOTCModel,
  player: string,
  role: RoleRef,
  reportedInfo: BoolLike,
  period: MathPeriod,
): BoolVar {
  const active = game.actualIs(player, role);
  const noDashiiPoison = noDashiiPoisoned(game, player);
  game.addImplication(
    game.allOf([active, game.roleInPlay(NoDashii), noDashiiPoison.not()], `${player}_${roleName(role)}_sober_info`),
    reportedInfo,
  );
  game.addImplication(
    game.allOf([active, game.roleInPlay(Vortox)], `${player}_${roleName(role)}_vortox_info`),
    game.not(reportedInfo, `${player}_${roleName(role)}_vortox_false`),
  );
  return game.anyOf(
    [
      game.allOf([active, game.roleInPlay(Vortox)], `${player}_${roleName(role)}_${period}_vortox_malfunction`),
      game.allOf(
        [active, game.roleInPlay(NoDashii), noDashiiPoison],
        `${player}_${roleName(role)}_${period}_nodashii_malfunction`,
      ),
    ],
    `${player}_${roleName(role)}_${period}_malfunction`,
  );
}

function addSnakeCharmerClaim(game: BOTCModel, player: string, picked: string): void {
  game.addImplication(
    game.allOf(
      [game.actualIs(player, SnakeCharmer), noDashiiPoisoned(game, player).not()],
      `${player}_active_snake_charmer`,
    ),
    game.isDemon(picked).not(),
  );
}

function snakeCharmerMalfunction(game: BOTCModel, player: string, period: MathPeriod): BoolVar {
  return game.allOf(
    [game.actualIs(player, SnakeCharmer), game.roleInPlay(NoDashii), noDashiiPoisoned(game, player)],
    `${player}_snake_charmer_${period}_malfunction`,
  );
}

function addMathematicianClaim(
  game: BOTCModel,
  malfunctions: readonly BoolLike[],
  reportedCount: number,
  period: MathPeriod,
): void {
  const trueCount = game.boolSumEquals(
    malfunctions,
    reportedCount,
    `you_mathematician_${period}_true_count_${reportedCount}`,
  );
  game.addImplication(
    game.allOf([game.roleInPlay(NoDashii), noDashiiPoisoned(game, "You").not()], `you_mathematician_${period}_sober`),
    trueCount,
  );
  game.addImplication(
    game.allOf([game.roleInPlay(Vortox), game.actualIs("You", Mathematician)], `you_mathematician_${period}_vortox`),
    trueCount.not(),
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

function demonSitsStepsFromMinion(game: BOTCModel, steps: number): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.flatMap((demon, demonIndex) =>
      PLAYER_NAMES.flatMap((minion, minionIndex) => {
        const clockwise = (minionIndex - demonIndex + PLAYER_NAMES.length) % PLAYER_NAMES.length;
        const distance = Math.min(clockwise, PLAYER_NAMES.length - clockwise);
        return distance === steps
          ? [
              game.allOf(
                [game.isDemon(demon), game.actualIs(minion, Witch)],
                `${demon}_${minion}_demon_${steps}_from_minion`,
              ),
            ]
          : [];
      }),
    ),
    `demon_${steps}_steps_from_minion`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-34-the-vortox-conjecture.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [forcedRole("Demon", [NoDashii, Vortox], { includeRole: true }), forcedRole("Minion", Witch)],
  });
