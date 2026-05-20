import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Clockmaker,
  Courtier,
  Dreamer,
  Empath,
  Lunatic,
  Mayor,
  ScarletWoman,
  Slayer,
  Spy,
  Vortox,
  playerNames,
  roleNames,
  script,
} from "../characters";
import { sameAlignment } from "../predicates";

export const PLAYERS = ["Hannah", "Sarah", "Jasmine", "You", "Tim", "Fraser"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Vortox,
  Spy,
  ScarletWoman,
  Lunatic,
  Clockmaker,
  Courtier,
  Dreamer,
  Empath,
  Mayor,
  Slayer,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Vortox, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.setCharacterCount(Lunatic, 1);

  addClaim(game, "Hannah", Slayer, [Slayer, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "Sarah", Courtier, [Courtier, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "Jasmine", Mayor, [Mayor, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "You", Dreamer, [Dreamer]);
  addClaim(game, "Tim", Clockmaker, [Clockmaker, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "Fraser", Empath, [Empath, Lunatic, Vortox, Spy, ScarletWoman]);

  const vortoxDrunk = game.actualIs("Sarah", Courtier);
  const sarahDreamerInfo = game.anyOf(
    [game.actualIs("Sarah", Lunatic), game.actualIs("Sarah", ScarletWoman)],
    "you_dreamer_sarah_lunatic_or_scarlet_woman",
  );
  game.addImplication(vortoxDrunk, sarahDreamerInfo);
  game.addImplication(vortoxDrunk.not(), game.not(sarahDreamerInfo, "you_dreamer_false_info"));

  const clockmakerInfo = demonSitsStepsFromMinion(game, 2);
  game.addImplication(
    game.allOf([game.actualIs("Tim", Clockmaker), vortoxDrunk], "tim_clockmaker_correct"),
    clockmakerInfo,
  );
  game.addImplication(
    game.allOf([game.actualIs("Tim", Clockmaker), vortoxDrunk.not()], "tim_clockmaker_vortox_false"),
    game.not(clockmakerInfo, "tim_clockmaker_info_false"),
  );

  const fraserEmpathInfo = game.allOf(
    [registersGoodToEmpath(game, "Tim"), registersGoodToEmpath(game, "Hannah")],
    "fraser_empath_both_good",
  );
  game.addImplication(
    game.allOf([game.actualIs("Fraser", Empath), vortoxDrunk], "fraser_empath_correct"),
    fraserEmpathInfo,
  );
  game.addImplication(
    game.allOf([game.actualIs("Fraser", Empath), vortoxDrunk.not()], "fraser_empath_vortox_false"),
    game.not(fraserEmpathInfo, "fraser_empath_info_false"),
  );

  game.addImplication(game.actualIs("Hannah", Slayer), game.actualIs("Fraser", Vortox).not());
  game.addTruth(doomsayerCanKill(game, "Hannah", "Tim", "hannah_doomsayer_kills_tim"));
  game.addTruth(doomsayerCanKill(game, "You", "Sarah", "you_doomsayer_kills_sarah"));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addClaim(
  game: BOTCModel,
  player: string,
  apparentRole: RoleRef,
  possibleActualRoles: readonly RoleRef[],
): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, possibleActualRoles);
}

function registersGoodToEmpath(game: BOTCModel, player: string): BoolLike {
  return game.anyOf([game.isGood(player), game.actualIs(player, Spy)], `${player}_registers_good_to_empath`);
}

function doomsayerCanKill(game: BOTCModel, caller: string, deadPlayer: string, name: string): BoolLike {
  return game.anyOf([sameAlignment(game, caller, deadPlayer), game.actualIs(deadPlayer, Spy)], name);
}

function demonSitsStepsFromMinion(game: BOTCModel, steps: number): BoolLike {
  return game.anyOf(
    PLAYER_NAMES.flatMap((demon, demonIndex) =>
      PLAYER_NAMES.flatMap((minion, minionIndex) => {
        const clockwise = (minionIndex - demonIndex + PLAYER_NAMES.length) % PLAYER_NAMES.length;
        const distance = Math.min(clockwise, PLAYER_NAMES.length - clockwise);
        return distance === steps
          ? [
              game.allOf(
                [
                  game.actualIs(demon, Vortox),
                  game.anyOf(
                    MINION_ROLES.map((role) => game.actualIs(minion, role)),
                    `${minion}_is_minion`,
                  ),
                ],
                `${demon}_${minion}_demon_${steps}_from_minion`,
              ),
            ]
          : [];
      }),
    ),
    `demon_${steps}_steps_from_minion`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-12a-thunderstruck.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Vortox, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
