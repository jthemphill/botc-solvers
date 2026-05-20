import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Clockmaker,
  Courtier,
  Dreamer,
  Empath,
  Investigator,
  Librarian,
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

export const PLAYERS = ["Fraser", "Tom", "Aoife", "Steph", "You", "Oscar", "Anna", "Josh"];
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
  Investigator,
  Librarian,
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

  addClaim(game, "Fraser", Slayer, [Slayer, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "Tom", Dreamer, [Dreamer, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "Aoife", Clockmaker, [Clockmaker, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "Steph", Courtier, [Courtier, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "You", Librarian, [Librarian]);
  addClaim(game, "Oscar", Investigator, [Investigator, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "Anna", Empath, [Empath, Lunatic, Vortox, Spy, ScarletWoman]);
  addClaim(game, "Josh", Mayor, [Mayor, Lunatic, Vortox, Spy, ScarletWoman]);

  const vortoxDrunk = game.actualIs("Steph", Courtier);

  addVortoxAwareInfo(
    game,
    vortoxDrunk,
    "Tom",
    Dreamer,
    game.anyOf([game.actualIs("Steph", Lunatic), game.actualIs("Steph", Spy)], "tom_dreamer_info"),
  );
  addVortoxAwareInfo(game, vortoxDrunk, "Aoife", Clockmaker, demonSitsStepsFromMinion(game, 3));
  addVortoxAwareInfo(
    game,
    vortoxDrunk,
    "Oscar",
    Investigator,
    game.anyOf([game.actualIs("Josh", Spy), game.actualIs("Fraser", Spy)], "oscar_investigator_info"),
  );
  addVortoxAwareInfo(
    game,
    vortoxDrunk,
    "Anna",
    Empath,
    game.boolSumEquals([game.isEvil("Oscar"), game.isEvil("Josh")], 1, "anna_empath_exactly_one_evil"),
  );

  const youLibrarianTrue = game.anyOf(
    [
      game.actualIs("Fraser", Lunatic),
      game.actualIs("Steph", Lunatic),
      game.actualIs("Fraser", Spy),
      game.actualIs("Steph", Spy),
    ],
    "you_librarian_lunatic_or_spy_misregisters",
  );
  const youLibrarianActuallyFalse = game.not(
    game.anyOf([game.actualIs("Fraser", Lunatic), game.actualIs("Steph", Lunatic)], "you_librarian_actual_lunatic"),
    "you_librarian_false_without_spy",
  );
  game.addImplication(vortoxDrunk, youLibrarianTrue);
  game.addImplication(
    vortoxDrunk.not(),
    game.anyOf(
      [youLibrarianActuallyFalse, game.actualIs("Fraser", Spy), game.actualIs("Steph", Spy)],
      "you_librarian_vortox_or_spy_false",
    ),
  );

  game.addImplication(game.actualIs("Fraser", Slayer), game.actualIs("Steph", Vortox).not());
  game.addTruth(doomsayerCanKill(game, "Tom", "Josh", "tom_doomsayer_kills_josh"));
  game.addTruth(doomsayerCanKill(game, "Steph", "Oscar", "steph_doomsayer_kills_oscar"));
  game.addTruth(doomsayerCanKill(game, "Fraser", "Aoife", "fraser_doomsayer_kills_aoife"));

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

function addVortoxAwareInfo(
  game: BOTCModel,
  vortoxDrunk: BoolLike,
  player: string,
  role: RoleRef,
  reportedInfo: BoolLike,
): void {
  game.addImplication(game.allOf([game.actualIs(player, role), vortoxDrunk], `${player}_correct_info`), reportedInfo);
  game.addImplication(
    game.allOf([game.actualIs(player, role), game.not(vortoxDrunk, `${player}_vortox_active`)], `${player}_false_info`),
    game.not(reportedInfo, `${player}_reported_info_false`),
  );
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

if (import.meta.main && process.argv[1]?.endsWith("puzzle-12b-thunderstruck.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Vortox, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
