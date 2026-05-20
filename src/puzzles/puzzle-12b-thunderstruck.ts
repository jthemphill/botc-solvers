import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  type AppliedInfoClaim,
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
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";
import { sameAlignment } from "../predicates";

export const PLAYERS = [
  new Slayer({
    name: "Fraser",
    infoClaims: [(game) => game.actualIs("Steph", Vortox).not()],
  }),
  new Dreamer({
    name: "Tom",
    infoClaims: [
      {
        learned: (game) =>
          game.anyOf([game.actualIs("Steph", Lunatic), game.actualIs("Steph", Spy)], "tom_dreamer_info"),
        falseWhenVortox: true,
      },
    ],
  }),
  new Clockmaker({
    name: "Aoife",
    infoClaims: [{ learned: (game) => demonSitsStepsFromMinion(game, 3), falseWhenVortox: true }],
  }),
  new Courtier({ name: "Steph" }),
  new Librarian({
    name: "You",
    infoClaims: [(game, context) => youLibrarianInfo(game, context as BoolVar)],
  }),
  new Investigator({
    name: "Oscar",
    infoClaims: [
      {
        learned: (game) =>
          game.anyOf([game.actualIs("Josh", Spy), game.actualIs("Fraser", Spy)], "oscar_investigator_info"),
        falseWhenVortox: true,
      },
    ],
  }),
  new Empath({
    name: "Anna",
    infoClaims: [
      {
        learned: (game) =>
          game.boolSumEquals([game.isEvil("Oscar"), game.isEvil("Josh")], 1, "anna_empath_exactly_one_evil"),
        falseWhenVortox: true,
      },
    ],
  }),
  new Mayor({ name: "Josh" }),
];
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

  game.fixActual("You", Librarian);
  const vortoxDrunk = game.actualIs("Steph", Courtier);
  applyClaims(game, PLAYERS, { extraPossibleActualRoles: [Lunatic], info: addInfoClaim, context: vortoxDrunk });
  game.addTruth(doomsayerCanKill(game, "Tom", "Josh", "tom_doomsayer_kills_josh"));
  game.addTruth(doomsayerCanKill(game, "Steph", "Oscar", "steph_doomsayer_kills_oscar"));
  game.addTruth(doomsayerCanKill(game, "Fraser", "Aoife", "fraser_doomsayer_kills_aoife"));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addInfoClaim(game: BOTCModel, claim: AppliedInfoClaim): void {
  const vortoxDrunk = claim.context as BoolVar;
  if (!claim.falseWhenVortox) {
    game.addImplication(game.actualIs(claim.player, claim.role), claim.learned);
    return;
  }
  game.addImplication(
    game.allOf([game.actualIs(claim.player, claim.role), vortoxDrunk], `${claim.player}_correct_info`),
    claim.learned,
  );
  game.addImplication(
    game.allOf([game.actualIs(claim.player, claim.role), vortoxDrunk.not()], `${claim.player}_false_info`),
    game.not(claim.learned, `${claim.player}_reported_info_false`),
  );
}

function youLibrarianInfo(game: BOTCModel, vortoxDrunk: BoolVar): BoolVar {
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
  return game.allOf(
    [
      game.anyOf([vortoxDrunk.not(), youLibrarianTrue], "you_librarian_drunk_true"),
      game.anyOf(
        [
          vortoxDrunk,
          game.anyOf(
            [youLibrarianActuallyFalse, game.actualIs("Fraser", Spy), game.actualIs("Steph", Spy)],
            "you_librarian_vortox_or_spy_false",
          ),
        ],
        "you_librarian_vortox_false",
      ),
    ],
    "you_librarian_info",
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
