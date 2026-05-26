import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  type AppliedInfoClaim,
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
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";
import { sameAlignment } from "../predicates";

export const PLAYERS = [
  new Slayer({
    timing: "day_1",
    name: "Hannah",
    infoClaims: [(game) => game.actualIs("Fraser", Vortox).not()],
  }),
  new Courtier({ name: "Sarah" }),
  new Mayor({ name: "Jasmine" }),
  new Dreamer({
    name: "You",
    infoClaims: [
      {
        learned: (game) =>
          game.anyOf(
            [game.actualIs("Sarah", Lunatic), game.actualIs("Sarah", ScarletWoman)],
            "you_dreamer_sarah_lunatic_or_scarlet_woman",
          ),
        vortoxAffected: true,
      },
    ],
  }),
  new Clockmaker({
    name: "Tim",
    infoClaims: [{ learned: (game) => demonSitsStepsFromMinion(game, 2), vortoxAffected: true }],
  }),
  new Empath({
    name: "Fraser",
    infoClaims: [
      {
        learned: (game) =>
          game.allOf(
            [registersGoodToEmpath(game, "Tim"), registersGoodToEmpath(game, "Hannah")],
            "fraser_empath_both_good",
          ),
        vortoxAffected: true,
      },
    ],
  }),
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
  Mayor,
  Slayer,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);

  game.fixActual("You", Dreamer);
  const vortoxDrunk = game.actualIs("Sarah", Courtier);
  applyClaims(game, PLAYERS, { extraPossibleActualRoles: [Lunatic], info: addInfoClaim, context: vortoxDrunk });
  game.addTruth(doomsayerCanKill(game, "Hannah", "Tim", "hannah_doomsayer_kills_tim"));
  game.addTruth(doomsayerCanKill(game, "You", "Sarah", "you_doomsayer_kills_sarah"));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function registersGoodToEmpath(game: BOTCModel, player: string): BoolLike {
  return game.anyOf([game.isGood(player), game.actualIs(player, Spy)], `${player}_registers_good_to_empath`);
}

function addInfoClaim(game: BOTCModel, claim: AppliedInfoClaim): void {
  const vortoxDrunk = claim.context as BoolVar;
  if (!claim.vortoxAffected) {
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
