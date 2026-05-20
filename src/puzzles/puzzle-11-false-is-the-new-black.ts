import { Alignment, CharacterType, type RoleRef, roleAlignment, roleName } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Artist,
  Cerenovus,
  Clockmaker,
  Dreamer,
  Mutant,
  Philosopher,
  PitHag,
  Sage,
  Seamstress,
  SnakeCharmer,
  Sweetheart,
  Vortox,
  playerNames,
  roleNames,
  script,
} from "../characters";
import { sameAlignment } from "../predicates";

export const PLAYERS = ["Matthew", "Anna", "Aoife", "Hannah", "You", "Sula", "Sarah", "Tom"];
export const CHARACTERS = script(
  Vortox,
  Cerenovus,
  PitHag,
  Mutant,
  Sweetheart,
  Artist,
  Clockmaker,
  Dreamer,
  Philosopher,
  Sage,
  Seamstress,
  SnakeCharmer,
);
export const PLAYER_NAMES = playerNames(PLAYERS);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Vortox, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    1,
  );

  addClaim(game, "Matthew", Artist, [Artist, Mutant, Vortox, Cerenovus, PitHag]);
  addClaim(game, "Anna", Sage, [Sage, Vortox, Cerenovus, PitHag]);
  addClaim(game, "Aoife", SnakeCharmer, [SnakeCharmer, Mutant, Vortox, Cerenovus, PitHag]);
  addClaim(game, "Hannah", Artist, [Artist, Mutant, Vortox, Cerenovus, PitHag]);
  addClaim(game, "You", Clockmaker, [Clockmaker]);
  addClaim(game, "Sula", SnakeCharmer, [SnakeCharmer, Philosopher, Vortox, Cerenovus, PitHag]);
  addClaim(game, "Sarah", Dreamer, [Dreamer, Mutant, Vortox, Cerenovus, PitHag]);
  addClaim(game, "Tom", Sweetheart, [Sweetheart, Vortox, Cerenovus, PitHag]);

  for (const deadPlayer of ["Anna", "You", "Sula", "Tom"]) {
    game.fixNotActual(deadPlayer, Mutant);
    game.fixNotActual(deadPlayer, Vortox);
  }

  addFalseInfoClaim(game, "Matthew", Artist, game.actualIs("You", Clockmaker));
  addFalseInfoClaim(
    game,
    "Anna",
    Sage,
    game.anyOf([game.actualIs("Matthew", Vortox), game.actualIs("Hannah", Vortox)], "anna_sage_pair_has_demon"),
  );
  addFalseInfoClaim(game, "You", Clockmaker, demonSitsStepsFromMinion(game, 2));
  addFalseInfoClaim(
    game,
    "Sarah",
    Dreamer,
    game.allOf(
      [
        Dreamer.learnsOneOf(game, "Matthew", [Cerenovus, Seamstress], "sarah_dreamer_matthew"),
        Dreamer.learnsOneOf(game, "Aoife", [Vortox, Mutant], "sarah_dreamer_aoife"),
        Dreamer.learnsOneOf(game, "You", [Vortox, Mutant], "sarah_dreamer_you"),
      ],
      "sarah_dreamer_all_checks",
    ),
  );
  addFalseInfoClaim(game, "Matthew", Seamstress, sameAlignment(game, "Aoife", "Tom"));

  addActionClaim(game, "Aoife", SnakeCharmer, [
    game.actualIs("Tom", Vortox).not(),
    game.actualIs("Hannah", Vortox).not(),
    game.actualIs("Matthew", Vortox).not(),
  ]);
  addActionClaim(game, "Sula", SnakeCharmer, [game.actualIs("Sarah", Vortox).not()]);
  addActionClaim(game, "Sula", Philosopher, [game.actualIs("Sarah", Vortox).not()]);

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

function addFalseInfoClaim(game: BOTCModel, player: string, role: RoleRef, reportedInfo: BoolLike): void {
  game.addImplication(game.actualIs(player, role), game.not(reportedInfo, `${player}_${roleName(role)}_vortox_false`));
}

function addActionClaim(game: BOTCModel, player: string, role: RoleRef, consequences: readonly BoolLike[]): void {
  game.addImplication(
    game.actualIs(player, role),
    game.allOf(consequences, `${player}_${roleName(role)}_action_happened`),
  );
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

export function goodRoles(): RoleRef[] {
  return CHARACTERS.filter((role) => roleAlignment(role) === Alignment.Good);
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-11-false-is-the-new-black.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [forcedRole("Demon", Vortox, { includeRole: true }), forcedRole("Minion", MINION_ROLES)],
  });
