import { Alignment, CharacterType, type RoleRef, roleAlignment } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  type AppliedInfoClaim,
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
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";
import { sameAlignment } from "../predicates";

export const PLAYERS = [
  new Artist({
    name: "Matthew",
    infoClaims: [
      { learned: (game) => game.actualIs("You", Clockmaker), falseWhenVortox: true },
      { role: Seamstress, learned: (game) => sameAlignment(game, "Aoife", "Tom"), falseWhenVortox: true },
    ],
  }),
  new Sage({
    name: "Anna",
    infoClaims: [
      {
        learned: (game) =>
          game.anyOf([game.actualIs("Matthew", Vortox), game.actualIs("Hannah", Vortox)], "anna_sage_pair_has_demon"),
        falseWhenVortox: true,
      },
    ],
  }),
  new SnakeCharmer({
    name: "Aoife",
    infoClaims: [
      (game) =>
        game.allOf(
          [
            game.actualIs("Tom", Vortox).not(),
            game.actualIs("Hannah", Vortox).not(),
            game.actualIs("Matthew", Vortox).not(),
          ],
          "Aoife_Snake Charmer_action_happened",
        ),
    ],
  }),
  new Artist({ name: "Hannah" }),
  new Clockmaker({
    name: "You",
    infoClaims: [{ learned: (game) => demonSitsStepsFromMinion(game, 2), falseWhenVortox: true }],
  }),
  new SnakeCharmer({
    name: "Sula",
    infoClaims: [
      {
        learned: (game) => game.allOf([game.actualIs("Sarah", Vortox).not()], "Sula_Snake Charmer_action_happened"),
      },
      {
        role: Philosopher,
        learned: (game) => game.allOf([game.actualIs("Sarah", Vortox).not()], "Sula_Philosopher_action_happened"),
      },
    ],
  }),
  new Dreamer({
    name: "Sarah",
    infoClaims: [
      {
        learned: (game) =>
          game.allOf(
            [
              Dreamer.learnsOneOf(game, "Matthew", [Cerenovus, Seamstress], "sarah_dreamer_matthew"),
              Dreamer.learnsOneOf(game, "Aoife", [Vortox, Mutant], "sarah_dreamer_aoife"),
              Dreamer.learnsOneOf(game, "You", [Vortox, Mutant], "sarah_dreamer_you"),
            ],
            "sarah_dreamer_all_checks",
          ),
        falseWhenVortox: true,
      },
    ],
  }),
  new Sweetheart({ name: "Tom" }),
];
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
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);

  game.fixActual("You", Clockmaker);
  applyClaims(
    game,
    PLAYERS.filter((claim) => ["Matthew", "Aoife", "Hannah", "Sarah"].includes(claim.name)),
    { extraPossibleActualRoles: [Mutant], info: addInfoClaim },
  );
  applyClaims(
    game,
    PLAYERS.filter((claim) => claim.name === "Sula"),
    { extraPossibleActualRoles: [Philosopher], info: addInfoClaim },
  );
  applyClaims(
    game,
    PLAYERS.filter((claim) => !["Matthew", "Aoife", "Hannah", "Sarah", "Sula"].includes(claim.name)),
    { info: addInfoClaim },
  );

  for (const deadPlayer of ["Anna", "You", "Sula", "Tom"]) {
    game.fixNotActual(deadPlayer, Mutant);
    game.fixNotActual(deadPlayer, Vortox);
  }

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addInfoClaim(game: BOTCModel, claim: AppliedInfoClaim): void {
  game.addImplication(
    game.actualIs(claim.player, claim.role),
    claim.falseWhenVortox ? game.not(claim.learned, `${claim.player}_${claim.role}_vortox_false`) : claim.learned,
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
