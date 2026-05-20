import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Artist,
  Clockmaker,
  EvilTwin,
  Juggler,
  Klutz,
  Mutant,
  NoDashii,
  Savant,
  Seamstress,
  SnakeCharmer,
  Vortox,
  playerNames,
  roleNames,
  script,
} from "../characters";
import { differentAlignments } from "../predicates";

export const PLAYERS = ["Fraser", "Aoife", "Adam", "Jasmine", "You", "Oscar", "Sarah", "Hannah"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  NoDashii,
  Vortox,
  EvilTwin,
  Mutant,
  Klutz,
  Artist,
  Clockmaker,
  Juggler,
  Savant,
  Seamstress,
  SnakeCharmer,
);
export const DEMON_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Demon });

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, {
    characters: CHARACTERS,
    seating: PLAYER_NAMES,
    uniqueCharacters: false,
    backend,
  });
  enforceRoleCounts(game);

  addClaim(game, "Fraser", Clockmaker, [Clockmaker, Mutant, NoDashii, Vortox, EvilTwin]);
  addClaim(game, "Aoife", Seamstress, [Seamstress, Mutant, NoDashii, Vortox, EvilTwin]);
  addClaim(game, "Adam", Artist, [Artist, Mutant, NoDashii, Vortox, EvilTwin]);
  addClaim(game, "Jasmine", SnakeCharmer, [SnakeCharmer, Mutant, NoDashii, Vortox, EvilTwin]);
  addClaim(game, "You", Savant, [Savant]);
  addClaim(game, "Oscar", Klutz, [Klutz, NoDashii, Vortox, EvilTwin]);
  addClaim(game, "Sarah", Juggler, [Juggler, Mutant, NoDashii, Vortox, EvilTwin]);
  addClaim(game, "Hannah", SnakeCharmer, [SnakeCharmer, Mutant, NoDashii, Vortox, EvilTwin]);

  addInfo(game, "Fraser", Clockmaker, demonSitsStepsFromMinion(game, 3));
  addInfo(game, "Aoife", Seamstress, differentAlignments(game, "Oscar", "Hannah"));
  addInfo(
    game,
    "Adam",
    Artist,
    game.not(
      game.anyOf(
        ["You", "Oscar", "Sarah"].map((player) => game.actualIs(player, Vortox)),
        "artist_any_vortox",
      ),
      "artist_none_vortox",
    ),
  );
  addInfo(
    game,
    "Sarah",
    Juggler,
    Juggler.learnsCorrectCount(
      game,
      {
        You: Savant,
        Hannah: SnakeCharmer,
        Fraser: Clockmaker,
        Aoife: Seamstress,
        Jasmine: SnakeCharmer,
      },
      3,
      "sarah_juggler_count",
    ),
  );
  addSavantInfo(game);
  game.addTruth(EvilTwin.pairIsOneOf(game, [["Jasmine", "Hannah"]], "snake_charmer_twin_pair"));
  addSnakeCharmerClaim(game, "Hannah", ["Sarah", "Oscar", "Aoife"], "Jasmine");
  addSnakeCharmerClaim(game, "Jasmine", ["Fraser", "Aoife", "Adam"], "Hannah");
  game.addImplication(game.actualIs("Oscar", Klutz), game.isGood("Sarah"));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function enforceRoleCounts(game: BOTCModel): void {
  const always = game.constantBool(true, "role_count_constraints");
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isDemon(player)),
    1,
  );
  game.setCharacterCount(EvilTwin, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    1,
  );
  for (const role of [NoDashii, Vortox, EvilTwin, Mutant, Klutz, Artist, Clockmaker, Juggler, Savant, Seamstress]) {
    game.addEnforcedAtMostN(
      PLAYER_NAMES.map((player) => game.actualIs(player, role)),
      1,
      always,
    );
  }
  game.addEnforcedAtMostN(
    PLAYER_NAMES.map((player) => game.actualIs(player, SnakeCharmer)),
    2,
    always,
  );
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

function addInfo(game: BOTCModel, player: string, role: RoleRef, reportedInfo: BoolLike): void {
  const active = game.allOf(
    [game.actualIs(player, role), noDashiiPoisoned(game, player).not()],
    `${player}_active_info`,
  );
  game.addImplication(game.allOf([active, game.roleInPlay(NoDashii)], `${player}_true_info`), reportedInfo);
  game.addImplication(
    game.allOf([active, game.roleInPlay(Vortox)], `${player}_vortox_false_info`),
    game.not(reportedInfo, `${player}_reported_info_false`),
  );
}

function addSavantInfo(game: BOTCModel): void {
  const roleMissingCount = game.boolSumEquals(
    [Clockmaker, Klutz, Juggler, Vortox].map((role) => game.roleInPlay(role).not()),
    1,
    "savant_role_missing_count",
  );
  const chainLengthFive = longestTownfolkChainIs(game, 5);
  const active = game.allOf([game.actualIs("You", Savant), noDashiiPoisoned(game, "You").not()], "you_active_savant");
  game.addImplication(
    game.allOf([active, game.roleInPlay(NoDashii)], "you_savant_normal"),
    Savant.learnsExactlyOne(game, [roleMissingCount, chainLengthFive], "you_savant_one_true"),
  );
  game.addImplication(
    game.allOf([active, game.roleInPlay(Vortox)], "you_savant_vortox"),
    game.allOf([roleMissingCount.not(), chainLengthFive.not()], "you_savant_both_false"),
  );
}

function addSnakeCharmerClaim(game: BOTCModel, player: string, picks: readonly string[], accusedTwin: string): void {
  const active = game.allOf(
    [game.actualIs(player, SnakeCharmer), noDashiiPoisoned(game, player).not()],
    `${player}_active_snake_charmer`,
  );
  game.addImplication(
    active,
    game.allOf(
      [...picks.map((pick) => game.isDemon(pick).not()), game.actualIs(accusedTwin, EvilTwin)],
      `${player}_snake_charmer_claims`,
    ),
  );
}

function noDashiiPoisoned(game: BOTCModel, player: string): BoolVar {
  const sources = PLAYER_NAMES.flatMap((demon) => {
    const [left, right] = game.neighbors(demon);
    return player === left || player === right
      ? [
          game.allOf(
            [game.actualIs(demon, NoDashii), game.hasCharacterType(player, CharacterType.Townsfolk)],
            `${player}_poisoned_by_no_dashii_${demon}`,
          ),
        ]
      : [];
  });
  return game.anyOf(sources, `${player}_poisoned_by_no_dashii`);
}

function longestTownfolkChainIs(game: BOTCModel, length: number): BoolVar {
  return game.allOf(
    [
      townfolkChainAtLeast(game, length),
      game.not(townfolkChainAtLeast(game, length + 1), `townfolk_chain_not_${length + 1}`),
    ],
    `townfolk_chain_exactly_${length}`,
  );
}

function townfolkChainAtLeast(game: BOTCModel, length: number): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((_, start) =>
      game.allOf(
        Array.from({ length }, (_ignored, offset) =>
          game.hasCharacterType(
            PLAYER_NAMES[(start + offset) % PLAYER_NAMES.length] as string,
            CharacterType.Townsfolk,
          ),
        ),
        `townfolk_chain_${start}_${length}`,
      ),
    ),
    `townfolk_chain_at_least_${length}`,
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
                [game.isDemon(demon), game.actualIs(minion, EvilTwin)],
                `${demon}_${minion}_demon_${steps}_from_twin`,
              ),
            ]
          : [];
      }),
    ),
    `demon_${steps}_steps_from_twin`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-15-wake-up-and-choose-violets.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", DEMON_ROLES, { includeRole: true }),
      forcedRole("Minion", EvilTwin, { includeRole: true }),
    ],
  });
