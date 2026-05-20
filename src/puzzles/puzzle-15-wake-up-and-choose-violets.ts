import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  type AppliedInfoClaim,
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
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const PLAYERS = [
  new Clockmaker({
    name: "Fraser",
    infoClaims: [{ learned: (game) => demonSitsStepsFromMinion(game, 3), falseWhenVortox: true }],
  }),
  new Seamstress({
    name: "Aoife",
    among: ["Oscar", "Hannah"],
    infoClaims: [
      { learned: (game) => Seamstress.learnsDifferentAlignment(game, "Oscar", "Hannah"), falseWhenVortox: true },
    ],
  }),
  new Artist({
    name: "Adam",
    infoClaims: [{ learned: artistInfo, falseWhenVortox: true }],
  }),
  new SnakeCharmer({
    name: "Jasmine",
    infoClaims: [(game) => snakeCharmerClaim(game, "Jasmine", ["Fraser", "Aoife", "Adam"], "Hannah")],
  }),
  new Savant({ name: "You", infoClaims: [savantInfo] }),
  new Klutz({ name: "Oscar" }),
  new Juggler({
    name: "Sarah",
    guesses: {
      You: Savant,
      Hannah: SnakeCharmer,
      Fraser: Clockmaker,
      Aoife: Seamstress,
      Jasmine: SnakeCharmer,
    },
    infoClaims: [
      {
        learned: (game) =>
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
        falseWhenVortox: true,
      },
    ],
  }),
  new SnakeCharmer({
    name: "Hannah",
    infoClaims: [(game) => snakeCharmerClaim(game, "Hannah", ["Sarah", "Oscar", "Aoife"], "Jasmine")],
  }),
];
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
export const PUZZLE = {
  players: PLAYER_NAMES,
  characters: CHARACTERS,
  seating: PLAYER_NAMES,
  uniqueCharacters: false,
} satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  enforceRoleCounts(game);
  game.fixActual("You", Savant);

  applyClaims(game, PLAYERS, { info: addInfo });
  game.addTruth(EvilTwin.pairIsOneOf(game, [["Jasmine", "Hannah"]], "snake_charmer_twin_pair"));
  game.addImplication(game.actualIs("Oscar", Klutz), game.isGood("Sarah"));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function enforceRoleCounts(game: BOTCModel): void {
  const always = game.constantBool(true, "role_count_constraints");
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

function addInfo(game: BOTCModel, claim: AppliedInfoClaim): void {
  const active = game.allOf(
    [game.actualIs(claim.player, claim.role), noDashiiPoisoned(game, claim.player).not()],
    `${claim.player}_active_info`,
  );
  if (!claim.falseWhenVortox) {
    game.addImplication(active, claim.learned);
    return;
  }
  game.addImplication(game.allOf([active, game.roleInPlay(NoDashii)], `${claim.player}_true_info`), claim.learned);
  game.addImplication(
    game.allOf([active, game.roleInPlay(Vortox)], `${claim.player}_vortox_false_info`),
    game.not(claim.learned, `${claim.player}_reported_info_false`),
  );
}

function artistInfo(game: BOTCModel): BoolVar {
  return game.not(
    game.anyOf(
      ["You", "Oscar", "Sarah"].map((player) => game.actualIs(player, Vortox)),
      "artist_any_vortox",
    ),
    "artist_none_vortox",
  );
}

function savantInfo(game: BOTCModel): BoolVar {
  const roleMissingCount = game.boolSumEquals(
    [Clockmaker, Klutz, Juggler, Vortox].map((role) => game.roleInPlay(role).not()),
    1,
    "savant_role_missing_count",
  );
  const chainLengthFive = longestTownfolkChainIs(game, 5);
  return game.allOf(
    [
      game.anyOf(
        [
          game.roleInPlay(NoDashii).not(),
          Savant.learnsExactlyOne(game, [roleMissingCount, chainLengthFive], "you_savant_one_true"),
        ],
        "you_savant_normal_claim",
      ),
      game.anyOf(
        [
          game.roleInPlay(Vortox).not(),
          game.allOf([roleMissingCount.not(), chainLengthFive.not()], "you_savant_both_false"),
        ],
        "you_savant_vortox_claim",
      ),
    ],
    "you_savant_info",
  );
}

function snakeCharmerClaim(game: BOTCModel, player: string, picks: readonly string[], accusedTwin: string): BoolVar {
  return game.allOf(
    [...picks.map((pick) => game.isDemon(pick).not()), game.actualIs(accusedTwin, EvilTwin)],
    `${player}_snake_charmer_claims`,
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
