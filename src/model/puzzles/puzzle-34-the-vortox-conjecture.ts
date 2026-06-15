import { CharacterType, roleName } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  type AppliedInfoClaim,
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
  applyClaims,
  playerNames,
  script,
} from "../characters";
import { sameAlignment } from "../predicates";

export const PLAYERS = [
  new Clockmaker({
    name: "Sula",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) => demonSitsStepsFromMinion(game, 3),
        vortoxAffected: true,
      },
    ],
  }),
  new Seamstress({
    timing: "night_1",
    name: "Sarah",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) => sameAlignment(game, "Steph", "Aoife"),
        vortoxAffected: true,
      },
    ],
  }),
  new Juggler({
    timing: "night_2",
    name: "Josh",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => Juggler.learnsCorrectCount(game, { Steph: Artist, Sula: Clockmaker }, 0, "josh_juggle_zero"),
        vortoxAffected: true,
      },
    ],
  }),
  new SnakeCharmer({
    name: "Aoife",
    infoClaims: [{ timing: "night_1", learned: (game) => game.isDemon("Josh").not() }],
  }),
  new Mathematician({
    name: "You",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game, context) =>
          game.boolSumEquals(
            (context as ClaimContext).malfunctions.night_1 ?? [],
            1,
            "you_mathematician_night_1_true_count_1",
          ),
        vortoxAffected: true,
      },
      {
        timing: "night_2",
        learned: (game, context) =>
          game.boolSumEquals(
            (context as ClaimContext).malfunctions.night_2 ?? [],
            0,
            "you_mathematician_night_2_true_count_0",
          ),
        vortoxAffected: true,
      },
    ],
  }),
  new Sage({
    timing: "night_2",
    name: "Fraser",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => game.anyOf([game.isDemon("Sarah"), game.isDemon("Josh")], "fraser_sage_pair_has_demon"),
        vortoxAffected: true,
      },
    ],
  }),
  new Artist({
    timing: "day_1",
    name: "Steph",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => game.actualIs("Aoife", NoDashii),
        vortoxAffected: true,
      },
    ],
  }),
];
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
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS } satisfies PuzzleSpec;

interface ClaimContext {
  readonly malfunctions: Record<string, BoolVar[]>;
}

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixActual("You", Mathematician);

  for (const deadBeforeNightTwo of ["Steph", "Aoife", "Fraser"]) {
    game.fixNotActual(deadBeforeNightTwo, NoDashii);
    game.fixNotActual(deadBeforeNightTwo, Vortox);
  }

  const context: ClaimContext = { malfunctions: { night_1: [], night_2: [] } };
  applyClaims(
    game,
    PLAYERS.filter((claim) => !(claim instanceof Mathematician)),
    { info: addInfoClaim, context },
  );
  applyClaims(
    game,
    PLAYERS.filter((claim) => claim instanceof Mathematician),
    { info: addInfoClaim, context },
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addInfoClaim(game: BOTCModel, claim: AppliedInfoClaim): void {
  const timing = claim.timing;
  if (claim.role === Mathematician) {
    game.addImplication(
      game.allOf(
        [game.roleInPlay(NoDashii), noDashiiPoisoned(game, claim.player).not()],
        `you_mathematician_${timing}_sober`,
      ),
      claim.learned,
    );
    game.addImplication(
      game.allOf(
        [game.roleInPlay(Vortox), game.actualIs(claim.player, Mathematician)],
        `you_mathematician_${timing}_vortox`,
      ),
      game.not(claim.learned, `you_mathematician_${timing}_false_count`),
    );
    return;
  }

  const active = game.actualIs(claim.player, claim.role);
  const noDashiiPoison = noDashiiPoisoned(game, claim.player);
  if (claim.vortoxAffected) {
    game.addImplication(
      game.allOf(
        [active, game.roleInPlay(NoDashii), noDashiiPoison.not()],
        `${claim.player}_${roleName(claim.role)}_sober_info`,
      ),
      claim.learned,
    );
    game.addImplication(
      game.allOf([active, game.roleInPlay(Vortox)], `${claim.player}_${roleName(claim.role)}_vortox_info`),
      game.not(claim.learned, `${claim.player}_${roleName(claim.role)}_vortox_false`),
    );
  } else {
    game.addImplication(
      game.allOf([active, noDashiiPoison.not()], `${claim.player}_${roleName(claim.role)}_active_info`),
      claim.learned,
    );
  }

  const malfunction = game.anyOf(
    [
      ...(claim.vortoxAffected
        ? [
            game.allOf(
              [active, game.roleInPlay(Vortox)],
              `${claim.player}_${roleName(claim.role)}_${timing}_vortox_malfunction`,
            ),
          ]
        : []),
      game.allOf(
        [active, game.roleInPlay(NoDashii), noDashiiPoison],
        `${claim.player}_${roleName(claim.role)}_${timing}_nodashii_malfunction`,
      ),
    ],
    `${claim.player}_${roleName(claim.role)}_${timing}_malfunction`,
  );
  (claim.context as ClaimContext).malfunctions[timing]?.push(malfunction);
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
