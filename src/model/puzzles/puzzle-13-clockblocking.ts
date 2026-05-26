import { night } from "../model";
import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import type { BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Baron,
  Clockmaker,
  Drunk,
  FortuneTeller,
  Imp,
  Investigator,
  Librarian,
  Poisoner,
  Ravenkeeper,
  Recluse,
  ScarletWoman,
  Slayer,
  Spy,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = night(1);
export const NIGHT_2 = night(2);

export const PLAYERS = [
  new Ravenkeeper({
    timing: "night_2",
    name: "Tim",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => game.registersAsRole("Oscar", Librarian, "tim_ravenkeeper"),
      },
    ],
  }),
  new FortuneTeller({
    name: "Sarah",
    checks: [
      {
        left: "You",
        right: "Oscar",
        yes: false,
        demonRole: Imp,
        registers: true,
        timing: "night_1",
      },
      {
        left: "You",
        right: "Jasmine",
        yes: false,
        demonRole: Imp,
        registers: true,
        timing: "night_2",
      },
    ],
  }),
  new Slayer({
    timing: "day_1",
    name: "Fraser",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => game.registersAsRole("Oscar", Imp, "fraser_slayer").not(),
      },
    ],
  }),
  new Recluse({ name: "Aoife" }),
  new Investigator({
    name: "You",
    role: ScarletWoman,
    among: ["Sarah", "Aoife"],
    timing: "night_1",
  }),
  new Clockmaker({
    name: "Jasmine",
    infoClaims: [{ timing: "night_1", learned: (game) => demonSitsStepsFromMinion(game, 3) }],
  }),
  new Librarian({ name: "Oscar", outsiderCount: 0, timing: "night_1" }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Poisoner,
  Spy,
  Baron,
  ScarletWoman,
  Drunk,
  Recluse,
  Clockmaker,
  FortuneTeller,
  Investigator,
  Librarian,
  Ravenkeeper,
  Slayer,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixNotActual("Aoife", Imp);
  game.fixNotActual("Tim", Imp);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Aoife", Poisoner).not() });
  applyClaims(game, PLAYERS);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function demonSitsStepsFromMinion(game: BOTCModel, steps: number) {
  return game.anyOf(
    PLAYER_NAMES.flatMap((demon, demonIndex) =>
      PLAYER_NAMES.flatMap((minion, minionIndex) => {
        const clockwise = (minionIndex - demonIndex + PLAYER_NAMES.length) % PLAYER_NAMES.length;
        const distance = Math.min(clockwise, PLAYER_NAMES.length - clockwise);
        return distance === steps
          ? [
              game.allOf(
                [
                  game.actualIs(demon, Imp),
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

if (import.meta.main && process.argv[1]?.endsWith("puzzle-13-clockblocking.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: "night_2",
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
