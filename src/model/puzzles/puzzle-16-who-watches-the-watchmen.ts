import { night } from "../model";
import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Baron,
  Chef,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Nightwatchman,
  Poisoner,
  Recluse,
  Saint,
  ScarletWoman,
  Spy,
  Washerwoman,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = night(1);
export const NIGHT_2 = night(2);
export const NIGHT_3 = night(3);

export const PLAYERS = [
  new Recluse({ name: "Oscar" }),
  new Washerwoman({ name: "Hannah", role: Chef, among: ["Oscar", "Tim"], timing: "night_1" }),
  new Investigator({
    name: "Sarah",
    role: Poisoner,
    among: ["Olivia", "Hannah"],
    timing: "night_1",
  }),
  new Chef({ name: "Tim", count: 1, timing: "night_1" }),
  new Saint({ name: "You" }),
  new Empath({
    name: "Olivia",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) => empathAliveNeighborCount(game, ["You", "Jasmine"], 0, "olivia_empath_night_1"),
      },
      {
        timing: "night_2",
        learned: (game) => empathAliveNeighborCount(game, ["Tim", "Jasmine"], 1, "olivia_empath_night_2"),
      },
    ],
  }),
  new FortuneTeller({
    name: "Jasmine",
    checks: [
      {
        left: "Hannah",
        right: "Tim",
        yes: false,
        demonRole: Imp,
        registers: true,
        timing: "night_1",
      },
      {
        left: "Olivia",
        right: "Tim",
        yes: false,
        demonRole: Imp,
        registers: true,
        timing: "night_2",
      },
      {
        left: "Sarah",
        right: "Jasmine",
        yes: false,
        demonRole: Imp,
        registers: true,
        timing: "night_3",
      },
    ],
  }),
  new Nightwatchman({
    name: "Fraser",
    infoClaims: [{ timing: "night_1", learned: (game) => game.isEvil("Tim") }],
  }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Baron,
  Poisoner,
  ScarletWoman,
  Spy,
  Drunk,
  Recluse,
  Saint,
  Chef,
  Empath,
  FortuneTeller,
  Investigator,
  Nightwatchman,
  Washerwoman,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Hannah", Poisoner).not() });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [game.actualIs("Hannah", Poisoner).not(), game.actualIs("Fraser", Poisoner).not()],
      "poisoner_alive_night_3",
    ),
  });

  applyClaims(game, PLAYERS);
  game.fixActual("You", Saint);
  game.addTruth(demonCanKillAfterDayOne(game));
  game.addTruth(demonCanKillAfterDayTwo(game));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function demonCanKillAfterDayOne(game: BOTCModel): BoolVar {
  return game.anyOf(
    [
      roleAliveAfter(game, Imp, ["Hannah"], "imp_alive_after_day_1"),
      game.allOf(
        [
          game.actualIs("Hannah", Imp),
          roleAliveAfter(game, ScarletWoman, ["Hannah"], "scarlet_woman_alive_after_day_1"),
        ],
        "scarlet_woman_replaces_hannah",
      ),
    ],
    "demon_can_kill_after_day_1",
  );
}

function demonCanKillAfterDayTwo(game: BOTCModel): BoolVar {
  return game.anyOf(
    [
      roleAliveAfter(game, Imp, ["Hannah", "Fraser"], "imp_alive_after_day_2"),
      game.allOf(
        [
          game.anyOf([game.actualIs("Hannah", Imp), game.actualIs("Fraser", Imp)], "imp_died_by_day_2"),
          roleAliveAfter(game, ScarletWoman, ["Hannah", "Fraser"], "scarlet_woman_alive_after_day_2"),
        ],
        "scarlet_woman_replaces_by_day_2",
      ),
    ],
    "demon_can_kill_after_day_2",
  );
}

function roleAliveAfter(
  game: BOTCModel,
  role: typeof Imp | typeof ScarletWoman,
  deadPlayers: readonly string[],
  name: string,
): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.filter((player) => !deadPlayers.includes(player)).map((player) => game.actualIs(player, role)),
    name,
  );
}

function empathAliveNeighborCount(
  game: BOTCModel,
  aliveNeighbors: readonly string[],
  count: number,
  name: string,
): BoolVar {
  return game.boolSumEquals(
    aliveNeighbors.map((player) => game.registersAsEvil(player, name)),
    count,
    `${name}_alive_neighbor_count`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-16-who-watches-the-watchmen.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: "night_2",
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
