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
  Imp,
  Librarian,
  Poisoner,
  Recluse,
  Saint,
  ScarletWoman,
  Slayer,
  Soldier,
  Spy,
  Undertaker,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = night(1);
export const NIGHT_2 = night(2);
export const NIGHT_3 = night(3);

export const PLAYERS = [
  new Librarian({ name: "Matthew", role: Drunk, among: ["You", "Josh"], timing: "night_1" }),
  new Soldier({ name: "Josh" }),
  new Undertaker({
    name: "Sula",
    infoClaims: [
      { timing: "night_2", learned: (game) => game.actualIs("You", Empath) },
      { timing: "night_3", learned: (game) => game.actualIs("Dan", Slayer) },
    ],
  }),
  new Chef({ name: "Fraser", count: 2, timing: "night_1" }),
  new Empath({ name: "You", count: 0, timing: "night_1" }),
  new Saint({ name: "Olivia" }),
  new Slayer({
    timing: "day_1",
    name: "Dan",
    infoClaims: [{ timing: "night_2", learned: (game) => isDemonOnDayTwo(game, "Matthew").not() }],
  }),
  new Recluse({ name: "Tom" }),
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
  Librarian,
  Slayer,
  Soldier,
  Undertaker,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, {
    activeIf: game.allOf(
      [game.actualIs("Josh", Poisoner).not(), game.actualIs("Josh", Imp).not()],
      "night_2_poisoner_still_active",
    ),
  });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [
        game.actualIs("Josh", Poisoner).not(),
        game.actualIs("Dan", Poisoner).not(),
        game.actualIs("Olivia", Poisoner).not(),
        game.actualIs("Josh", Imp).not(),
        game.actualIs("Olivia", Imp).not(),
      ],
      "night_3_poisoner_still_active",
    ),
  });

  applyClaims(game, PLAYERS);
  game.addImplication(game.actualIs("Josh", Soldier), game.poisoned("Josh", NIGHT_2));
  game.addTruth(demonExistsAtNight(game, 2));
  game.addTruth(demonExistsAtNight(game, 3));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function demonExistsAtNight(game: BOTCModel, night: 2 | 3): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((player) => (night === 2 ? isDemonOnNightTwo(game, player) : isDemonOnNightThree(game, player))),
    `demon_exists_night_${night}`,
  );
}

function isDemonOnDayTwo(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf([game.actualIs("Josh", Imp).not(), game.actualIs(player, Imp)], `${player}_starting_imp_day_2`),
      game.allOf([game.actualIs("Josh", Imp), game.isMinion(player)], `${player}_starpass_after_josh_day_2`),
    ],
    `${player}_demon_day_2`,
  );
}

function isDemonOnNightTwo(game: BOTCModel, player: string): BoolVar {
  return game.actualIs(player, Imp);
}

function isDemonOnNightThree(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      ["Josh", "Dan"].includes(player)
        ? game.constantBool(false, `${player}_dead_before_n3`)
        : isDemonOnDayTwo(game, player),
      game.allOf(
        [
          isDemonOnDayTwo(game, "Dan"),
          game.actualIs(player, ScarletWoman),
          ["Josh", "Dan"].includes(player)
            ? game.constantBool(false, `${player}_sw_dead_before_n3`)
            : game.constantBool(true, `${player}_sw_alive_n3`),
        ],
        `${player}_sw_after_dan_n3`,
      ),
    ],
    `${player}_demon_n3`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-26-a-major-problem.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: "night_3",
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
