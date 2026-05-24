import { night, day, type Timing } from "../model";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Baron,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Poisoner,
  Ravenkeeper,
  Recluse,
  Saint,
  ScarletWoman,
  Slayer,
  Spy,
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = night(1);
export const NIGHT_2 = night(2);
export const DAY_3 = day(3);

export const MINION_ROLES = [Baron, Poisoner, Spy, ScarletWoman];
export const PLAYERS = [
  new Investigator({
    name: "Sula",
    role: Spy,
    among: ["Steph", "Josh"],
    timing: "night_1",
  }),
  new FortuneTeller({
    name: "Olivia",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game, context) =>
          game.fortuneTellerNo(
            context as ReadonlyMap<string, BoolVar>,
            ["Josh", "Oscar"],
            "olivia_ft_josh_oscar_no",
            (player) => isDemonAtTiming(game, player, NIGHT_1),
          ),
      },
      {
        timing: "night_2",
        learned: (game, context) =>
          game.fortuneTellerNo(
            context as ReadonlyMap<string, BoolVar>,
            ["Adam", "Oscar"],
            "olivia_ft_adam_oscar_no",
            (player) => isDemonAtTiming(game, player, NIGHT_2),
          ),
      },
    ],
  }),
  new Recluse({ name: "Fraser" }),
  new Slayer({
    timing: "day_1",
    name: "Oscar",
    infoClaims: [{ timing: "night_2", learned: (game) => isDemonOnDayTwo(game, "Steph").not() }],
  }),
  new Empath({
    name: "You",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) => game.registeredEvilCount(["Oscar", "Steph"], 1, "you_empath_n1"),
      },
    ],
  }),
  new Saint({ name: "Steph" }),
  new Slayer({
    timing: "day_1",
    name: "Adam",
    infoClaims: [{ timing: "day_3", learned: (game) => isDemonOnDayThree(game, "Sula").not() }],
  }),
  new Ravenkeeper({
    timing: "night_2",
    name: "Josh",
    infoClaims: [{ timing: "night_2", learned: (game) => game.actualIs("Adam", ScarletWoman) }],
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Baron,
  Poisoner,
  Spy,
  ScarletWoman,
  Drunk,
  Recluse,
  Saint,
  Empath,
  FortuneTeller,
  Investigator,
  Ravenkeeper,
  Slayer,
);
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixNotActual("You", Imp);
  for (const minion of MINION_ROLES) game.fixNotActual("You", minion);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2);
  game.addPoisonerEffect(DAY_3, {
    activeIf: game.allOf(
      [game.actualIs("Josh", Poisoner).not(), game.actualIs("Oscar", Poisoner).not()],
      "poisoner_alive_day_3",
    ),
  });

  const redHerrings = game.addFortuneTellerRedHerring("Olivia");
  applyClaims(game, PLAYERS, { context: redHerrings });
  game.addTruth(
    game.anyOf(
      PLAYER_NAMES.map((player) => isDemonOnNightThree(game, player)),
      "night_3_demon_exists_to_kill_olivia",
    ),
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function isDemonAtTiming(game: BOTCModel, player: string, timing: Timing): BoolVar {
  if (timing === NIGHT_1) return game.actualIs(player, Imp);
  if (timing === NIGHT_2) return isDemonOnDayTwo(game, player);
  return isDemonOnDayThree(game, player);
}

function isDemonOnDayTwo(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf([game.actualIs(player, Imp), game.actualIs("Josh", Imp).not()], `${player}_starting_imp_day_2`),
      player === "Josh" || player === "You"
        ? game.constantBool(false, `${player}_cannot_be_josh_starpass_day_2`)
        : game.allOf([game.actualIs("Josh", Imp), game.isMinion(player)], `${player}_josh_starpass_day_2`),
    ],
    `${player}_demon_day_2`,
  );
}

function isDemonOnNightThree(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf(
        [game.actualIs(player, Imp), game.actualIs("Josh", Imp).not(), game.actualIs("Oscar", Imp).not()],
        `${player}_starting_imp_night_3`,
      ),
      player === "Josh" || player === "Oscar" || player === "You"
        ? game.constantBool(false, `${player}_cannot_be_josh_starpass_night_3`)
        : game.allOf([game.actualIs("Josh", Imp), game.isMinion(player)], `${player}_josh_starpass_night_3`),
      player === "Josh" || player === "Oscar" || player === "You"
        ? game.constantBool(false, `${player}_cannot_be_scarlet_woman_night_3`)
        : game.allOf([game.actualIs("Oscar", Imp), game.actualIs(player, ScarletWoman)], `${player}_sw_after_oscar`),
    ],
    `${player}_demon_night_3`,
  );
}

function isDemonOnDayThree(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      player === "Olivia" ? game.constantBool(false, "olivia_dead_before_day_3") : isDemonOnNightThree(game, player),
      player === "Olivia" || player === "Josh" || player === "Oscar" || player === "You"
        ? game.constantBool(false, `${player}_cannot_receive_olivia_starpass_day_3`)
        : game.allOf([isDemonOnNightThree(game, "Olivia"), game.isMinion(player)], `${player}_olivia_starpass_day_3`),
    ],
    `${player}_demon_day_3`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-36-what-is-your-weapon-of-choice.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: "night_2",
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk),
    ],
  });
