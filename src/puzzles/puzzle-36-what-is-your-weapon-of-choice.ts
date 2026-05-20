import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
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

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const DAY_3 = "day_3";

export const MINION_ROLES = [Baron, Poisoner, Spy, ScarletWoman];
export const PLAYERS = [
  new Investigator({
    name: "Sula",
    role: Spy,
    among: ["Steph", "Josh"],
    poisonContext: NIGHT_1,
  }),
  new FortuneTeller({
    name: "Olivia",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) =>
          game.fortuneTellerNo(
            context as ReadonlyMap<string, BoolVar>,
            ["Josh", "Oscar"],
            "olivia_ft_josh_oscar_no",
            (player) => isDemonAtContext(game, player, NIGHT_1),
          ),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game, context) =>
          game.fortuneTellerNo(
            context as ReadonlyMap<string, BoolVar>,
            ["Adam", "Oscar"],
            "olivia_ft_adam_oscar_no",
            (player) => isDemonAtContext(game, player, NIGHT_2),
          ),
      },
    ],
  }),
  new Recluse({ name: "Fraser" }),
  new Slayer({
    name: "Oscar",
    infoClaims: [{ poisonContext: NIGHT_2, learned: (game) => isDemonOnDayTwo(game, "Steph").not() }],
  }),
  new Empath({
    name: "You",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => game.registeredEvilCount(["Oscar", "Steph"], 1, "you_empath_n1") },
    ],
  }),
  new Saint({ name: "Steph" }),
  new Slayer({
    name: "Adam",
    infoClaims: [{ poisonContext: DAY_3, learned: (game) => isDemonOnDayThree(game, "Sula").not() }],
  }),
  new Ravenkeeper({
    name: "Josh",
    infoClaims: [{ poisonContext: NIGHT_2, learned: (game) => game.actualIs("Adam", ScarletWoman) }],
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

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.addBaronOutsiderCounts({ withoutBaron: 1, withBaron: 3 });
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
  applyClaims(game, PLAYERS, { drunkThinksOutOfPlayRole: true, context: redHerrings });
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

function isDemonAtContext(game: BOTCModel, player: string, poisonContext: string): BoolVar {
  if (poisonContext === NIGHT_1) return game.actualIs(player, Imp);
  if (poisonContext === NIGHT_2) return isDemonOnDayTwo(game, player);
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
    poisonContext: NIGHT_2,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk),
    ],
  });
