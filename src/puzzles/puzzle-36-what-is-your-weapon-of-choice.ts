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
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const DAY_3 = "day_3";

export const PLAYERS = ["Sula", "Olivia", "Fraser", "Oscar", "You", "Steph", "Adam", "Josh"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const MINION_ROLES = [Baron, Poisoner, Spy, ScarletWoman];
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

  game.addClaim("Sula", Investigator, [Investigator, Drunk, Imp, ...MINION_ROLES]);
  game.addClaim("Olivia", FortuneTeller, [FortuneTeller, Drunk, Imp, ...MINION_ROLES]);
  game.addClaim("Fraser", Recluse, [Recluse, Imp, ...MINION_ROLES]);
  game.addClaim("Oscar", Slayer, [Slayer, Drunk, Imp, ...MINION_ROLES]);
  game.addClaim("You", Empath, [Empath, Drunk]);
  game.addClaim("Steph", Saint, [Saint, Imp, ...MINION_ROLES]);
  game.addClaim("Adam", Slayer, [Slayer, Drunk, Imp, ...MINION_ROLES]);
  game.addClaim("Josh", Ravenkeeper, [Ravenkeeper, Drunk, Imp, ...MINION_ROLES]);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2);
  game.addPoisonerEffect(DAY_3, {
    activeIf: game.allOf(
      [game.actualIs("Josh", Poisoner).not(), game.actualIs("Oscar", Poisoner).not()],
      "poisoner_alive_day_3",
    ),
  });

  const redHerrings = game.addFortuneTellerRedHerring("Olivia");

  game.addTruthfulInfoClaim(
    "Sula",
    Investigator,
    Investigator.learnsRoleAmong(game, ["Steph", "Josh"], Spy, "sula_investigator"),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim(
    "Olivia",
    FortuneTeller,
    game.fortuneTellerNo(redHerrings, ["Josh", "Oscar"], "olivia_ft_josh_oscar_no", (player) =>
      isDemonAtContext(game, player, NIGHT_1),
    ),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim(
    "Olivia",
    FortuneTeller,
    game.fortuneTellerNo(redHerrings, ["Adam", "Oscar"], "olivia_ft_adam_oscar_no", (player) =>
      isDemonAtContext(game, player, NIGHT_2),
    ),
    { poisonContext: NIGHT_2 },
  );
  game.addTruthfulInfoClaim("You", Empath, game.registeredEvilCount(["Oscar", "Steph"], 1, "you_empath_n1"), {
    poisonContext: NIGHT_1,
  });
  game.addTruthfulInfoClaim("Josh", Ravenkeeper, game.actualIs("Adam", ScarletWoman), {
    poisonContext: NIGHT_2,
  });

  const oscarActiveSlayer = game.allOf(
    [game.actualIs("Oscar", Slayer), game.poisoned("Oscar", NIGHT_2).not()],
    "oscar_active_slayer",
  );
  game.addImplication(oscarActiveSlayer, isDemonOnDayTwo(game, "Steph").not());

  const adamActiveSlayer = game.allOf(
    [game.actualIs("Adam", Slayer), game.poisoned("Adam", DAY_3).not()],
    "adam_active_slayer",
  );
  game.addImplication(adamActiveSlayer, isDemonOnDayThree(game, "Sula").not());
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
