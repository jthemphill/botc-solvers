import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Baron,
  Butler,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Librarian,
  Poisoner,
  Recluse,
  Saint,
  ScarletWoman,
  Slayer,
  Spy,
  Washerwoman,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const PLAYERS = ["Hannah", "Fraser", "Tim", "Josh", "Adam", "You", "Matthew", "Steph", "Jasmine"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const MINION_ROLES = [Baron, Poisoner, Spy, ScarletWoman];
export const CHARACTERS = script(
  Imp,
  Baron,
  Poisoner,
  Spy,
  ScarletWoman,
  Butler,
  Drunk,
  Recluse,
  Saint,
  Empath,
  FortuneTeller,
  Investigator,
  Librarian,
  Slayer,
  Washerwoman,
);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.addImplication(game.roleInPlay(Baron), outsiderCount(game, 4));
  game.addImplication(game.roleInPlay(Baron).not(), outsiderCount(game, 2));
  game.fixNotActual("You", Imp);
  for (const minion of MINION_ROLES) game.fixNotActual("You", minion);
  for (const deadBeforeFinalNight of ["Josh", "Fraser", "Jasmine", "Tim"]) game.fixNotActual(deadBeforeFinalNight, Imp);

  addClaim(game, "Hannah", Saint, [Saint, Imp, ...MINION_ROLES]);
  addClaim(game, "Fraser", Librarian, [Librarian, Drunk, Imp, ...MINION_ROLES]);
  addClaim(game, "Tim", Empath, [Empath, Drunk, Imp, ...MINION_ROLES]);
  addClaim(game, "Josh", Butler, [Butler, Imp, ...MINION_ROLES]);
  addClaim(game, "Adam", Slayer, [Slayer, Drunk, Imp, ...MINION_ROLES]);
  addClaim(game, "You", Investigator, [Investigator, Drunk]);
  addClaim(game, "Matthew", FortuneTeller, [FortuneTeller, Drunk, Imp, ...MINION_ROLES]);
  addClaim(game, "Steph", Recluse, [Recluse, Imp, ...MINION_ROLES]);
  addClaim(game, "Jasmine", Washerwoman, [Washerwoman, Drunk, Imp, ...MINION_ROLES]);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Josh", Poisoner).not() });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [game.actualIs("Josh", Poisoner).not(), game.actualIs("Jasmine", Poisoner).not()],
      "poisoner_active_n3",
    ),
  });

  const redHerrings = addFortuneTellerRedHerring(game);

  game.addTruthfulInfoClaim(
    "Fraser",
    Librarian,
    game.anyOf(
      [
        game.registersAsRole("Jasmine", Drunk, "fraser_librarian_jasmine"),
        game.registersAsRole("Hannah", Drunk, "fraser_librarian_hannah"),
      ],
      "fraser_librarian_drunk",
    ),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim("Tim", Empath, empathCount(game, ["Fraser", "Josh"], 2, "tim_empath_n1"), {
    poisonContext: NIGHT_1,
  });
  game.addTruthfulInfoClaim("Tim", Empath, empathCount(game, ["Adam", "Hannah"], 1, "tim_empath_n2"), {
    poisonContext: NIGHT_2,
  });
  game.addTruthfulInfoClaim(
    "You",
    Investigator,
    game.anyOf(
      [
        game.registersAsRole("Steph", ScarletWoman, "you_investigator_steph"),
        game.registersAsRole("Fraser", ScarletWoman, "you_investigator_fraser"),
      ],
      "you_investigator_scarlet_woman",
    ),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim(
    "Matthew",
    FortuneTeller,
    game.allOf(
      [
        fortuneTellerNo(game, redHerrings, ["Tim", "Josh"], "matthew_ft_tim_josh_no"),
        fortuneTellerNo(game, redHerrings, ["Hannah", "Tim"], "matthew_ft_hannah_tim_no"),
        fortuneTellerYes(game, redHerrings, ["You", "Matthew"], "matthew_ft_you_self_yes"),
      ],
      "matthew_fortune_teller_checks",
    ),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim(
    "Jasmine",
    Washerwoman,
    game.anyOf(
      [
        game.registersAsRole("Tim", Empath, "jasmine_washerwoman_tim"),
        game.registersAsRole("Adam", Empath, "jasmine_washerwoman_adam"),
      ],
      "jasmine_washerwoman_empath",
    ),
    { poisonContext: NIGHT_1 },
  );

  const activeSlayer = game.allOf(
    [game.actualIs("Adam", Slayer), game.poisoned("Adam", NIGHT_3).not()],
    "adam_active_slayer",
  );
  game.addImplication(activeSlayer, game.registersAsRole("Matthew", Imp, "adam_slayer_matthew").not());

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addClaim(game: BOTCModel, player: string, apparentRole: RoleRef, possibleRoles: readonly RoleRef[]): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, possibleRoles);
  if (possibleRoles.includes(Drunk)) game.addDrunkThinksOutOfPlayRole(player, apparentRole, Drunk);
}

function outsiderCount(game: BOTCModel, count: number): BoolVar {
  return game.boolSumEquals(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    count,
    `outsider_count_${count}`,
  );
}

function empathCount(game: BOTCModel, players: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.registersAsEvil(player, `${name}_${player}`)),
    count,
    name,
  );
}

function addFortuneTellerRedHerring(game: BOTCModel): ReadonlyMap<string, BoolVar> {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Matthew", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerYes(
  game: BOTCModel,
  redHerrings: ReadonlyMap<string, BoolVar>,
  players: readonly [string, string],
  name: string,
): BoolVar {
  return game.anyOf(
    [
      ...players.map((player) => game.registersAsRole(player, Imp, `${name}_${player}`)),
      ...players.map((player) => redHerrings.get(player) as BoolVar),
    ],
    name,
  );
}

function fortuneTellerNo(
  game: BOTCModel,
  redHerrings: ReadonlyMap<string, BoolVar>,
  players: readonly [string, string],
  name: string,
): BoolVar {
  return game.not(fortuneTellerYes(game, redHerrings, players, `${name}_yes`), name);
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-40-nine-lives.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_3,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk),
    ],
  });
