import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Baron,
  Chef,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Poisoner,
  Ravenkeeper,
  Recluse,
  ScarletWoman,
  Spy,
  Undertaker,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const PLAYERS = ["Adam", "Fraser", "Sarah", "Olivia", "You", "Aoife", "Tim"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const EVIL_ROLES = [Imp, Poisoner, Spy, Baron, ScarletWoman];
export const CHARACTERS = script(
  Imp,
  Poisoner,
  Spy,
  Baron,
  ScarletWoman,
  Drunk,
  Chef,
  Empath,
  FortuneTeller,
  Investigator,
  Ravenkeeper,
  Recluse,
  Undertaker,
);

type RedHerring = ReadonlyMap<string, BoolVar>;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.addImplication(game.roleInPlay(Baron), outsiderCount(game, 2));
  game.addImplication(game.roleInPlay(Baron).not(), outsiderCount(game, 0));
  game.fixNotActual("You", Imp);
  for (const minion of [Poisoner, Spy, Baron, ScarletWoman]) game.fixNotActual("You", minion);

  addClaim(game, "Adam", Investigator, [Investigator, Drunk, ...EVIL_ROLES]);
  addClaim(game, "Fraser", Recluse, [Recluse, ...EVIL_ROLES]);
  addClaim(game, "Sarah", Undertaker, [Undertaker, Drunk, ...EVIL_ROLES]);
  addClaim(game, "Olivia", FortuneTeller, [FortuneTeller, Drunk, ...EVIL_ROLES]);
  addClaim(game, "You", Chef, [Chef, Drunk]);
  addClaim(game, "Aoife", Empath, [Empath, Drunk, ...EVIL_ROLES]);
  addClaim(game, "Tim", Ravenkeeper, [Ravenkeeper, Drunk, ...EVIL_ROLES]);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2);
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [game.actualIs("Sarah", Poisoner).not(), game.actualIs("Tim", Poisoner).not()],
      "poisoner_alive_n3",
    ),
  });
  addDeathTimelineConstraints(game);

  const redHerrings = addFortuneTellerRedHerring(game);
  addInfo(
    game,
    "Adam",
    Investigator,
    NIGHT_1,
    Investigator.learnsRoleAmong(game, ["Aoife", "Fraser"], Spy, "adam_investigator"),
  );
  addInfo(game, "Sarah", Undertaker, NIGHT_2, Undertaker.learnsRole(game, "You", Spy));
  addInfo(
    game,
    "Olivia",
    FortuneTeller,
    NIGHT_1,
    fortuneTellerNo(game, redHerrings, ["Aoife", "Tim"], "olivia_ft_aoife_tim"),
  );
  addInfo(
    game,
    "Olivia",
    FortuneTeller,
    NIGHT_2,
    fortuneTellerNo(game, redHerrings, ["Aoife", "Olivia"], "olivia_ft_aoife_olivia"),
  );
  addInfo(game, "You", Chef, NIGHT_1, chefRegistersCount(game, 1, "you_chef"));
  addInfo(game, "Aoife", Empath, NIGHT_1, empathCount(game, ["You", "Tim"], 0, "aoife_empath_n1"));
  addInfo(game, "Aoife", Empath, NIGHT_2, empathCount(game, ["Adam", "Olivia"], 1, "aoife_empath_n2"));
  addInfo(game, "Aoife", Empath, NIGHT_3, empathCount(game, ["Adam", "Fraser"], 1, "aoife_empath_n3"));
  addInfo(game, "Tim", Ravenkeeper, NIGHT_2, game.actualIs("Olivia", Imp));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addClaim(game: BOTCModel, player: string, apparentRole: RoleRef, possibleRoles: readonly RoleRef[]): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, possibleRoles);
}

function outsiderCount(game: BOTCModel, count: number): BoolVar {
  return game.boolSumEquals(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    count,
    `outsider_count_${count}`,
  );
}

function addInfo(game: BOTCModel, player: string, role: RoleRef, poisonContext: string, info: BoolLike): void {
  game.addTruthfulInfoClaim(player, role, info, { poisonContext });
}

function addDeathTimelineConstraints(game: BOTCModel): void {
  game.addImplication(game.actualIs("Sarah", Imp), scarletWomanCanExplainNightThreeDeath(game, "sarah_imp_executed"));
  game.addImplication(game.actualIs("Tim", Imp), scarletWomanCanExplainNightThreeDeath(game, "tim_imp_died"));
  game.addImplication(game.actualIs("Olivia", Imp), scarletWomanCanExplainNightThreeDeath(game, "olivia_imp_died"));
}

function scarletWomanCanExplainNightThreeDeath(game: BOTCModel, name: string): BoolVar {
  return game.anyOf(
    ["Adam", "Fraser", "Olivia", "Aoife"].map((player) => game.actualIs(player, ScarletWoman)),
    name,
  );
}

function addFortuneTellerRedHerring(game: BOTCModel): RedHerring {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Olivia", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerNo(
  game: BOTCModel,
  redHerrings: RedHerring,
  players: readonly [string, string],
  name: string,
): BoolVar {
  return game.not(
    game.anyOf(
      [
        ...players.map((player) => game.actualIs(player, Imp)),
        ...players.map((player) => redHerrings.get(player) as BoolVar),
      ],
      `${name}_yes`,
    ),
    `${name}_no`,
  );
}

function chefRegistersCount(game: BOTCModel, count: number, name: string): BoolVar {
  return game.boolSumEquals(
    game
      .adjacentPairs()
      .map(([left, right]) =>
        game.allOf(
          [game.registersAsEvil(left, name), game.registersAsEvil(right, name)],
          `${name}_${left}_${right}_evil_pair`,
        ),
      ),
    count,
    name,
  );
}

function empathCount(game: BOTCModel, players: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.registersAsEvil(player, name)),
    count,
    name,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-31-no-your-other-left.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", [Poisoner, Spy, Baron, ScarletWoman], { includeRole: true }),
      forcedRole("Outsider", [Drunk, Recluse], { includeRole: true }),
    ],
  });
