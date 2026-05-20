import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Baron,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Librarian,
  Poisoner,
  Ravenkeeper,
  Recluse,
  Saint,
  ScarletWoman,
  Spy,
  Washerwoman,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const PLAYERS = ["Tom", "Oscar", "Sula", "Fraser", "You", "Olivia", "Jasmine", "Hannah"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const EVIL_ROLES = [Imp, Baron, Poisoner, Spy, ScarletWoman];
export const CHARACTERS = script(
  Imp,
  Baron,
  Poisoner,
  Spy,
  ScarletWoman,
  Drunk,
  Empath,
  FortuneTeller,
  Investigator,
  Librarian,
  Ravenkeeper,
  Recluse,
  Saint,
  Washerwoman,
);

type RedHerring = ReadonlyMap<string, BoolVar>;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.addImplication(game.roleInPlay(Baron), outsiderCount(game, 3));
  game.addImplication(game.roleInPlay(Baron).not(), outsiderCount(game, 1));
  game.fixNotActual("You", Imp);
  for (const minion of [Baron, Poisoner, Spy, ScarletWoman]) game.fixNotActual("You", minion);

  addClaim(game, "Tom", Librarian, [Librarian, Drunk, ...EVIL_ROLES]);
  addClaim(game, "Oscar", FortuneTeller, [FortuneTeller, Drunk, ...EVIL_ROLES]);
  addClaim(game, "Sula", Saint, [Saint, ...EVIL_ROLES]);
  addClaim(game, "Fraser", Investigator, [Investigator, Drunk, ...EVIL_ROLES]);
  addClaim(game, "You", Empath, [Empath, Drunk]);
  addClaim(game, "Olivia", Recluse, [Recluse, ...EVIL_ROLES]);
  addClaim(game, "Jasmine", Ravenkeeper, [Ravenkeeper, Drunk, ...EVIL_ROLES]);
  addClaim(game, "Hannah", Washerwoman, [Washerwoman, Drunk, ...EVIL_ROLES]);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2);
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [
        game.actualIs("Olivia", Poisoner).not(),
        game.actualIs("Fraser", Poisoner).not(),
        game.actualIs("Olivia", Imp).not(),
      ],
      "poisoner_alive_n3",
    ),
  });
  addDeathTimelineConstraints(game);

  const redHerrings = addFortuneTellerRedHerring(game);
  addInfo(game, "Tom", Librarian, NIGHT_1, Librarian.learnsRoleAmong(game, ["Olivia", "Sula"], Saint, "tom_librarian"));
  addInfo(
    game,
    "Oscar",
    FortuneTeller,
    NIGHT_1,
    fortuneTellerNo(game, redHerrings, NIGHT_1, ["Sula", "Fraser"], "oscar_ft_n1"),
  );
  addInfo(
    game,
    "Oscar",
    FortuneTeller,
    NIGHT_2,
    fortuneTellerNo(game, redHerrings, NIGHT_2, ["Tom", "Sula"], "oscar_ft_n2"),
  );
  addInfo(
    game,
    "Oscar",
    FortuneTeller,
    NIGHT_3,
    fortuneTellerNo(game, redHerrings, NIGHT_3, ["Hannah", "Tom"], "oscar_ft_n3"),
  );
  addInfo(
    game,
    "Fraser",
    Investigator,
    NIGHT_1,
    Investigator.learnsRoleAmong(game, ["You", "Jasmine"], Poisoner, "fraser_investigator"),
  );
  addInfo(game, "You", Empath, NIGHT_1, empathCount(game, ["Olivia", "Fraser"], 0, "you_empath"));
  addInfo(game, "Jasmine", Ravenkeeper, NIGHT_3, game.actualIs("Hannah", Washerwoman));
  addInfo(
    game,
    "Hannah",
    Washerwoman,
    NIGHT_1,
    Washerwoman.learnsRoleAmong(game, ["Sula", "Fraser"], Investigator, "hannah_washerwoman"),
  );

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
  game.addImplication(game.actualIs("Olivia", Imp), minionCanExplainNightThreeDeath(game, "olivia_imp_starpass"));
  game.addImplication(game.actualIs("Fraser", Imp), scarletWomanCanExplainNightThreeDeath(game, "fraser_imp_executed"));
}

function minionCanExplainNightThreeDeath(game: BOTCModel, name: string): BoolVar {
  return game.anyOf(
    ["Tom", "Oscar", "Sula", "Hannah"].map((player) => game.isMinion(player)),
    name,
  );
}

function scarletWomanCanExplainNightThreeDeath(game: BOTCModel, name: string): BoolVar {
  return game.anyOf(
    ["Tom", "Oscar", "Sula", "Hannah"].map((player) => game.actualIs(player, ScarletWoman)),
    name,
  );
}

function addFortuneTellerRedHerring(game: BOTCModel): RedHerring {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Oscar", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerNo(
  game: BOTCModel,
  redHerrings: RedHerring,
  poisonContext: string,
  players: readonly [string, string],
  name: string,
): BoolVar {
  return game.not(
    game.anyOf(
      [
        ...players.map((player) => isDemonAtContext(game, player, poisonContext)),
        ...players.map((player) => redHerrings.get(player) as BoolVar),
      ],
      `${name}_yes`,
    ),
    `${name}_no`,
  );
}

function isDemonAtContext(game: BOTCModel, player: string, poisonContext: string): BoolVar {
  if (poisonContext === NIGHT_1) return game.actualIs(player, Imp);
  if (poisonContext === NIGHT_2)
    return game.anyOf(
      [
        game.allOf([game.actualIs(player, Imp), game.actualIs("Olivia", Imp).not()], `${player}_starting_imp_n2`),
        game.allOf([game.actualIs("Olivia", Imp), game.isMinion(player)], `${player}_olivia_starpass_imp_n2`),
      ],
      `${player}_demon_${poisonContext}`,
    );
  return game.anyOf(
    [
      game.allOf(
        [
          game.actualIs(player, Imp),
          game.actualIs("Olivia", Imp).not(),
          game.actualIs("Fraser", Imp).not(),
          game.actualIs("Jasmine", Imp).not(),
        ],
        `${player}_starting_imp_n3`,
      ),
      player === "Fraser" || player === "Jasmine"
        ? game.constantBool(false, "fraser_executed_after_olivia_starpass")
        : game.allOf([game.actualIs("Olivia", Imp), game.isMinion(player)], `${player}_olivia_starpass_imp_n3`),
      game.allOf([game.actualIs("Fraser", Imp), game.actualIs(player, ScarletWoman)], `${player}_scarlet_woman_imp_n3`),
      game.allOf([game.actualIs("Jasmine", Imp), game.isMinion(player)], `${player}_jasmine_starpass_imp_n3`),
    ],
    `${player}_demon_${poisonContext}`,
  );
}

function empathCount(game: BOTCModel, players: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.registersAsEvil(player, name)),
    count,
    name,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-33-twice-is-coincidence-thrice-is-proof.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", [Baron, Poisoner, Spy, ScarletWoman], { includeRole: true }),
      forcedRole("Drunk", Drunk, { includeRole: true }),
    ],
  });
