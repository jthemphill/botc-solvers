import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Chef,
  FortuneTeller,
  Goblin,
  Imp,
  Investigator,
  Librarian,
  Lunatic,
  Ravenkeeper,
  Slayer,
  Washerwoman,
  playerNames,
  script,
} from "../characters";

export const PLAYERS = ["Aoife", "Fraser", "Tom", "Sula", "You", "Hannah", "Matt", "Tim"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Goblin,
  Lunatic,
  Chef,
  FortuneTeller,
  Investigator,
  Librarian,
  Ravenkeeper,
  Slayer,
  Washerwoman,
);

type RedHerring = ReadonlyMap<string, BoolVar>;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.setCharacterCount(Goblin, 1);
  game.setCharacterCount(Lunatic, 1);

  addClaim(game, "Aoife", Ravenkeeper, [Ravenkeeper, Lunatic, Imp, Goblin]);
  addClaim(game, "Fraser", Goblin, [Lunatic, Imp, Goblin]);
  addClaim(game, "Tom", Librarian, [Librarian, Lunatic, Imp, Goblin]);
  addClaim(game, "Sula", Slayer, [Slayer, Lunatic, Imp, Goblin]);
  addClaim(game, "You", Chef, [Chef]);
  addClaim(game, "Hannah", Washerwoman, [Washerwoman, Lunatic, Imp, Goblin]);
  addClaim(game, "Matt", Investigator, [Investigator, Lunatic, Imp, Goblin]);
  addClaim(game, "Tim", FortuneTeller, [FortuneTeller, Lunatic, Imp, Goblin]);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    1,
  );

  const redHerrings = addFortuneTellerRedHerring(game);

  game.addTruthfulInfoClaim("Aoife", Ravenkeeper, game.actualIs("Matt", Investigator));
  game.addTruthfulInfoClaim(
    "Tom",
    Librarian,
    Librarian.learnsRoleAmong(game, ["Matt", "Fraser"], Lunatic, "tom_librarian"),
  );
  game.addImplication(game.actualIs("Sula", Slayer), isDemonOnDayTwo(game, "Matt").not());
  game.addTruthfulInfoClaim("You", Chef, Chef.learnsCount(game, 0, "you_chef", { registers: false }));
  game.addTruthfulInfoClaim(
    "Hannah",
    Washerwoman,
    Washerwoman.learnsRoleAmong(game, ["Tom", "Sula"], Librarian, "hannah_washerwoman"),
  );
  game.addTruthfulInfoClaim(
    "Matt",
    Investigator,
    Investigator.learnsRoleAmong(game, ["Aoife", "Fraser"], Goblin, "matt_investigator"),
  );
  game.addTruthfulInfoClaim(
    "Tim",
    FortuneTeller,
    game.allOf(
      [
        fortuneTellerCheck(game, redHerrings, ["Hannah", "Tim"], false, "tim_ft_1"),
        fortuneTellerCheck(game, redHerrings, ["Fraser", "Sula"], true, "tim_ft_2"),
      ],
      "tim_fortune_teller",
    ),
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

function addFortuneTellerRedHerring(game: BOTCModel): RedHerring {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Tim", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerCheck(
  game: BOTCModel,
  redHerrings: RedHerring,
  players: readonly [string, string],
  yes: boolean,
  name: string,
): BoolVar {
  const either = game.anyOf(
    [
      ...players.map((player) => game.actualIs(player, Imp)),
      ...players.map((player) => redHerrings.get(player) as BoolVar),
    ],
    `${name}_yes`,
  );
  return yes ? either : game.not(either, `${name}_no`);
}

function isDemonOnDayTwo(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf([game.actualIs("Aoife", Imp).not(), game.actualIs(player, Imp)], `${player}_starting_imp_day_2`),
      game.allOf([game.actualIs("Aoife", Imp), game.actualIs(player, Goblin)], `${player}_starpassed_goblin_day_2`),
    ],
    `${player}_demon_day_2`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-23-goblincore.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", Goblin, { includeRole: true }),
      forcedRole("Outsider", Lunatic, { includeRole: true }),
    ],
  });
