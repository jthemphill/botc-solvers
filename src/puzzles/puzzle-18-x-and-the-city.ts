import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel, type World } from "../model";
import { differentCharacterTypes } from "../predicates";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Balloonist,
  Drunk,
  FortuneTeller,
  Investigator,
  Juggler,
  Leviathan,
  Librarian,
  Recluse,
  Saint,
  SnakeCharmer,
  Xaan,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const PLAYERS = ["Aoife", "Tim", "Olivia", "Sarah", "You", "Steph", "Fraser", "Dan"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Leviathan,
  Xaan,
  Drunk,
  Saint,
  Recluse,
  Balloonist,
  FortuneTeller,
  Investigator,
  Juggler,
  Librarian,
  SnakeCharmer,
);
export const DEMON_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Demon });
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const OUTSIDER_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Outsider });

type Night = 1 | 2 | 3;
type XVars = Readonly<Record<Night, BoolVar>>;
type RedHerring = ReadonlyMap<string, BoolVar>;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Leviathan, 1);
  game.setCharacterCount(Xaan, 1);

  addClaim(game, "Aoife", [Balloonist, Drunk, Leviathan, Xaan], Balloonist);
  addClaim(game, "Tim", [Saint, Leviathan, Xaan], Saint);
  addClaim(game, "Olivia", [Investigator, Drunk, Leviathan, Xaan], Investigator);
  addClaim(game, "Sarah", [Recluse, Leviathan, Xaan], Recluse);
  addClaim(game, "You", [Librarian, Drunk], Librarian);
  addClaim(game, "Steph", [Juggler, Drunk, Leviathan, Xaan], Juggler);
  addClaim(game, "Fraser", [SnakeCharmer, Drunk, Leviathan, Xaan], SnakeCharmer);
  addClaim(game, "Dan", [FortuneTeller, Drunk, Leviathan, Xaan], FortuneTeller);

  const x = addXBranches(game);
  const redHerrings = addFortuneTellerRedHerring(game);

  addNightInfo(game, x, "Aoife", Balloonist, 2, differentCharacterTypes(game, "Olivia", "Aoife"));
  addNightInfo(game, x, "Aoife", Balloonist, 3, differentCharacterTypes(game, "You", "Aoife"));
  addNightInfo(
    game,
    x,
    "Olivia",
    Investigator,
    1,
    Investigator.learnsRoleAmong(game, ["Fraser", "Aoife"], Xaan, "olivia_investigator"),
  );
  addNightInfo(game, x, "You", Librarian, 1, Librarian.learnsRoleAmong(game, ["Aoife", "Tim"], Drunk, "you_librarian"));
  addNightInfo(
    game,
    x,
    "Steph",
    Juggler,
    2,
    Juggler.learnsCorrectCount(
      game,
      {
        Fraser: Leviathan,
        Aoife: Balloonist,
        Tim: Xaan,
      },
      2,
      "steph_juggler",
    ),
  );
  addSnakeCharmerChoice(game, x, 1, "Olivia");
  addSnakeCharmerChoice(game, x, 2, "Steph");
  addSnakeCharmerChoice(game, x, 3, "Aoife");
  addNightInfo(
    game,
    x,
    "Dan",
    FortuneTeller,
    1,
    fortuneTellerCheck(game, redHerrings, ["Tim", "Sarah"], false, "dan_ft_n1"),
  );
  addNightInfo(
    game,
    x,
    "Dan",
    FortuneTeller,
    2,
    fortuneTellerCheck(game, redHerrings, ["Steph", "Aoife"], false, "dan_ft_n2"),
  );
  addNightInfo(
    game,
    x,
    "Dan",
    FortuneTeller,
    3,
    fortuneTellerCheck(game, redHerrings, ["Fraser", "Olivia"], false, "dan_ft_n3"),
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addClaim(game: BOTCModel, player: string, possibleRoles: readonly RoleRef[], apparentRole: RoleRef): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, possibleRoles);
}

function addXBranches(game: BOTCModel): XVars {
  const x = {
    1: game.newBool("x_is_1"),
    2: game.newBool("x_is_2"),
    3: game.newBool("x_is_3"),
  } satisfies Record<Night, BoolVar>;
  game.addExactlyOne([x[1], x[2], x[3]]);
  const outsiders = PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider));
  game.addEnforcedExactlyN(outsiders, 1, x[1]);
  game.addEnforcedExactlyN(outsiders, 2, x[2]);
  game.addEnforcedExactlyN(outsiders, 3, x[3]);
  return x;
}

function addNightInfo(game: BOTCModel, x: XVars, player: string, role: RoleRef, night: Night, info: BoolLike): void {
  const active = game.allOf([game.actualIs(player, role), x[night].not()], `${player}_${night}_active_info`);
  game.addImplication(active, info);
}

function addSnakeCharmerChoice(game: BOTCModel, x: XVars, night: Night, chosen: string): void {
  addNightInfo(game, x, "Fraser", SnakeCharmer, night, game.actualIs(chosen, Leviathan).not());
}

function addFortuneTellerRedHerring(game: BOTCModel): RedHerring {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Dan", FortuneTeller),
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
      ...players.map((player) => game.actualIs(player, Leviathan)),
      ...players.map((player) => redHerrings.get(player) as BoolVar),
    ],
    `${name}_yes`,
  );
  return yes ? either : game.not(either, `${name}_no`);
}

export function forcedX(worlds: readonly World[]): number | undefined {
  const values = new Set(worlds.map((world) => outsiderCount(world)));
  return values.size === 1 ? [...values][0] : undefined;
}

function outsiderCount(world: World): number {
  return PLAYER_NAMES.filter((player) => OUTSIDER_ROLES.includes(world.actualRole(player))).length;
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-18-x-and-the-city.ts")) {
  const worlds = await solve();
  printSolution(worlds, PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", DEMON_ROLES, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
  console.log(`\nX: ${forcedX(worlds) ?? "not forced"}`);
}
