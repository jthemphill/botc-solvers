import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Chambermaid,
  Clockmaker,
  Drunk,
  Empath,
  FortuneTeller,
  Juggler,
  Librarian,
  NoDashii,
  Oracle,
  Pukka,
  ScarletWoman,
  Undertaker,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const PLAYERS = ["Adam", "Oscar", "Olivia", "Sarah", "You", "Matt", "Fraser", "Aoife"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Pukka,
  NoDashii,
  ScarletWoman,
  Drunk,
  Chambermaid,
  Clockmaker,
  Empath,
  FortuneTeller,
  Juggler,
  Librarian,
  Oracle,
  Undertaker,
);
export const DEMON_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Demon });
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });

type RedHerring = ReadonlyMap<string, BoolVar>;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isDemon(player)),
    1,
  );
  game.setCharacterCount(ScarletWoman, 1);
  game.setCharacterCount(Drunk, 1);

  addClaim(game, "Adam", Clockmaker, [Clockmaker, Drunk, Pukka, NoDashii, ScarletWoman]);
  addClaim(game, "Oscar", Empath, [Empath, Drunk, Pukka, NoDashii, ScarletWoman]);
  addClaim(game, "Olivia", FortuneTeller, [FortuneTeller, Drunk, Pukka, NoDashii, ScarletWoman]);
  addClaim(game, "Sarah", Oracle, [Oracle, Drunk, Pukka, NoDashii, ScarletWoman]);
  addClaim(game, "You", Chambermaid, [Chambermaid, Drunk]);
  addClaim(game, "Matt", Juggler, [Juggler, Drunk, Pukka, NoDashii, ScarletWoman]);
  addClaim(game, "Fraser", Undertaker, [Undertaker, Drunk, Pukka, NoDashii, ScarletWoman]);
  addClaim(game, "Aoife", Librarian, [Librarian, Drunk, Pukka, NoDashii, ScarletWoman]);

  game.allowPoisonInContext(NIGHT_1);
  game.allowPoisonInContext(NIGHT_2);
  game.allowPoisonInContext(NIGHT_3);
  game.addImplication(game.roleInPlay(Pukka), game.poisoned("You", NIGHT_1));
  game.addImplication(game.roleInPlay(Pukka), game.poisoned("Sarah", NIGHT_2));
  for (const player of PLAYER_NAMES) {
    if (player !== "You") game.addImplication(game.roleInPlay(Pukka), game.poisoned(player, NIGHT_1).not());
    if (player !== "Sarah") game.addImplication(game.roleInPlay(Pukka), game.poisoned(player, NIGHT_2).not());
    game.addImplication(game.roleInPlay(Pukka), game.poisoned(player, NIGHT_3).not());
    game.addImplication(game.roleInPlay(NoDashii), game.poisoned(player, NIGHT_1).not());
    game.addImplication(game.roleInPlay(NoDashii), game.poisoned(player, NIGHT_2).not());
    game.addImplication(game.roleInPlay(NoDashii), game.poisoned(player, NIGHT_3).not());
  }

  const redHerrings = addFortuneTellerRedHerring(game);
  addInfo(game, "Adam", Clockmaker, NIGHT_1, demonOppositeMinion(game));
  addInfo(game, "Oscar", Empath, NIGHT_1, empathAliveNeighborCount(game, ["Adam", "Olivia"], 1, "oscar_empath_n1"));
  addInfo(game, "Oscar", Empath, NIGHT_2, empathAliveNeighborCount(game, ["Aoife", "Olivia"], 2, "oscar_empath_n2"));
  addInfo(game, "Oscar", Empath, NIGHT_3, empathAliveNeighborCount(game, ["Fraser", "Olivia"], 1, "oscar_empath_n3"));
  addInfo(
    game,
    "Olivia",
    FortuneTeller,
    NIGHT_1,
    fortuneTellerCheck(game, redHerrings, NIGHT_1, ["Olivia", "Sarah"], false, "olivia_ft_n1"),
  );
  addInfo(
    game,
    "Olivia",
    FortuneTeller,
    NIGHT_2,
    fortuneTellerCheck(game, redHerrings, NIGHT_2, ["Olivia", "Aoife"], false, "olivia_ft_n2"),
  );
  addInfo(
    game,
    "Olivia",
    FortuneTeller,
    NIGHT_3,
    fortuneTellerCheck(game, redHerrings, NIGHT_3, ["Matt", "Oscar"], false, "olivia_ft_n3"),
  );
  addInfo(game, "Sarah", Oracle, NIGHT_2, deadEvilCount(game, ["Adam", "You"], 1, "sarah_oracle_n2"));
  addInfo(game, "You", Chambermaid, NIGHT_1, chambermaidWokeCount(game, ["Adam", "Sarah"], 1, "you_chambermaid"));
  addInfo(
    game,
    "Matt",
    Juggler,
    NIGHT_1,
    Juggler.learnsCorrectCount(game, { Fraser: Undertaker, Oscar: NoDashii }, 2, "matt_juggler"),
  );
  addInfo(
    game,
    "Fraser",
    Undertaker,
    NIGHT_2,
    game.allOf([game.actualIs("Adam", Drunk), game.actualIs("Aoife", NoDashii)], "fraser_undertaker_claims"),
  );
  addInfo(
    game,
    "Aoife",
    Librarian,
    NIGHT_1,
    Librarian.learnsRoleAmong(game, ["Matt", "Adam"], Drunk, "aoife_librarian"),
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

function addInfo(game: BOTCModel, player: string, role: RoleRef, poisonContext: string, info: BoolLike): void {
  const active = game.allOf(
    [
      game.actualIs(player, role),
      game.poisoned(player, poisonContext).not(),
      noDashiiPoisoned(game, player, poisonContext).not(),
    ],
    `${player}_${poisonContext}_active_info`,
  );
  game.addImplication(active, info);
}

function noDashiiPoisoned(game: BOTCModel, player: string, poisonContext: string): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.flatMap((demon) => {
      const [left, right] = game.neighbors(demon);
      return player === left || player === right
        ? [
            game.allOf(
              [isNoDashiiAtContext(game, demon, poisonContext), game.hasCharacterType(player, CharacterType.Townsfolk)],
              `${player}_poisoned_by_no_dashii_${demon}`,
            ),
          ]
        : [];
    }),
    `${player}_poisoned_by_no_dashii`,
  );
}

function isNoDashiiAtContext(game: BOTCModel, player: string, poisonContext: string): BoolVar {
  if (poisonContext === NIGHT_1) return game.actualIs(player, NoDashii);
  return game.anyOf(
    [
      player === "Adam" ? game.constantBool(false, `${player}_dead_${poisonContext}`) : game.actualIs(player, NoDashii),
      game.allOf(
        [game.actualIs("Adam", NoDashii), game.actualIs(player, ScarletWoman)],
        `${player}_sw_no_dashii_${poisonContext}`,
      ),
      poisonContext === NIGHT_3
        ? game.allOf(
            [game.actualIs("Aoife", NoDashii), game.actualIs(player, ScarletWoman)],
            `${player}_sw_after_aoife_no_dashii`,
          )
        : game.constantBool(false, `${player}_no_aoife_sw_${poisonContext}`),
    ],
    `${player}_no_dashii_${poisonContext}`,
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

function deadEvilCount(game: BOTCModel, deadPlayers: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    deadPlayers.map((player) => game.isEvil(player)),
    count,
    name,
  );
}

function chambermaidWokeCount(game: BOTCModel, players: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    players.map((player) =>
      game.anyOf(
        [Pukka, NoDashii, Chambermaid, Clockmaker, Empath, FortuneTeller, Librarian].map((role) =>
          game.actualIs(player, role),
        ),
        `${name}_${player}_woke`,
      ),
    ),
    count,
    name,
  );
}

function demonOppositeMinion(game: BOTCModel): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((demon, index) =>
      game.allOf(
        [game.isDemon(demon), game.actualIs(PLAYER_NAMES[(index + 4) % PLAYER_NAMES.length] as string, ScarletWoman)],
        `${demon}_opposite_minion`,
      ),
    ),
    "demon_opposite_minion",
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

function fortuneTellerCheck(
  game: BOTCModel,
  redHerrings: RedHerring,
  poisonContext: string,
  players: readonly [string, string],
  yes: boolean,
  name: string,
): BoolVar {
  const either = game.anyOf(
    [
      ...players.map((player) => isDemonAtContext(game, player, poisonContext)),
      ...players.map((player) => redHerrings.get(player) as BoolVar),
    ],
    `${name}_yes`,
  );
  return yes ? either : game.not(either, `${name}_no`);
}

function isDemonAtContext(game: BOTCModel, player: string, poisonContext: string): BoolVar {
  if (poisonContext === NIGHT_1) return game.isDemon(player);
  return game.anyOf(
    [
      player === "Adam" ? game.constantBool(false, `${player}_dead_demon_${poisonContext}`) : game.isDemon(player),
      game.allOf(
        [
          game.anyOf([game.actualIs("Adam", Pukka), game.actualIs("Adam", NoDashii)], "adam_starting_demon"),
          game.actualIs(player, ScarletWoman),
        ],
        `${player}_sw_demon_${poisonContext}`,
      ),
      poisonContext === NIGHT_3
        ? game.allOf(
            [
              game.anyOf([game.actualIs("Aoife", Pukka), game.actualIs("Aoife", NoDashii)], "aoife_starting_demon"),
              game.actualIs(player, ScarletWoman),
            ],
            `${player}_sw_after_aoife_demon`,
          )
        : game.constantBool(false, `${player}_no_aoife_demon_${poisonContext}`),
    ],
    `${player}_demon_${poisonContext}`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-28-a-study-in-scarlet.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", DEMON_ROLES, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Outsider", Drunk, { includeRole: true }),
    ],
  });
