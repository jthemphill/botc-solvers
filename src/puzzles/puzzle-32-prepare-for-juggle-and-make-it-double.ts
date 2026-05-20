import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Baron,
  Dreamer,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Juggler,
  Poisoner,
  Recluse,
  Saint,
  Undertaker,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const PLAYERS = ["Dan", "Fraser", "Jasmine", "Tim", "You", "Matthew", "Olivia", "Sula"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const EVIL_ROLES = [Imp, Baron, Poisoner];
export const CHARACTERS = script(
  Imp,
  Baron,
  Poisoner,
  Drunk,
  Dreamer,
  Empath,
  FortuneTeller,
  Juggler,
  Recluse,
  Saint,
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
  game.addImplication(game.roleInPlay(Baron), outsiderCount(game, 3));
  game.addImplication(game.roleInPlay(Baron).not(), outsiderCount(game, 1));
  game.fixNotActual("You", Imp);
  for (const minion of [Baron, Poisoner]) game.fixNotActual("You", minion);
  game.fixNotActual("Tim", Imp);
  game.fixNotActual("Dan", Imp);

  addClaim(game, "Dan", Juggler, [Juggler, Drunk, ...EVIL_ROLES]);
  addClaim(game, "Fraser", Saint, [Saint, ...EVIL_ROLES]);
  addClaim(game, "Jasmine", Undertaker, [Undertaker, Drunk, ...EVIL_ROLES]);
  addClaim(game, "Tim", FortuneTeller, [FortuneTeller, Drunk, ...EVIL_ROLES]);
  addClaim(game, "You", Dreamer, [Dreamer, Drunk]);
  addClaim(game, "Matthew", Juggler, [Juggler, Drunk, ...EVIL_ROLES]);
  addClaim(game, "Olivia", Recluse, [Recluse, ...EVIL_ROLES]);
  addClaim(game, "Sula", Empath, [Empath, Drunk, ...EVIL_ROLES]);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2);
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [
        game.actualIs("Tim", Poisoner).not(),
        game.actualIs("Dan", Poisoner).not(),
        game.actualIs("Fraser", Poisoner).not(),
      ],
      "poisoner_alive_n3",
    ),
  });

  const redHerrings = addFortuneTellerRedHerring(game);
  addInfo(
    game,
    "Dan",
    Juggler,
    NIGHT_2,
    Juggler.learnsCorrectCount(game, { You: Dreamer, Fraser: Poisoner, Tim: Baron }, 0, "dan_juggler"),
  );
  addInfo(
    game,
    "Matthew",
    Juggler,
    NIGHT_2,
    Juggler.learnsCorrectCount(
      game,
      { You: Imp, Dan: Drunk, Jasmine: Baron, Tim: FortuneTeller },
      0,
      "matthew_juggler",
    ),
  );
  addInfo(game, "Jasmine", Undertaker, NIGHT_2, Undertaker.learnsRole(game, "You", Dreamer));
  addInfo(game, "Jasmine", Undertaker, NIGHT_3, Undertaker.learnsRole(game, "Dan", Juggler));
  addInfo(game, "Tim", FortuneTeller, NIGHT_1, fortuneTellerNo(game, redHerrings, ["Matthew", "Fraser"], "tim_ft"));
  addInfo(game, "You", Dreamer, NIGHT_1, Dreamer.learnsOneOf(game, "Sula", [Drunk, Imp], "you_dreamer"));
  addInfo(game, "Sula", Empath, NIGHT_1, empathCount(game, ["Olivia", "Dan"], 1, "sula_empath_n1"));
  addInfo(game, "Sula", Empath, NIGHT_2, empathCount(game, ["Olivia", "Dan"], 1, "sula_empath_n2"));
  addInfo(game, "Sula", Empath, NIGHT_3, empathCount(game, ["Olivia", "Jasmine"], 0, "sula_empath_n3"));

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

function empathCount(game: BOTCModel, players: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.registersAsEvil(player, name)),
    count,
    name,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-32-prepare-for-juggle-and-make-it-double.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", [Baron, Poisoner], { includeRole: true }),
      forcedRole("Drunk", Drunk, { includeRole: true }),
    ],
  });
