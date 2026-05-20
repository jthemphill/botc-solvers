import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
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
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const EVIL_ROLES = [Imp, Baron, Poisoner];
export const PLAYERS = [
  new Juggler({
    name: "Dan",
    guesses: { You: Dreamer, Fraser: Poisoner, Tim: Baron },
    correctCount: 0,
    poisonContext: NIGHT_2,
  }),
  new Saint({ name: "Fraser" }),
  new Undertaker({
    name: "Jasmine",
    infoClaims: [
      { poisonContext: NIGHT_2, learned: (game) => Undertaker.learnsRole(game, "You", Dreamer) },
      { poisonContext: NIGHT_3, learned: (game) => Undertaker.learnsRole(game, "Dan", Juggler) },
    ],
  }),
  new FortuneTeller({
    name: "Tim",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) => fortuneTellerNo(game, context as RedHerring, ["Matthew", "Fraser"], "tim_ft"),
      },
    ],
  }),
  new Dreamer({
    name: "You",
    player: "Sula",
    roles: [Drunk, Imp],
    poisonContext: NIGHT_1,
  }),
  new Juggler({
    name: "Matthew",
    guesses: { You: Imp, Dan: Drunk, Jasmine: Baron, Tim: FortuneTeller },
    correctCount: 0,
    poisonContext: NIGHT_2,
  }),
  new Recluse({ name: "Olivia" }),
  new Empath({
    name: "Sula",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => empathCount(game, ["Olivia", "Dan"], 1, "sula_empath_n1") },
      { poisonContext: NIGHT_2, learned: (game) => empathCount(game, ["Olivia", "Dan"], 1, "sula_empath_n2") },
      { poisonContext: NIGHT_3, learned: (game) => empathCount(game, ["Olivia", "Jasmine"], 0, "sula_empath_n3") },
    ],
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
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
  applyClaims(game, PLAYERS, { context: redHerrings });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function outsiderCount(game: BOTCModel, count: number): BoolVar {
  return game.boolSumEquals(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    count,
    `outsider_count_${count}`,
  );
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
