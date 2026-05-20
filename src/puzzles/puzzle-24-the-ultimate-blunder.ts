import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Chef,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Klutz,
  Librarian,
  Poisoner,
  Virgin,
  Washerwoman,
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const PLAYERS = [
  new Virgin({
    name: "Sula",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game) => game.hasCharacterType("Adam", CharacterType.Townsfolk).not(),
      },
    ],
  }),
  new Librarian({ name: "Oscar", role: Klutz, among: ["You", "Olivia"], poisonContext: NIGHT_1 }),
  new Chef({ name: "Adam", count: 1, poisonContext: NIGHT_1 }),
  new Empath({
    name: "Josh",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game) => empathAliveNeighborCount(game, ["You", "Adam"], 1, "josh_empath_n1"),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game) => empathAliveNeighborCount(game, ["Steph", "Adam"], 0, "josh_empath_n2"),
      },
    ],
  }),
  new Investigator({
    name: "You",
    role: Poisoner,
    among: ["Olivia", "Josh"],
    poisonContext: NIGHT_1,
  }),
  new Klutz({
    name: "Olivia",
    infoClaims: [{ poisonContext: NIGHT_2, learned: (game) => game.isGood("Adam") }],
  }),
  new FortuneTeller({
    name: "Steph",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) =>
          fortuneTellerCheck(game, context as RedHerring, 1, ["Steph", "Adam"], false, "steph_ft_n1"),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game, context) =>
          fortuneTellerCheck(game, context as RedHerring, 2, ["Steph", "Adam"], true, "steph_ft_n2"),
      },
    ],
  }),
  new Washerwoman({ name: "Fraser", role: Virgin, among: ["Olivia", "Sula"], poisonContext: NIGHT_1 }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Poisoner,
  Drunk,
  Klutz,
  Chef,
  Empath,
  FortuneTeller,
  Investigator,
  Librarian,
  Virgin,
  Washerwoman,
);

type RedHerring = ReadonlyMap<string, BoolVar>;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.setCharacterCount(Poisoner, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    1,
  );
  for (const evilRole of [Imp, Poisoner]) game.fixNotActual("You", evilRole);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, {
    activeIf: game.allOf(
      [game.actualIs("Olivia", Poisoner).not(), game.actualIs("Olivia", Imp).not()],
      "night_2_poisoner_still_active",
    ),
  });

  const redHerrings = addFortuneTellerRedHerring(game);
  applyClaims(game, PLAYERS, { context: redHerrings });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
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

function addFortuneTellerRedHerring(game: BOTCModel): RedHerring {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Steph", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerCheck(
  game: BOTCModel,
  redHerrings: RedHerring,
  night: 1 | 2,
  players: readonly [string, string],
  yes: boolean,
  name: string,
): BoolVar {
  const either = game.anyOf(
    [
      ...players.map((player) => isDemonAtNight(game, night, player)),
      ...players.map((player) => redHerrings.get(player) as BoolVar),
    ],
    `${name}_yes`,
  );
  return yes ? either : game.not(either, `${name}_no`);
}

function isDemonAtNight(game: BOTCModel, night: 1 | 2, player: string): BoolVar {
  if (night === 1) return game.actualIs(player, Imp);
  return game.anyOf(
    [
      player === "Olivia" ? game.constantBool(false, "olivia_dead_before_ft_n2") : game.actualIs(player, Imp),
      game.allOf([game.actualIs("Olivia", Imp), game.actualIs(player, Poisoner)], `${player}_poisoner_starpass_n2`),
    ],
    `${player}_demon_n2`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-24-the-ultimate-blunder.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_2,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", Poisoner, { includeRole: true }),
      forcedRole("Outsider", [Klutz, Drunk], { includeRole: true }),
    ],
  });
