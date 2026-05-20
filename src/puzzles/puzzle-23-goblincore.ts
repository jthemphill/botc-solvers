import { CharacterType } from "../core";
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
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const PLAYERS = [
  new Ravenkeeper({
    name: "Aoife",
    infoClaims: [(game) => game.actualIs("Matt", Investigator)],
  }),
  new Goblin({ name: "Fraser" }),
  new Librarian({
    name: "Tom",
    role: Lunatic,
    among: ["Matt", "Fraser"],
  }),
  new Slayer({
    name: "Sula",
    infoClaims: [(game) => isDemonOnDayTwo(game, "Matt").not()],
  }),
  new Chef({ name: "You", count: 0, registers: false }),
  new Washerwoman({
    name: "Hannah",
    role: Librarian,
    among: ["Tom", "Sula"],
  }),
  new Investigator({
    name: "Matt",
    role: Goblin,
    among: ["Aoife", "Fraser"],
  }),
  new FortuneTeller({
    name: "Tim",
    infoClaims: [
      (game, context) =>
        game.allOf(
          [
            fortuneTellerCheck(game, context as RedHerring, ["Hannah", "Tim"], false, "tim_ft_1"),
            fortuneTellerCheck(game, context as RedHerring, ["Fraser", "Sula"], true, "tim_ft_2"),
          ],
          "tim_fortune_teller",
        ),
    ],
  }),
];
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
  game.fixActual("You", Chef);

  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    1,
  );

  const redHerrings = addFortuneTellerRedHerring(game);
  applyClaims(game, PLAYERS, { extraPossibleActualRoles: [Lunatic], context: redHerrings });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
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
