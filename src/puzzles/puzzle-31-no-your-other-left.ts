import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
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
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const EVIL_ROLES = [Imp, Poisoner, Spy, Baron, ScarletWoman];
export const PLAYERS = [
  new Investigator({
    name: "Adam",
    role: Spy,
    among: ["Aoife", "Fraser"],
    poisonContext: NIGHT_1,
  }),
  new Recluse({ name: "Fraser" }),
  new Undertaker({
    name: "Sarah",
    player: "You",
    role: Spy,
    poisonContext: NIGHT_2,
  }),
  new FortuneTeller({
    name: "Olivia",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) =>
          fortuneTellerNo(game, context as RedHerring, ["Aoife", "Tim"], "olivia_ft_aoife_tim"),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game, context) =>
          fortuneTellerNo(game, context as RedHerring, ["Aoife", "Olivia"], "olivia_ft_aoife_olivia"),
      },
    ],
  }),
  new Chef({
    name: "You",
    infoClaims: [{ poisonContext: NIGHT_1, learned: (game) => chefRegistersCount(game, 1, "you_chef") }],
  }),
  new Empath({
    name: "Aoife",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => empathCount(game, ["You", "Tim"], 0, "aoife_empath_n1") },
      { poisonContext: NIGHT_2, learned: (game) => empathCount(game, ["Adam", "Olivia"], 1, "aoife_empath_n2") },
      { poisonContext: NIGHT_3, learned: (game) => empathCount(game, ["Adam", "Fraser"], 1, "aoife_empath_n3") },
    ],
  }),
  new Ravenkeeper({
    name: "Tim",
    infoClaims: [{ poisonContext: NIGHT_2, learned: (game) => game.actualIs("Olivia", Imp) }],
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
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
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixNotActual("You", Imp);
  for (const minion of [Poisoner, Spy, Baron, ScarletWoman]) game.fixNotActual("You", minion);

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
  applyClaims(game, PLAYERS, { context: redHerrings });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
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
