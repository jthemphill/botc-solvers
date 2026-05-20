import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
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
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const EVIL_ROLES = [Imp, Baron, Poisoner, Spy, ScarletWoman];
export const PLAYERS = [
  new Librarian({
    name: "Tom",
    role: Saint,
    among: ["Olivia", "Sula"],
    poisonContext: NIGHT_1,
  }),
  new FortuneTeller({
    name: "Oscar",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) =>
          fortuneTellerNo(game, context as RedHerring, NIGHT_1, ["Sula", "Fraser"], "oscar_ft_n1"),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game, context) =>
          fortuneTellerNo(game, context as RedHerring, NIGHT_2, ["Tom", "Sula"], "oscar_ft_n2"),
      },
      {
        poisonContext: NIGHT_3,
        learned: (game, context) =>
          fortuneTellerNo(game, context as RedHerring, NIGHT_3, ["Hannah", "Tom"], "oscar_ft_n3"),
      },
    ],
  }),
  new Saint({ name: "Sula" }),
  new Investigator({
    name: "Fraser",
    role: Poisoner,
    among: ["You", "Jasmine"],
    poisonContext: NIGHT_1,
  }),
  new Empath({
    name: "You",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => empathCount(game, ["Olivia", "Fraser"], 0, "you_empath") },
    ],
  }),
  new Recluse({ name: "Olivia" }),
  new Ravenkeeper({
    name: "Jasmine",
    infoClaims: [{ poisonContext: NIGHT_3, learned: (game) => game.actualIs("Hannah", Washerwoman) }],
  }),
  new Washerwoman({
    name: "Hannah",
    role: Investigator,
    among: ["Sula", "Fraser"],
    poisonContext: NIGHT_1,
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
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
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixNotActual("You", Imp);
  for (const minion of [Baron, Poisoner, Spy, ScarletWoman]) game.fixNotActual("You", minion);

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
  applyClaims(game, PLAYERS, { context: redHerrings });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
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
