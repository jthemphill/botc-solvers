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
  Poisoner,
  Ravenkeeper,
  Recluse,
  Saint,
  ScarletWoman,
  SnakeCharmer,
  Spy,
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const MINION_ROLES = [Baron, Poisoner, Spy, ScarletWoman];
export const PLAYERS = [
  new SnakeCharmer({
    name: "Tim",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => isDemonAtContext(game, "Matt", NIGHT_1).not() },
      { poisonContext: NIGHT_2, learned: (game) => isDemonAtContext(game, "Sula", NIGHT_2).not() },
      { poisonContext: NIGHT_3, learned: (game) => isDemonAtContext(game, "Hannah", NIGHT_3).not() },
    ],
  }),
  new SnakeCharmer({
    name: "Fraser",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => isDemonAtContext(game, "Sula", NIGHT_1).not() },
      { poisonContext: NIGHT_2, learned: (game) => isDemonAtContext(game, "Hannah", NIGHT_2).not() },
      { poisonContext: NIGHT_3, learned: (game) => isDemonAtContext(game, "Adam", NIGHT_3).not() },
    ],
  }),
  new FortuneTeller({
    name: "Sula",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) =>
          game.fortuneTellerNo(
            context as ReadonlyMap<string, BoolVar>,
            ["You", "Tim"],
            "sula_ft_you_tim_no",
            (player) => isDemonAtContext(game, player, NIGHT_1),
          ),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game, context) =>
          game.fortuneTellerNo(
            context as ReadonlyMap<string, BoolVar>,
            ["Fraser", "Matt"],
            "sula_ft_fraser_matt_no",
            (player) => isDemonAtContext(game, player, NIGHT_2),
          ),
      },
    ],
  }),
  new Saint({ name: "Matt" }),
  new Recluse({ name: "You" }),
  new Empath({
    name: "Hannah",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => game.registeredEvilCount(["You", "Dan"], 0, "hannah_empath_n1") },
      { poisonContext: NIGHT_2, learned: (game) => game.registeredEvilCount(["Adam", "Matt"], 1, "hannah_empath_n2") },
      {
        poisonContext: NIGHT_3,
        learned: (game) => game.registeredEvilCount(["Adam", "Fraser"], 1, "hannah_empath_n3"),
      },
    ],
  }),
  new Ravenkeeper({
    name: "Dan",
    infoClaims: [{ poisonContext: NIGHT_2, learned: (game) => game.actualIs("Fraser", Poisoner) }],
  }),
  new Investigator({
    name: "Adam",
    role: Baron,
    among: ["Tim", "Sula"],
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
  Recluse,
  Saint,
  Empath,
  FortuneTeller,
  Investigator,
  Ravenkeeper,
  SnakeCharmer,
);
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixNotActual("You", Imp);
  for (const minion of MINION_ROLES) game.fixNotActual("You", minion);
  game.fixNotActual("You", Drunk);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Dan", Poisoner).not() });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [
        game.actualIs("Dan", Poisoner).not(),
        game.actualIs("Sula", Poisoner).not(),
        isDemonOnNightThree(game, "Matt").not(),
      ],
      "poisoner_active_n3",
    ),
  });

  const redHerrings = game.addFortuneTellerRedHerring("Sula");
  applyClaims(game, PLAYERS, { context: redHerrings });

  game.addTruth(
    game.anyOf(
      PLAYER_NAMES.map((player) => isDemonOnNightThree(game, player)),
      "night_3_demon_exists_to_kill_matt",
    ),
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function isDemonAtContext(game: BOTCModel, player: string, poisonContext: string): BoolVar {
  if (poisonContext === NIGHT_1) return game.actualIs(player, Imp);
  if (poisonContext === NIGHT_2) return isDemonOnNightTwo(game, player);
  return isDemonOnNightThree(game, player);
}

function isDemonOnNightTwo(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf([game.actualIs(player, Imp), game.actualIs("Dan", Imp).not()], `${player}_starting_imp_n2`),
      player === "Dan" || player === "You"
        ? game.constantBool(false, `${player}_cannot_be_dan_starpass_n2`)
        : game.allOf([game.actualIs("Dan", Imp), game.isMinion(player)], `${player}_dan_starpass_n2`),
    ],
    `${player}_demon_n2`,
  );
}

function isDemonOnNightThree(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf(
        [game.actualIs(player, Imp), game.actualIs("Dan", Imp).not(), game.actualIs("Sula", Imp).not()],
        `${player}_starting_imp_n3`,
      ),
      player === "Dan" || player === "Sula" || player === "You"
        ? game.constantBool(false, `${player}_cannot_be_dan_starpass_n3`)
        : game.allOf([game.actualIs("Dan", Imp), game.isMinion(player)], `${player}_dan_starpass_n3`),
      player === "Dan" || player === "Sula" || player === "You"
        ? game.constantBool(false, `${player}_cannot_be_sw_after_sula_n3`)
        : game.allOf([isDemonOnNightTwo(game, "Sula"), game.actualIs(player, ScarletWoman)], `${player}_sw_after_sula`),
    ],
    `${player}_demon_n3`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-38-snakes-on-a-plane.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_3,
    forcedRoles: [
      forcedRole("Starting Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk),
    ],
  });
