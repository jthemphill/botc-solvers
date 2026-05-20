import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { chefCountRegistersAs } from "../predicates";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Chef,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Librarian,
  Marionette,
  Poisoner,
  Ravenkeeper,
  ScarletWoman,
  Spy,
  Undertaker,
  Washerwoman,
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const MINION_ROLES = [Poisoner, Spy, ScarletWoman, Marionette];
export const PLAYERS = [
  new Librarian({
    name: "Sula",
    role: Drunk,
    among: ["Jasmine", "Steph"],
    poisonContext: NIGHT_1,
  }),
  new FortuneTeller({
    name: "Aoife",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) =>
          game.fortuneTellerYes(
            context as ReadonlyMap<string, BoolVar>,
            ["You", "Jasmine"],
            "aoife_ft_you_jasmine_yes",
            (player) => isDemonAtContext(game, player, NIGHT_1),
          ),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game, context) =>
          game.fortuneTellerNo(
            context as ReadonlyMap<string, BoolVar>,
            ["Jasmine", "Sula"],
            "aoife_ft_jasmine_sula_no",
            (player) => isDemonAtContext(game, player, NIGHT_2),
          ),
      },
    ],
  }),
  new Empath({
    name: "Fraser",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game) => game.registeredEvilCount(["Jasmine", "Aoife"], 1, "fraser_empath_n1"),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game) => game.registeredEvilCount(["Jasmine", "Aoife"], 1, "fraser_empath_n2"),
      },
      {
        poisonContext: NIGHT_3,
        learned: (game) => game.registeredEvilCount(["Jasmine", "Steph"], 1, "fraser_empath_n3"),
      },
    ],
  }),
  new Imp({ name: "Jasmine" }),
  new Undertaker({
    name: "You",
    infoClaims: [
      { poisonContext: NIGHT_2, learned: (game) => game.actualIs("Matt", Spy) },
      { poisonContext: NIGHT_3, learned: (game) => game.actualIs("Aoife", Marionette) },
    ],
  }),
  new Washerwoman({
    name: "Matt",
    role: Undertaker,
    among: ["You", "Fraser"],
    poisonContext: NIGHT_1,
  }),
  new Chef({
    name: "Steph",
    infoClaims: [{ poisonContext: NIGHT_1, learned: (game) => chefCountRegistersAs(game, 1, "steph_chef") }],
  }),
  new Ravenkeeper({
    name: "Adam",
    infoClaims: [
      { poisonContext: NIGHT_2, learned: (game) => game.registersAsRole("Fraser", Empath, "adam_ravenkeeper") },
    ],
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Poisoner,
  Spy,
  ScarletWoman,
  Marionette,
  Drunk,
  Chef,
  Empath,
  FortuneTeller,
  Librarian,
  Ravenkeeper,
  Undertaker,
  Washerwoman,
);
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.addImplication(game.roleInPlay(Marionette), marionetteNeighborsDemon(game));
  for (const evilRole of [Imp, Poisoner, Spy, ScarletWoman]) game.fixNotActual("You", evilRole);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, {
    activeIf: game.allOf(
      [game.actualIs("Matt", Poisoner).not(), game.actualIs("Adam", Poisoner).not()],
      "poisoner_active_night_2",
    ),
  });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [
        game.actualIs("Matt", Poisoner).not(),
        game.actualIs("Adam", Poisoner).not(),
        game.actualIs("Aoife", Poisoner).not(),
        game.actualIs("Sula", Poisoner).not(),
        game.actualIs("Adam", Imp).not(),
        isDemonOnNightThree(game, "Sula").not(),
      ],
      "poisoner_active_night_3",
    ),
  });

  const redHerrings = game.addFortuneTellerRedHerring("Aoife");
  applyClaims(game, PLAYERS, { context: redHerrings });

  game.addTruth(
    game.anyOf(
      PLAYER_NAMES.map((player) => isDemonOnNightTwo(game, player)),
      "night_2_demon_exists_to_kill_adam",
    ),
  );
  game.addTruth(
    game.anyOf(
      PLAYER_NAMES.map((player) => isDemonOnNightThree(game, player)),
      "night_3_demon_exists_to_kill_sula",
    ),
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function marionetteNeighborsDemon(game: BOTCModel): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((player) => {
      const [left, right] = game.neighbors(player);
      return game.allOf(
        [
          game.actualIs(player, Marionette),
          game.anyOf([game.actualIs(left, Imp), game.actualIs(right, Imp)], `${player}_neighbor_imp`),
        ],
        `${player}_marionette_neighbors_imp`,
      );
    }),
    "marionette_neighbors_demon",
  );
}

function isDemonAtContext(game: BOTCModel, player: string, poisonContext: string): BoolVar {
  if (poisonContext === NIGHT_1) return game.actualIs(player, Imp);
  if (poisonContext === NIGHT_2) return isDemonOnNightTwo(game, player);
  return isDemonOnNightThree(game, player);
}

function isDemonOnNightTwo(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf([game.actualIs(player, Imp), game.actualIs("Matt", Imp).not()], `${player}_starting_imp_night_2`),
      player === "Matt"
        ? game.constantBool(false, "matt_dead_before_night_2")
        : game.allOf([game.actualIs("Matt", Imp), game.actualIs(player, ScarletWoman)], `${player}_sw_after_matt`),
    ],
    `${player}_demon_night_2`,
  );
}

function isDemonOnNightThree(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf(
        [
          game.actualIs(player, Imp),
          game.actualIs("Matt", Imp).not(),
          game.actualIs("Adam", Imp).not(),
          game.actualIs("Aoife", Imp).not(),
        ],
        `${player}_starting_imp_night_3`,
      ),
      player === "Matt" || player === "Adam" || player === "Aoife"
        ? game.constantBool(false, `${player}_cannot_be_adam_starpass_night_3`)
        : game.allOf([game.actualIs("Adam", Imp), game.isMinion(player)], `${player}_adam_starpass_night_3`),
      player === "Matt" || player === "Adam" || player === "Aoife"
        ? game.constantBool(false, `${player}_cannot_be_scarlet_woman_night_3`)
        : game.allOf(
            [game.actualIs("Matt", Imp), game.actualIs(player, ScarletWoman)],
            `${player}_sw_after_matt_night_3`,
          ),
      player === "Matt" || player === "Adam" || player === "Aoife"
        ? game.constantBool(false, `${player}_cannot_be_sw_after_aoife_night_3`)
        : game.allOf(
            [isDemonOnNightTwo(game, "Aoife"), game.actualIs(player, ScarletWoman)],
            `${player}_sw_after_aoife`,
          ),
    ],
    `${player}_demon_night_3`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-37-new-super-marionette-bros-u.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_3,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk),
    ],
  });
