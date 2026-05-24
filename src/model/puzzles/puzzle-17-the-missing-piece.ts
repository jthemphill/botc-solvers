import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel, type World } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  type AppliedInfoClaim,
  Chef,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Puzzlemaster,
  ScarletWoman,
  Slayer,
  Undertaker,
  Washerwoman,
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const PLAYERS = [
  new Undertaker({
    name: "Sarah",
    timing: "night_2",
    infoClaims: [
      (game) =>
        game.allOf([game.actualIs("Steph", Empath), game.actualIs("Sula", Washerwoman)], "sarah_undertaker_info"),
    ],
  }),
  new Washerwoman({
    name: "Sula",
    role: Undertaker,
    among: ["Sarah", "Hannah"],
  }),
  new Investigator({
    name: "Hannah",
    role: ScarletWoman,
    among: ["Fraser", "Sarah"],
  }),
  new Slayer({
    name: "Tom",
    timing: "day_3",
    infoClaims: [(game) => game.not(isDemonOnDayThree(game, "Sarah"), "tom_slayer_shot_does_not_kill_sarah")],
  }),
  new Puzzlemaster({ name: "You" }),
  new Chef({
    name: "Adam",
    count: 0,
    registers: false,
  }),
  new Empath({
    name: "Steph",
    infoClaims: [(game) => game.allOf([game.isGood("Adam"), game.isGood("Fraser")], "steph_empath_zero")],
  }),
  new FortuneTeller({
    name: "Fraser",
    infoClaims: [
      (game, context) => {
        const redHerrings = context as RedHerring;
        return game.allOf(
          [
            fortuneTellerCheck(game, redHerrings, ["Hannah", "Tom"], 1, false, "fraser_ft_night_1"),
            fortuneTellerCheck(game, redHerrings, ["Tom", "Fraser"], 2, true, "fraser_ft_night_2"),
            fortuneTellerCheck(game, redHerrings, ["You", "Sarah"], 3, true, "fraser_ft_night_3"),
          ],
          "fraser_fortune_teller_info",
        );
      },
    ],
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  ScarletWoman,
  Puzzlemaster,
  Chef,
  Empath,
  FortuneTeller,
  Investigator,
  Slayer,
  Undertaker,
  Washerwoman,
);

type RedHerring = ReadonlyMap<string, BoolVar>;
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);

  game.addPuzzlemasterDrunking({ excludedPlayers: ["You"] });

  game.addTruth(demonExistsOnNightTwo(game));
  game.addTruth(demonExistsOnNightThree(game));

  const redHerrings = addFortuneTellerRedHerring(game);
  applyClaims(game, PLAYERS, { info: addPuzzlemasterInfo, context: redHerrings });
  game.fixActual("You", Puzzlemaster);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addPuzzlemasterInfo(game: BOTCModel, claim: AppliedInfoClaim): void {
  const active = game.allOf(
    [game.actualIs(claim.player, claim.role), game.globalDrunk(claim.player).not()],
    `${claim.player}_active_puzzlemaster_info`,
  );
  game.addImplication(active, claim.learned);
}

function addFortuneTellerRedHerring(game: BOTCModel): RedHerring {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Fraser", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerCheck(
  game: BOTCModel,
  redHerrings: RedHerring,
  players: readonly [string, string],
  night: 1 | 2 | 3,
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

function demonExistsOnNightTwo(game: BOTCModel): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((player) => isDemonAtNight(game, 2, player)),
    "demon_exists_night_2",
  );
}

function demonExistsOnNightThree(game: BOTCModel): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((player) => isDemonAtNight(game, 3, player)),
    "demon_exists_night_3",
  );
}

function isDemonAtNight(game: BOTCModel, night: 1 | 2 | 3, player: string): BoolVar {
  if (night === 1) return game.actualIs(player, Imp);
  if (night === 2) {
    return game.anyOf(
      [
        player === "Steph" ? game.constantBool(false, `${player}_executed_before_night_2`) : game.actualIs(player, Imp),
        game.allOf([game.actualIs("Steph", Imp), game.actualIs(player, ScarletWoman)], `${player}_sw_after_steph`),
      ],
      `${player}_demon_night_2`,
    );
  }
  return game.anyOf(
    [
      ["Steph", "Adam", "Sula"].includes(player)
        ? game.constantBool(false, `${player}_dead_before_night_3`)
        : game.actualIs(player, Imp),
      game.allOf(
        [
          game.actualIs("Steph", Imp),
          game.actualIs(player, ScarletWoman),
          player === "Adam" || player === "Sula"
            ? game.constantBool(false, `${player}_sw_dead_before_night_3_from_steph`)
            : game.constantBool(true, `${player}_sw_alive_night_3_from_steph`),
        ],
        `${player}_sw_after_steph_night_3`,
      ),
      game.allOf(
        [
          game.actualIs("Adam", Imp),
          game.actualIs(player, ScarletWoman),
          player === "Steph" || player === "Sula"
            ? game.constantBool(false, `${player}_sw_dead_before_night_3_from_adam`)
            : game.constantBool(true, `${player}_sw_alive_night_3_from_adam`),
        ],
        `${player}_sw_after_adam_night_3`,
      ),
      game.allOf(
        [
          game.actualIs("Sula", Imp),
          game.actualIs(player, ScarletWoman),
          ["Steph", "Adam", "Sula"].includes(player)
            ? game.constantBool(false, `${player}_sw_dead_before_night_3_from_sula`)
            : game.constantBool(true, `${player}_sw_alive_night_3_from_sula`),
        ],
        `${player}_sw_after_sula_night_3`,
      ),
    ],
    `${player}_demon_night_3`,
  );
}

function isDemonOnDayThree(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      player === "Hannah" ? game.constantBool(false, "hannah_dead_before_day_3") : isDemonAtNight(game, 3, player),
      game.allOf(
        [
          game.actualIs("Hannah", Imp),
          game.actualIs(player, ScarletWoman),
          ["Steph", "Adam", "Sula", "Hannah"].includes(player)
            ? game.constantBool(false, `${player}_sw_dead_before_day_3`)
            : game.constantBool(true, `${player}_sw_alive_day_3`),
        ],
        `${player}_sw_after_hannah_night_3`,
      ),
    ],
    `${player}_demon_day_3`,
  );
}

export function puzzlemasterDrunkTargets(worlds: readonly World[]): string[] {
  const candidates = PLAYER_NAMES.filter((player) => player !== "You");
  return candidates.filter((player) => worlds.every((world) => world.isDrunk(player)));
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-17-the-missing-piece.ts")) {
  const worlds = await solve();
  printSolution(worlds, PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", ScarletWoman, { includeRole: true }),
    ],
  });
  console.log(`\nPuzzlemaster drunk target: ${puzzlemasterDrunkTargets(worlds).join(", ") || "not forced"}`);
}
