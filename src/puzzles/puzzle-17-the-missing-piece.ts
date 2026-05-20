import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel, type World } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
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
  playerNames,
  script,
} from "../characters";

export const PUZZLEMASTER_DRUNK = "puzzlemaster_drunk";

export const PLAYERS = ["Sarah", "Sula", "Hannah", "Tom", "You", "Adam", "Steph", "Fraser"];
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

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.setCharacterCount(ScarletWoman, 1);
  game.setCharacterCount(Puzzlemaster, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    1,
  );

  addClaim(game, "Sarah", Undertaker);
  addClaim(game, "Sula", Washerwoman);
  addClaim(game, "Hannah", Investigator);
  addClaim(game, "Tom", Slayer);
  addClaim(game, "You", Puzzlemaster);
  addClaim(game, "Adam", Chef);
  addClaim(game, "Steph", Empath);
  addClaim(game, "Fraser", FortuneTeller);
  game.fixActual("You", Puzzlemaster);

  game.allowPoisonInContext(PUZZLEMASTER_DRUNK);
  game.addExactlyN(
    PLAYER_NAMES.filter((player) => player !== "You").map((player) => game.poisoned(player, PUZZLEMASTER_DRUNK)),
    1,
  );
  game.fixPoisoned("You", false, PUZZLEMASTER_DRUNK);

  game.addTruth(demonExistsOnNightTwo(game));
  game.addTruth(demonExistsOnNightThree(game));

  const redHerrings = addFortuneTellerRedHerring(game);
  addPuzzlemasterInfo(
    game,
    "Sarah",
    Undertaker,
    game.allOf([game.actualIs("Steph", Empath), game.actualIs("Sula", Washerwoman)], "sarah_undertaker_info"),
  );
  addPuzzlemasterInfo(
    game,
    "Sula",
    Washerwoman,
    Washerwoman.learnsRoleAmong(game, ["Sarah", "Hannah"], Undertaker, "sula_washerwoman"),
  );
  addPuzzlemasterInfo(
    game,
    "Hannah",
    Investigator,
    Investigator.learnsRoleAmong(game, ["Fraser", "Sarah"], ScarletWoman, "hannah_investigator"),
  );
  addPuzzlemasterInfo(
    game,
    "Tom",
    Slayer,
    game.not(isDemonOnDayThree(game, "Sarah"), "tom_slayer_shot_does_not_kill_sarah"),
  );
  addPuzzlemasterInfo(game, "Adam", Chef, Chef.learnsCount(game, 0, "adam_chef", { registers: false }));
  addPuzzlemasterInfo(
    game,
    "Steph",
    Empath,
    game.allOf([game.isGood("Adam"), game.isGood("Fraser")], "steph_empath_zero"),
  );
  addPuzzlemasterInfo(
    game,
    "Fraser",
    FortuneTeller,
    game.allOf(
      [
        fortuneTellerCheck(game, redHerrings, ["Hannah", "Tom"], 1, false, "fraser_ft_night_1"),
        fortuneTellerCheck(game, redHerrings, ["Tom", "Fraser"], 2, true, "fraser_ft_night_2"),
        fortuneTellerCheck(game, redHerrings, ["You", "Sarah"], 3, true, "fraser_ft_night_3"),
      ],
      "fraser_fortune_teller_info",
    ),
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addClaim(game: BOTCModel, player: string, apparentRole: typeof Puzzlemaster): void;
function addClaim(
  game: BOTCModel,
  player: string,
  apparentRole:
    | typeof Chef
    | typeof Empath
    | typeof FortuneTeller
    | typeof Investigator
    | typeof Slayer
    | typeof Undertaker
    | typeof Washerwoman,
): void;
function addClaim(
  game: BOTCModel,
  player: string,
  apparentRole:
    | typeof Chef
    | typeof Empath
    | typeof FortuneTeller
    | typeof Investigator
    | typeof Puzzlemaster
    | typeof Slayer
    | typeof Undertaker
    | typeof Washerwoman,
): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(
    player,
    apparentRole === Puzzlemaster ? [Puzzlemaster] : [apparentRole, Imp, ScarletWoman],
  );
}

function addPuzzlemasterInfo(
  game: BOTCModel,
  player: string,
  role: Parameters<BOTCModel["actualIs"]>[1],
  info: BoolVar,
): void {
  const active = game.allOf(
    [game.actualIs(player, role), game.poisoned(player, PUZZLEMASTER_DRUNK).not()],
    `${player}_${String(role)}_active_puzzlemaster_info`,
  );
  game.addImplication(active, info);
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
  return candidates.filter((player) => worlds.every((world) => world.isPoisoned(player, PUZZLEMASTER_DRUNK)));
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-17-the-missing-piece.ts")) {
  const worlds = await solve();
  printSolution(worlds, PLAYER_NAMES, {
    poisonContext: PUZZLEMASTER_DRUNK,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", ScarletWoman, { includeRole: true }),
    ],
  });
  console.log(`\nPuzzlemaster drunk target: ${puzzlemasterDrunkTargets(worlds).join(", ") || "not forced"}`);
}
