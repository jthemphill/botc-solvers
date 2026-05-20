import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Baron,
  Chef,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Nightwatchman,
  Poisoner,
  Recluse,
  Saint,
  ScarletWoman,
  Spy,
  Washerwoman,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const PLAYERS = [
  new Recluse({ name: "Oscar" }),
  new Washerwoman({ name: "Hannah", role: Chef, among: ["Oscar", "Tim"], poisonContext: NIGHT_1 }),
  new Investigator({ name: "Sarah", role: Poisoner, among: ["Olivia", "Hannah"], poisonContext: NIGHT_1 }),
  new Chef({ name: "Tim", count: 1, poisonContext: NIGHT_1 }),
  new Saint({ name: "You" }),
  new Empath({ name: "Olivia" }),
  new FortuneTeller({
    name: "Jasmine",
    checks: [
      { left: "Hannah", right: "Tim", yes: false, demonRole: Imp, registers: true, poisonContext: NIGHT_1 },
      { left: "Olivia", right: "Tim", yes: false, demonRole: Imp, registers: true, poisonContext: NIGHT_2 },
      { left: "Sarah", right: "Jasmine", yes: false, demonRole: Imp, registers: true, poisonContext: NIGHT_3 },
    ],
  }),
  new Nightwatchman({ name: "Fraser" }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Baron,
  Poisoner,
  ScarletWoman,
  Spy,
  Drunk,
  Recluse,
  Saint,
  Chef,
  Empath,
  FortuneTeller,
  Investigator,
  Nightwatchman,
  Washerwoman,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );

  const outsiderCount = PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider));
  game.addEnforcedExactlyN(outsiderCount, 3, game.roleInPlay(Baron));
  game.addEnforcedExactlyN(outsiderCount, 1, game.roleInPlay(Baron).not());

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Hannah", Poisoner).not() });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [game.actualIs("Hannah", Poisoner).not(), game.actualIs("Fraser", Poisoner).not()],
      "poisoner_alive_night_3",
    ),
  });

  applyClaims(game, PLAYERS);
  game.fixActual("You", Saint);
  game.addTruth(demonCanKillAfterDayOne(game));
  game.addTruth(demonCanKillAfterDayTwo(game));

  game.addTruthfulInfoClaim(
    "Olivia",
    Empath,
    empathAliveNeighborCount(game, ["You", "Jasmine"], 0, "olivia_empath_night_1"),
    {
      poisonContext: NIGHT_1,
    },
  );
  game.addTruthfulInfoClaim(
    "Olivia",
    Empath,
    empathAliveNeighborCount(game, ["Tim", "Jasmine"], 1, "olivia_empath_night_2"),
    {
      poisonContext: NIGHT_2,
    },
  );

  game.addImplication(activeNightwatchman(game), game.isEvil("Tim"));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function activeNightwatchman(game: BOTCModel): BoolVar {
  return game.allOf(
    [game.actualIs("Fraser", Nightwatchman), game.poisoned("Fraser", NIGHT_1).not()],
    "fraser_active_nightwatchman",
  );
}

function demonCanKillAfterDayOne(game: BOTCModel): BoolVar {
  return game.anyOf(
    [
      roleAliveAfter(game, Imp, ["Hannah"], "imp_alive_after_day_1"),
      game.allOf(
        [
          game.actualIs("Hannah", Imp),
          roleAliveAfter(game, ScarletWoman, ["Hannah"], "scarlet_woman_alive_after_day_1"),
        ],
        "scarlet_woman_replaces_hannah",
      ),
    ],
    "demon_can_kill_after_day_1",
  );
}

function demonCanKillAfterDayTwo(game: BOTCModel): BoolVar {
  return game.anyOf(
    [
      roleAliveAfter(game, Imp, ["Hannah", "Fraser"], "imp_alive_after_day_2"),
      game.allOf(
        [
          game.anyOf([game.actualIs("Hannah", Imp), game.actualIs("Fraser", Imp)], "imp_died_by_day_2"),
          roleAliveAfter(game, ScarletWoman, ["Hannah", "Fraser"], "scarlet_woman_alive_after_day_2"),
        ],
        "scarlet_woman_replaces_by_day_2",
      ),
    ],
    "demon_can_kill_after_day_2",
  );
}

function roleAliveAfter(
  game: BOTCModel,
  role: typeof Imp | typeof ScarletWoman,
  deadPlayers: readonly string[],
  name: string,
): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.filter((player) => !deadPlayers.includes(player)).map((player) => game.actualIs(player, role)),
    name,
  );
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

if (import.meta.main && process.argv[1]?.endsWith("puzzle-16-who-watches-the-watchmen.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_2,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
