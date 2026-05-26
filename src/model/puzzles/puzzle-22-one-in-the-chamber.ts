import { night, type Timing } from "../model";
import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Baron,
  Chambermaid,
  Drunk,
  Imp,
  Investigator,
  Librarian,
  Poisoner,
  Ravenkeeper,
  Recluse,
  Saint,
  ScarletWoman,
  Slayer,
  Spy,
  Washerwoman,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = night(1);
export const NIGHT_2 = night(2);
export const NIGHT_3 = night(3);

export const PLAYERS = [
  new Saint({ name: "Tim" }),
  new Recluse({ name: "Fraser" }),
  new Librarian({ name: "Oscar", role: Drunk, among: ["You", "Sarah"], timing: "night_1" }),
  new Washerwoman({ name: "Steph", role: Chambermaid, among: ["You", "Aoife"], timing: "night_1" }),
  new Chambermaid({
    name: "You",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) => chambermaidInfo(game, NIGHT_1, ["Anna", "Steph"], 2),
      },
      { timing: "night_2", learned: (game) => chambermaidInfo(game, NIGHT_2, ["Tim", "Steph"], 0) },
      { timing: "night_3", learned: (game) => chambermaidInfo(game, NIGHT_3, ["Tim", "Steph"], 1) },
    ],
  }),
  new Investigator({ name: "Anna", role: Baron, among: ["Aoife", "Steph"], timing: "night_1" }),
  new Slayer({
    timing: "day_1",
    name: "Aoife",
    infoClaims: [{ timing: "night_3", learned: (game) => isDemonOnDayThree(game, "Tim").not() }],
  }),
  new Ravenkeeper({
    timing: "night_2",
    name: "Sarah",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => game.registersAsRole("Steph", Washerwoman, "sarah_ravenkeeper"),
      },
    ],
  }),
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
  Chambermaid,
  Investigator,
  Librarian,
  Ravenkeeper,
  Slayer,
  Washerwoman,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  for (const evilRole of [Imp, Baron, Poisoner, ScarletWoman, Spy]) game.fixNotActual("You", evilRole);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, {
    activeIf: game.allOf(
      [
        game.actualIs("Oscar", Poisoner).not(),
        game.actualIs("Sarah", Poisoner).not(),
        game.actualIs("Sarah", Imp).not(),
      ],
      "night_2_poisoner_still_active",
    ),
  });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [
        game.actualIs("Oscar", Poisoner).not(),
        game.actualIs("Sarah", Poisoner).not(),
        game.actualIs("Fraser", Poisoner).not(),
        game.actualIs("Anna", Poisoner).not(),
        game.actualIs("Sarah", Imp).not(),
        game.actualIs("Anna", Imp).not(),
      ],
      "night_3_poisoner_still_active",
    ),
  });

  applyClaims(game, PLAYERS);
  game.addTruth(demonExistsAtNight(game, 2));
  game.addTruth(demonExistsAtNight(game, 3));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function chambermaidInfo(game: BOTCModel, timing: Timing, players: readonly [string, string], count: number): BoolVar {
  return game.boolSumEquals(
    players.map((player) => wokeDueToAbility(game, player, timing)),
    count,
    `you_chambermaid_${timing}`,
  );
}

function wokeDueToAbility(game: BOTCModel, player: string, timing: Timing): BoolVar {
  if (timing === NIGHT_1) {
    return game.anyOf(
      [
        ...[Investigator, Librarian, Washerwoman, Chambermaid, Poisoner, Spy].map((role) =>
          game.actualIs(player, role),
        ),
        game.allOf([game.actualIs(player, Drunk), drunkApparentRoleWakes(player, 1, game)], `${player}_drunk_wakes_n1`),
      ],
      `${player}_woke_n1`,
    );
  }
  const nightNumber = timing === NIGHT_2 ? 2 : 3;
  return game.anyOf(
    [
      isDemonAtNight(game, nightNumber, player),
      game.actualIs(player, Poisoner),
      game.actualIs(player, Spy),
      game.actualIs(player, Chambermaid),
      game.allOf(
        [game.actualIs(player, ScarletWoman), scarletWomanWakesDueToOwnAbility(game, nightNumber, player)],
        `${player}_scarlet_woman_wakes_n${nightNumber}`,
      ),
      game.allOf(
        [game.actualIs(player, Drunk), drunkApparentRoleWakes(player, nightNumber, game)],
        `${player}_drunk_wakes_n${nightNumber}`,
      ),
    ],
    `${player}_woke_n${nightNumber}`,
  );
}

function drunkApparentRoleWakes(player: string, night: number, game: BOTCModel): BoolVar {
  const wakes =
    player === "You" ? true : night === 1 && (player === "Anna" || player === "Oscar" || player === "Steph");
  return game.constantBool(wakes, `${player}_drunk_apparent_wakes_n${night}`);
}

function demonExistsAtNight(game: BOTCModel, night: 2 | 3): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((player) => isDemonAtNight(game, night, player)),
    `demon_exists_night_${night}`,
  );
}

function isDemonAtNight(game: BOTCModel, night: 2 | 3, player: string): BoolVar {
  if (night === 2) {
    return game.anyOf(
      [
        player === "Oscar" ? game.constantBool(false, `${player}_executed_before_n2`) : game.actualIs(player, Imp),
        game.allOf([game.actualIs("Oscar", Imp), game.actualIs(player, ScarletWoman)], `${player}_sw_after_oscar`),
      ],
      `${player}_demon_n2`,
    );
  }

  return game.anyOf(
    [
      ["Oscar", "Sarah", "Fraser"].includes(player)
        ? game.constantBool(false, `${player}_dead_before_n3`)
        : game.actualIs(player, Imp),
      game.allOf(
        [
          game.actualIs("Oscar", Imp),
          game.actualIs(player, ScarletWoman),
          ["Sarah", "Fraser"].includes(player)
            ? game.constantBool(false, `${player}_sw_dead_before_n3_from_oscar`)
            : game.constantBool(true, `${player}_sw_alive_n3_from_oscar`),
        ],
        `${player}_sw_after_oscar_n3`,
      ),
      game.allOf(
        [
          game.actualIs("Sarah", Imp),
          game.isMinion(player),
          ["Oscar", "Sarah", "Fraser"].includes(player)
            ? game.constantBool(false, `${player}_minion_dead_before_n3_from_sarah`)
            : game.constantBool(true, `${player}_minion_alive_n3_from_sarah`),
        ],
        `${player}_starpass_after_sarah_n3`,
      ),
      game.allOf(
        [
          game.actualIs("Fraser", Imp),
          game.actualIs(player, ScarletWoman),
          ["Oscar", "Sarah", "Fraser"].includes(player)
            ? game.constantBool(false, `${player}_sw_dead_before_n3_from_fraser`)
            : game.constantBool(true, `${player}_sw_alive_n3_from_fraser`),
        ],
        `${player}_sw_after_fraser_n3`,
      ),
    ],
    `${player}_demon_n3`,
  );
}

function scarletWomanWakesDueToOwnAbility(game: BOTCModel, night: 2 | 3, player: string): BoolVar {
  if (night === 2) return game.actualIs("Oscar", Imp);
  return game.anyOf([game.actualIs("Oscar", Imp), game.actualIs("Fraser", Imp)], `${player}_sw_wakes_n3`);
}

function isDemonOnDayThree(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      player === "Anna" ? game.constantBool(false, "anna_dead_before_day_3") : isDemonAtNight(game, 3, player),
      game.allOf(
        [
          game.actualIs("Anna", Imp),
          game.isMinion(player),
          ["Oscar", "Sarah", "Fraser", "Anna"].includes(player)
            ? game.constantBool(false, `${player}_minion_dead_before_day_3_from_anna`)
            : game.constantBool(true, `${player}_minion_alive_day_3_from_anna`),
        ],
        `${player}_starpass_after_anna_day_3`,
      ),
    ],
    `${player}_demon_day_3`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-22-one-in-the-chamber.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: "night_3",
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Outsider", Drunk, { includeRole: true }),
    ],
  });
