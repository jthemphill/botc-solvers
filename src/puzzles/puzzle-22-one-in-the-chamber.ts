import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
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

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const PLAYERS = [
  new Saint({ name: "Tim" }),
  new Recluse({ name: "Fraser" }),
  new Librarian({ name: "Oscar", role: Drunk, among: ["You", "Sarah"], poisonContext: NIGHT_1 }),
  new Washerwoman({ name: "Steph", role: Chambermaid, among: ["You", "Aoife"], poisonContext: NIGHT_1 }),
  new Chambermaid({
    name: "You",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => chambermaidInfo(game, NIGHT_1, ["Anna", "Steph"], 2) },
      { poisonContext: NIGHT_2, learned: (game) => chambermaidInfo(game, NIGHT_2, ["Tim", "Steph"], 0) },
      { poisonContext: NIGHT_3, learned: (game) => chambermaidInfo(game, NIGHT_3, ["Tim", "Steph"], 1) },
    ],
  }),
  new Investigator({ name: "Anna", role: Baron, among: ["Aoife", "Steph"], poisonContext: NIGHT_1 }),
  new Slayer({
    name: "Aoife",
    infoClaims: [{ poisonContext: NIGHT_3, learned: (game) => isDemonOnDayThree(game, "Tim").not() }],
  }),
  new Ravenkeeper({
    name: "Sarah",
    infoClaims: [
      { poisonContext: NIGHT_2, learned: (game) => game.registersAsRole("Steph", Washerwoman, "sarah_ravenkeeper") },
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

function chambermaidInfo(
  game: BOTCModel,
  poisonContext: string,
  players: readonly [string, string],
  count: number,
): BoolVar {
  return game.boolSumEquals(
    players.map((player) => wokeDueToAbility(game, player, poisonContext)),
    count,
    `you_chambermaid_${poisonContext}`,
  );
}

function wokeDueToAbility(game: BOTCModel, player: string, night: string): BoolVar {
  if (night === NIGHT_1) {
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
  const nightNumber = night === NIGHT_2 ? 2 : 3;
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
    poisonContext: NIGHT_3,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Outsider", Drunk, { includeRole: true }),
    ],
  });
