import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Baron,
  Drunk,
  Empath,
  Imp,
  Librarian,
  Poisoner,
  Ravenkeeper,
  Recluse,
  Saint,
  ScarletWoman,
  Slayer,
  Spy,
  Undertaker,
  Washerwoman,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const PLAYERS = [
  new Undertaker({
    name: "Olivia",
    infoClaims: [{ poisonContext: NIGHT_2, learned: (game) => game.actualIs("You", Baron) }],
  }),
  new Ravenkeeper({
    name: "Matt",
    infoClaims: [
      { poisonContext: NIGHT_2, learned: (game) => game.registersAsRole("Fraser", Saint, "matt_ravenkeeper") },
    ],
  }),
  new Washerwoman({ name: "Sula", role: Undertaker, among: ["Fraser", "Olivia"], poisonContext: NIGHT_1 }),
  new Empath({
    name: "Aoife",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game) => empathAliveNeighborCount(game, ["You", "Sula"], 0, "aoife_empath_night_1"),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game) => empathAliveNeighborCount(game, ["Fraser", "Sula"], 1, "aoife_empath_night_2"),
      },
    ],
  }),
  new Librarian({
    name: "You",
    role: Drunk,
    among: ["Fraser", "Matt"],
    poisonContext: NIGHT_1,
  }),
  new Saint({ name: "Fraser" }),
  new Recluse({ name: "Oscar" }),
  new Slayer({ name: "Jasmine" }),
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
  Empath,
  Librarian,
  Ravenkeeper,
  Slayer,
  Undertaker,
  Washerwoman,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  for (const evilRole of [Imp, Baron, Poisoner, ScarletWoman, Spy]) game.fixNotActual("You", evilRole);

  game.addPoisonerEffect(NIGHT_1);
  addNightTwoPoisonerEffect(game);

  applyClaims(game, PLAYERS);

  const soberSlayer = game.allOf(
    [game.actualIs("Jasmine", Slayer), game.poisoned("Jasmine", NIGHT_2).not()],
    "jasmine_sober_slayer_day_2",
  );
  game.addTruth(soberSlayer);
  game.addTruth(oscarCanDieToSlayer(game));
  game.addImplication(game.actualIs("Oscar", Imp), scarletWomanAliveAfterOscarShot(game));

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
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

function addNightTwoPoisonerEffect(game: BOTCModel): void {
  game.allowPoisonInContext(NIGHT_2);
  const poisoned = PLAYER_NAMES.map((player) => game.poisoned(player, NIGHT_2));
  const poisonerStillActiveForInfo = game.allOf(
    [game.roleInPlay(Poisoner), game.actualIs("Matt", Poisoner).not(), game.actualIs("Matt", Imp).not()],
    "night_2_poisoner_still_active_for_info",
  );
  game.addEnforcedExactlyN(poisoned, 1, poisonerStillActiveForInfo);
  game.addEnforcedExactlyN(poisoned, 0, poisonerStillActiveForInfo.not());
}

function oscarCanDieToSlayer(game: BOTCModel): BoolVar {
  return game.anyOf(
    [
      game.actualIs("Oscar", Imp),
      game.allOf(
        [game.actualIs("Oscar", Recluse), game.poisoned("Oscar", NIGHT_2).not()],
        "oscar_sober_recluse_registers_imp",
      ),
    ],
    "oscar_can_die_to_slayer",
  );
}

function scarletWomanAliveAfterOscarShot(game: BOTCModel): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.filter((player) => !["You", "Matt", "Oscar"].includes(player)).map((player) =>
      game.actualIs(player, ScarletWoman),
    ),
    "scarlet_woman_alive_after_oscar_shot",
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-19-he-could-be-you-he-could-be-me.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_2,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
