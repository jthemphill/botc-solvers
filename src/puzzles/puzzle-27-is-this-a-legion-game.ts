import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  type InfoClaim,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Legionary,
  Poisoner,
  Washerwoman,
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const PLAYERS = [
  new Legionary({
    name: "Sarah",
    infoClaims: legionaryInfo("Sarah", [1, 2]),
  }),
  new FortuneTeller({
    name: "Tom",
    checks: [
      { left: "You", right: "Fraser", yes: false, name: "tom_fortune_teller", demonRole: Imp, poisonContext: NIGHT_1 },
    ],
  }),
  new Empath({
    name: "Aoife",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game) => empathAliveNeighborCount(game, ["Tom", "Hannah"], 0, "aoife_empath_n1"),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game) => empathAliveNeighborCount(game, ["Sarah", "Hannah"], 0, "aoife_empath_n2"),
      },
    ],
  }),
  new Legionary({
    name: "Hannah",
    infoClaims: legionaryInfo("Hannah", [2, 2]),
  }),
  new Washerwoman({
    name: "You",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game) =>
          game.anyOf(
            [game.actualIs("Fraser", Legionary), game.actualIs("Sarah", Legionary)],
            "you_washerwoman_legionary",
          ),
      },
    ],
  }),
  new Legionary({
    name: "Fraser",
    infoClaims: legionaryInfo("Fraser", [2, 1]),
  }),
  new Investigator({
    name: "Adam",
    role: Poisoner,
    among: ["Tom", "Aoife"],
    poisonContext: NIGHT_1,
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(Imp, Poisoner, Empath, FortuneTeller, Investigator, Legionary, Washerwoman);
export const LEGIONARY_CLAIMANTS = ["Sarah", "Hannah", "Fraser"];

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, {
    characters: CHARACTERS,
    seating: PLAYER_NAMES,
    uniqueCharacters: false,
    backend,
  });
  enforceUniqueRolesExceptLegionary(game);
  game.setCharacterCount(Imp, 1);
  game.setCharacterCount(Poisoner, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    0,
  );

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Tom", Poisoner).not() });
  game.fixNotActual("Tom", Imp);
  applyClaims(game, PLAYERS);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function enforceUniqueRolesExceptLegionary(game: BOTCModel): void {
  const always = game.constantBool(true, "unique_non_legionary_roles");
  for (const role of [Imp, Poisoner, Empath, FortuneTeller, Investigator, Washerwoman]) {
    game.addEnforcedAtMostN(
      PLAYER_NAMES.map((player) => game.actualIs(player, role)),
      1,
      always,
    );
  }
  game.addEnforcedAtLeastN(
    LEGIONARY_CLAIMANTS.map((player) => game.actualIs(player, Legionary)),
    1,
    always,
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

function legionaryInfo(player: string, counts: readonly [number, number]): readonly InfoClaim[] {
  return [
    {
      poisonContext: NIGHT_1,
      learned: (game) =>
        legionaryLearnsCount(game, player, new Set(PLAYER_NAMES), counts[0], `${player}_${NIGHT_1}_legionary_count`),
    },
    {
      poisonContext: NIGHT_2,
      learned: (game) =>
        legionaryLearnsCount(
          game,
          player,
          new Set(PLAYER_NAMES.filter((candidate) => candidate !== "Tom")),
          counts[1],
          `${player}_${NIGHT_2}_legionary_count`,
        ),
    },
  ];
}

function legionaryLearnsCount(
  game: BOTCModel,
  player: string,
  livingPlayers: ReadonlySet<string>,
  count: number,
  name: string,
): BoolVar {
  return game.anyOf(
    clockwisePlayersAfter(player)
      .filter((candidate) => livingPlayers.has(candidate))
      .map((nextLegionary) => {
        const between = clockwiseBetween(player, nextLegionary).filter((candidate) => livingPlayers.has(candidate));
        const closerLivingPlayers = clockwiseBetween(player, nextLegionary).filter((candidate) =>
          livingPlayers.has(candidate),
        );
        return game.allOf(
          [
            game.actualIs(nextLegionary, Legionary),
            ...closerLivingPlayers.map((candidate) => game.actualIs(candidate, Legionary).not()),
            game.boolSumEquals(
              between.map((candidate) => game.isEvil(candidate)),
              count,
              `${name}_${nextLegionary}_evil_count`,
            ),
          ],
          `${name}_next_${nextLegionary}`,
        );
      }),
    name,
  );
}

function clockwisePlayersAfter(player: string): string[] {
  const start = PLAYER_NAMES.indexOf(player);
  return Array.from(
    { length: PLAYER_NAMES.length - 1 },
    (_ignored, offset) => PLAYER_NAMES[(start + offset + 1) % PLAYER_NAMES.length] as string,
  );
}

function clockwiseBetween(player: string, target: string): string[] {
  const result: string[] = [];
  for (const candidate of clockwisePlayersAfter(player)) {
    if (candidate === target) return result;
    result.push(candidate);
  }
  return result;
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-27-is-this-a-legion-game.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_2,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", Poisoner, { includeRole: true }),
    ],
  });
