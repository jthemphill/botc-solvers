import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Legionary,
  Poisoner,
  Washerwoman,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const PLAYERS = ["Sarah", "Tom", "Aoife", "Hannah", "You", "Fraser", "Adam"];
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

  addClaim(game, "Sarah", Legionary, [Legionary, Imp, Poisoner]);
  addClaim(game, "Tom", FortuneTeller, [FortuneTeller, Imp, Poisoner]);
  addClaim(game, "Aoife", Empath, [Empath, Imp, Poisoner]);
  addClaim(game, "Hannah", Legionary, [Legionary, Imp, Poisoner]);
  addClaim(game, "You", Washerwoman, [Washerwoman]);
  addClaim(game, "Fraser", Legionary, [Legionary, Imp, Poisoner]);
  addClaim(game, "Adam", Investigator, [Investigator, Imp, Poisoner]);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Tom", Poisoner).not() });
  game.fixNotActual("Tom", Imp);

  game.addTruthfulInfoClaim(
    "Tom",
    FortuneTeller,
    FortuneTeller.learnsCheck(game, "You", "Fraser", { yes: false, name: "tom_fortune_teller", demonRole: Imp }),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim("Aoife", Empath, empathAliveNeighborCount(game, ["Tom", "Hannah"], 0, "aoife_empath_n1"), {
    poisonContext: NIGHT_1,
  });
  game.addTruthfulInfoClaim(
    "Aoife",
    Empath,
    empathAliveNeighborCount(game, ["Sarah", "Hannah"], 0, "aoife_empath_n2"),
    {
      poisonContext: NIGHT_2,
    },
  );
  game.addTruthfulInfoClaim(
    "You",
    Washerwoman,
    game.anyOf([game.actualIs("Fraser", Legionary), game.actualIs("Sarah", Legionary)], "you_washerwoman_legionary"),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim(
    "Adam",
    Investigator,
    Investigator.learnsRoleAmong(game, ["Tom", "Aoife"], Poisoner, "adam_investigator"),
    {
      poisonContext: NIGHT_1,
    },
  );

  addLegionaryInfo(game, "Sarah", [1, 2]);
  addLegionaryInfo(game, "Hannah", [2, 2]);
  addLegionaryInfo(game, "Fraser", [2, 1]);

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

function addClaim(game: BOTCModel, player: string, apparentRole: RoleRef, possibleRoles: readonly RoleRef[]): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, possibleRoles);
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

function addLegionaryInfo(game: BOTCModel, player: string, counts: readonly [number, number]): void {
  addLegionaryNightInfo(game, player, NIGHT_1, new Set(PLAYER_NAMES), counts[0]);
  addLegionaryNightInfo(
    game,
    player,
    NIGHT_2,
    new Set(PLAYER_NAMES.filter((candidate) => candidate !== "Tom")),
    counts[1],
  );
}

function addLegionaryNightInfo(
  game: BOTCModel,
  player: string,
  poisonContext: string,
  livingPlayers: ReadonlySet<string>,
  count: number,
): void {
  const active = game.allOf(
    [game.actualIs(player, Legionary), game.poisoned(player, poisonContext).not()],
    `${player}_${poisonContext}_active_legionary`,
  );
  game.addImplication(
    active,
    legionaryLearnsCount(game, player, livingPlayers, count, `${player}_${poisonContext}_legionary_count`),
  );
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
