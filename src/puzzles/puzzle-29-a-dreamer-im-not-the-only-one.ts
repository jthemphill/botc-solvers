import { forcedRole, printSolution } from "../display";
import { BOTCModel } from "../model";
import { type InfoClaim, Dreamer, Drunk, Imp, Poisoner, applyClaims, playerNames, script } from "../characters";
import { KissatBackend, type SatBackend } from "../sat";
import type { RoleRef } from "../core";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const PLAYERS = [
  new Dreamer({
    name: "Sula",
    infoClaims: [
      dreamerInfo("Sula", NIGHT_1, "Jasmine", [Drunk, Poisoner]),
      dreamerInfo("Sula", NIGHT_2, "Hannah", [Drunk, Poisoner]),
    ],
  }),
  new Dreamer({
    name: "Steph",
    infoClaims: [
      dreamerInfo("Steph", NIGHT_1, "Jasmine", [Drunk, Imp]),
      dreamerInfo("Steph", NIGHT_2, "Sula", [Dreamer, Poisoner]),
    ],
  }),
  new Dreamer({
    name: "Hannah",
    infoClaims: [
      dreamerInfo("Hannah", NIGHT_1, "Adam", [Drunk, Poisoner]),
      dreamerInfo("Hannah", NIGHT_2, "Sula", [Drunk, Imp]),
    ],
  }),
  new Dreamer({
    name: "Fraser",
    infoClaims: [
      dreamerInfo("Fraser", NIGHT_1, "Hannah", [Drunk, Imp]),
      dreamerInfo("Fraser", NIGHT_2, "Jasmine", [Drunk, Poisoner]),
    ],
  }),
  new Dreamer({
    name: "You",
    infoClaims: [dreamerInfo("You", NIGHT_1, "Jasmine", [Dreamer, Poisoner])],
  }),
  new Dreamer({
    name: "Jasmine",
    infoClaims: [dreamerInfo("Jasmine", NIGHT_1, "Sula", [Drunk, Imp])],
  }),
  new Dreamer({
    name: "Adam",
    infoClaims: [
      dreamerInfo("Adam", NIGHT_1, "Jasmine", [Dreamer, Imp]),
      dreamerInfo("Adam", NIGHT_2, "Fraser", [Dreamer, Imp]),
    ],
  }),
  new Dreamer({
    name: "Sarah",
    infoClaims: [
      dreamerInfo("Sarah", NIGHT_1, "Jasmine", [Drunk, Poisoner]),
      dreamerInfo("Sarah", NIGHT_2, "Adam", [Drunk, Imp]),
    ],
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(Imp, Poisoner, Drunk, Dreamer);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, {
    characters: CHARACTERS,
    seating: PLAYER_NAMES,
    uniqueCharacters: false,
    backend,
  });
  game.setCharacterCount(Imp, 1);
  game.setCharacterCount(Poisoner, 1);
  game.setCharacterCount(Drunk, 1);
  game.addEnforcedExactlyN(
    PLAYER_NAMES.map((player) => game.actualIs(player, Dreamer)),
    5,
    game.constantBool(true, "five_dreamers"),
  );

  game.fixNotActual("Jasmine", Imp);
  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Jasmine", Poisoner).not() });

  applyClaims(game, PLAYERS);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function dreamerInfo(
  player: string,
  poisonContext: string,
  target: string,
  roles: readonly [RoleRef, RoleRef],
): InfoClaim {
  return {
    poisonContext,
    learned: (game) => Dreamer.learnsOneOf(game, target, roles, `${player}_${poisonContext}_dreamer`),
  };
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-29-a-dreamer-im-not-the-only-one.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", Poisoner, { includeRole: true }),
      forcedRole("Outsider", Drunk, { includeRole: true }),
    ],
  });
