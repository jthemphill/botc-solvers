import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import type { BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Acrobat,
  Balloonist,
  Drunk,
  Gambler,
  Goblin,
  Gossip,
  Imp,
  Juggler,
  Knight,
  Po,
  Steward,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const PLAYERS = [
  new Knight({ name: "Josh", noDemonAmong: ["Fraser", "Oscar"] }),
  new Gambler({ name: "Anna" }),
  new Juggler({
    timing: "night_2",
    name: "Sula",
  }),
  new Steward({ name: "Hannah", goodPlayer: "Oscar" }),
  new Acrobat({ name: "You" }),
  new Balloonist({
    name: "Fraser",
    differentCharacterTypePairs: [
      ["Oscar", "Anna"],
      ["Anna", "You"],
    ],
  }),
  new Gossip({
    timing: "day_1",
    name: "Oscar",
  }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Po,
  Goblin,
  Drunk,
  Acrobat,
  Balloonist,
  Gambler,
  Gossip,
  Juggler,
  Knight,
  Steward,
);
export const DEMON_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Demon });
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);

  applyClaims(game, PLAYERS);
  game.setPossibleActualRoles("You", [Acrobat, Drunk]);

  game.addImplication(game.actualIs("You", Acrobat), game.actualIs("Fraser", Drunk).not());
  game.addImplication(game.actualIs("You", Acrobat), game.actualIs("Josh", Drunk));
  game.addImplication(game.actualIs("Anna", Gambler), game.actualIs("Sula", Goblin));
  game.addImplication(game.actualIs("Anna", Gambler), game.actualIs("You", Drunk).not());

  const poChargeRequiresGossipDeath = game.allOf(
    [game.actualIs("Fraser", Po), game.actualIs("Oscar", Gossip)],
    "po_charge_requires_gossip_death",
  );
  game.addImplication(game.roleInPlay(Po), poChargeRequiresGossipDeath);

  const annaDemonAfterNightTwo = game.anyOf(
    [
      game.isDemon("Anna"),
      game.allOf([game.actualIs("Sula", Imp), game.actualIs("Anna", Goblin)], "anna_demon_after_sula_starpass"),
    ],
    "anna_demon_after_night_two",
  );
  game.addTruth(game.allOf([game.actualIs("Oscar", Gossip), annaDemonAfterNightTwo], "oscar_day_two_gossip_true"));
  game.addTruth(game.allOf([game.actualIs("You", Acrobat), game.actualIs("Josh", Drunk)], "you_dies_from_acrobat"));
  game.addTruth(
    game.anyOf(
      ["Josh", "Anna"].flatMap((startingImp) =>
        ["Hannah", "Fraser", "Oscar"].map((recipient) =>
          game.allOf(
            [game.actualIs(startingImp, Imp), game.actualIs(recipient, Goblin)],
            `${startingImp}_starpasses_to_${recipient}`,
          ),
        ),
      ),
      "night_three_imp_starpass",
    ),
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-09-the-new-acrobat.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Starting Demon", DEMON_ROLES),
      forcedRole("Starting Minion", Goblin, { includeRole: true }),
    ],
  });
