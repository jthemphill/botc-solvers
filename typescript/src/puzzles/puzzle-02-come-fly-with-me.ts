import { BOTCModel } from "../model";
import { printSolution } from "../display";
import { CharacterType } from "../core";
import {
  Balloonist,
  Clockmaker,
  Drunk,
  FortuneTeller,
  Goblin,
  Investigator,
  Juggler,
  Knight,
  Leviathan,
  Saint,
  Seamstress,
  applyClaims,
  playerNames,
  script,
} from "../characters";
import { roleCharacterType } from "../core";

export const PLAYERS = [
  new Investigator({ name: "Sarah", role: Goblin, among: ["Matthew", "Fraser"] }),
  new Juggler({
    name: "Matthew",
    guesses: { Steph: Knight, Sarah: Leviathan, Anna: Goblin, Sula: Goblin, You: Seamstress },
    correctCount: 2,
  }),
  new Clockmaker({ name: "Anna", demonNextToMinion: true }),
  new Balloonist({
    name: "Sula",
    differentCharacterTypePairs: [
      ["Tim", "Matthew"],
      ["Matthew", "Steph"],
    ],
  }),
  new Seamstress({ name: "You", aligned: true, among: ["Matthew", "Sula"] }),
  new Knight({ name: "Steph", noDemonAmong: ["Tim", "Sula"] }),
  new FortuneTeller({
    name: "Fraser",
    checks: [
      { left: "Sarah", right: "Anna", yes: false },
      { left: "You", right: "Fraser", yes: false },
      { left: "Steph", right: "Sarah", yes: false },
    ],
  }),
  new Saint({ name: "Tim" }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Leviathan,
  Goblin,
  Drunk,
  Saint,
  Balloonist,
  Clockmaker,
  FortuneTeller,
  Investigator,
  Juggler,
  Knight,
  Seamstress,
);

export function buildModel(): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES });
  game.setCharacterCount(Leviathan, 1);
  game.setCharacterCount(Goblin, 1);
  game.fixNotActual("You", Leviathan);
  game.fixNotActual("You", Goblin);
  const outsiderVars = PLAYER_NAMES.flatMap((player) =>
    [...game.characters.entries()]
      .filter(([, character]) => roleCharacterType(character) === CharacterType.Outsider)
      .map(([role]) => game.actualIs(player, role)),
  );
  const balloonistInPlay = game.roleInPlay(Balloonist);
  game.addEnforcedExactlyN(outsiderVars, 1, balloonistInPlay.not());
  game.addEnforcedAtLeastN(outsiderVars, 1, balloonistInPlay);
  game.addEnforcedAtMostN(outsiderVars, 2, balloonistInPlay);
  applyClaims(game, PLAYERS);
  return game;
}

export async function solve() {
  return buildModel().solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-02-come-fly-with-me.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [Goblin, Leviathan, Drunk],
    forcedMissing: "not in every world",
  });
