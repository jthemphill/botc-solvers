import { Alignment, CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { BOTCModel } from "../model";
import {
  Dreamer,
  Drunk,
  Empath,
  FortuneTeller,
  Investigator,
  Juggler,
  Librarian,
  LordOfTyphon,
  Marionette,
  Poisoner,
  Recluse,
  Undertaker,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";
export const PLAYERS = [
  new Librarian({ name: "Sarah", role: Drunk, among: ["You", "Hannah"], registers: false, poisonContext: NIGHT_1 }),
  new Recluse({ name: "Tim" }),
  new Juggler({
    name: "Matt",
    guesses: { You: Investigator, Dan: LordOfTyphon, Tim: Recluse, Hannah: Dreamer },
    correctCount: 1,
    poisonContext: NIGHT_2,
  }),
  new Dreamer({ name: "Hannah", player: "You", roles: [Investigator, LordOfTyphon], poisonContext: NIGHT_1 }),
  new Investigator({
    name: "You",
    role: Marionette,
    among: ["Matt", "Hannah"],
    registers: false,
    poisonContext: NIGHT_1,
  }),
  new Empath({ name: "Anna", count: 2, poisonContext: NIGHT_1 }),
  new Undertaker({ name: "Dan", player: "Anna", role: Empath, poisonContext: NIGHT_2 }),
  new FortuneTeller({
    name: "Fraser",
    checks: [
      { left: "Anna", right: "Tim", yes: true, demonRole: LordOfTyphon, registers: true, poisonContext: NIGHT_1 },
      { left: "You", right: "Fraser", yes: false, demonRole: LordOfTyphon, registers: true, poisonContext: NIGHT_2 },
      { left: "You", right: "Sarah", yes: true, demonRole: LordOfTyphon, registers: true, poisonContext: NIGHT_3 },
    ],
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  LordOfTyphon,
  Marionette,
  Poisoner,
  Drunk,
  Recluse,
  Investigator,
  Librarian,
  FortuneTeller,
  Juggler,
  Dreamer,
  Empath,
  Undertaker,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const EVIL_ROLES = roleNames(CHARACTERS, { alignment: Alignment.Evil });

export function buildModel(): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES });
  for (const role of EVIL_ROLES) game.setCharacterCount(role, 1);
  for (const player of PLAYER_NAMES) {
    const [left, right] = game.neighbors(player);
    game.addImplication(game.actualIs(player, LordOfTyphon), game.isMinion(left));
    game.addImplication(game.actualIs(player, LordOfTyphon), game.isMinion(right));
  }
  for (const deadOrExecuted of ["Anna", "Hannah", "Dan", "Tim"]) game.fixNotActual(deadOrExecuted, LordOfTyphon);
  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.not(game.actualIs("Anna", Poisoner), "anna_is_not_poisoner") });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      ["Anna", "Hannah", "Dan"].map((player) => game.actualIs(player, Poisoner).not()),
      "poisoner_alive_night_3",
    ),
  });
  applyClaims(game, PLAYERS);
  game.setPossibleActualRoles("You", [Investigator, Drunk, Marionette]);
  return game;
}

export async function solve() {
  return buildModel().solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-04-the-many-headed-monster.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_2,
    forcedRoles: [forcedRole("Demon", LordOfTyphon, { includeRole: true })],
  });
