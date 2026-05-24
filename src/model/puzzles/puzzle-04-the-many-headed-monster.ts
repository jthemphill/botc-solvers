import { night } from "../model";
import { Alignment, CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
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

export const NIGHT_1 = night(1);
export const NIGHT_2 = night(2);
export const NIGHT_3 = night(3);
export const PLAYERS = [
  new Librarian({
    name: "Sarah",
    role: Drunk,
    among: ["You", "Hannah"],
    registers: false,
    timing: "night_1",
  }),
  new Recluse({ name: "Tim" }),
  new Juggler({
    name: "Matt",
    guesses: { You: Investigator, Dan: LordOfTyphon, Tim: Recluse, Hannah: Dreamer },
    correctCount: 1,
    timing: "night_2",
  }),
  new Dreamer({
    name: "Hannah",
    player: "You",
    roles: [Investigator, LordOfTyphon],
    timing: "night_1",
  }),
  new Investigator({
    name: "You",
    role: Marionette,
    among: ["Matt", "Hannah"],
    registers: false,
    timing: "night_1",
  }),
  new Empath({ name: "Anna", count: 2, timing: "night_1" }),
  new Undertaker({ name: "Dan", player: "Anna", role: Empath, timing: "night_2" }),
  new FortuneTeller({
    name: "Fraser",
    checks: [
      {
        left: "Anna",
        right: "Tim",
        yes: true,
        demonRole: LordOfTyphon,
        registers: true,
        timing: "night_1",
      },
      {
        left: "You",
        right: "Fraser",
        yes: false,
        demonRole: LordOfTyphon,
        registers: true,
        timing: "night_2",
      },
      {
        left: "You",
        right: "Sarah",
        yes: true,
        demonRole: LordOfTyphon,
        registers: true,
        timing: "night_3",
      },
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

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
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
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-04-the-many-headed-monster.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: "night_2",
    forcedRoles: [forcedRole("Demon", LordOfTyphon, { includeRole: true })],
  });
