import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { BOTCModel } from "../model";
import {
  Baron,
  Chef,
  Drunk,
  Empath,
  Imp,
  Investigator,
  Librarian,
  Poisoner,
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

export const PLAYERS = [
  new Chef({ name: "Dan", count: 0 }),
  new Recluse({ name: "Anna" }),
  new Washerwoman({ name: "Matt", role: Librarian, among: ["Tim", "Dan"] }),
  new Empath({ name: "Fraser", count: 0 }),
  new Slayer({ name: "You" }),
  new Librarian({ name: "Tim", role: Drunk, among: ["You", "Hannah"] }),
  new Investigator({ name: "Sarah", role: ScarletWoman, among: ["Tim", "Fraser"] }),
  new Saint({ name: "Hannah" }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Baron,
  Spy,
  Poisoner,
  ScarletWoman,
  Drunk,
  Recluse,
  Saint,
  Chef,
  Empath,
  Investigator,
  Librarian,
  Slayer,
  Washerwoman,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const POISON_CONTEXT = "day_1";

export function buildModel(): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.addFalse(game.isEvil("You"));
  const outsiderCount = PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider));
  const baronInPlay = game.roleInPlay(Baron);
  game.addEnforcedExactlyN(outsiderCount, 3, baronInPlay);
  game.addEnforcedExactlyN(outsiderCount, 1, baronInPlay.not());
  game.addPoisonerEffect(POISON_CONTEXT);
  applyClaims(game, PLAYERS, { poisonContext: POISON_CONTEXT });
  game.addTruth(game.actualIs("You", Slayer));
  game.addFalse(game.poisoned("You", POISON_CONTEXT));
  const annaImpWithScarletWoman = game.allOf(
    [game.actualIs("Anna", Imp), game.roleInPlay(ScarletWoman)],
    "anna_imp_with_scarlet_woman",
  );
  const annaRecluseRegistersAsImp = game.allOf(
    [game.actualIs("Anna", Recluse), game.registersAsRole("Anna", Imp, "you_slayer")],
    "anna_recluse_registers_as_imp",
  );
  game.addTruth(
    game.anyOf([annaRecluseRegistersAsImp, annaImpWithScarletWoman], "slayer_shot_anna_died_without_game_ending"),
  );
  return game;
}

export async function solve() {
  return buildModel().solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-03b-not-throwing-away-my-shot.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: POISON_CONTEXT,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk, { missing: "not in play" }),
      forcedRole("Recluse", Recluse, { missing: "not in play" }),
    ],
  });
