import { Alignment, CharacterType } from "../core";
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
  new Investigator({ name: "Sula", role: Baron, among: ["You", "Aoife"] }),
  new Washerwoman({ name: "Matthew", role: Librarian, among: ["Aoife", "Oscar"] }),
  new Librarian({ name: "Oscar", outsiderCount: 0 }),
  new Empath({ name: "Josh", count: 0 }),
  new Slayer({ name: "You" }),
  new Chef({ name: "Aoife", count: 0 }),
  new Recluse({ name: "Tom" }),
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
  game.addEnforcedExactlyN(outsiderCount, 2, baronInPlay);
  game.addEnforcedExactlyN(outsiderCount, 0, baronInPlay.not());
  game.addPoisonerEffect(POISON_CONTEXT);
  applyClaims(game, PLAYERS, { poisonContext: POISON_CONTEXT });
  game.addTruth(game.actualIs("You", Slayer));
  game.addFalse(game.poisoned("You", POISON_CONTEXT));
  const tomImpWithScarletWoman = game.allOf(
    [game.actualIs("Tom", Imp), game.roleInPlay(ScarletWoman)],
    "tom_imp_with_scarlet_woman",
  );
  const tomRecluseRegistersAsImp = game.allOf(
    [game.actualIs("Tom", Recluse), game.registersAsRole("Tom", Imp, "you_slayer")],
    "tom_recluse_registers_as_imp",
  );
  game.addTruth(
    game.anyOf([tomRecluseRegistersAsImp, tomImpWithScarletWoman], "slayer_shot_tom_died_without_game_ending"),
  );
  return game;
}

export async function solve() {
  return buildModel().solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-03a-not-throwing-away-my-shot.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: POISON_CONTEXT,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk, { missing: "not in play" }),
      forcedRole("Recluse", Recluse, { missing: "not in play" }),
    ],
  });
