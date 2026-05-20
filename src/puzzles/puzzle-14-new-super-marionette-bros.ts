import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Chef,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Marionette,
  Poisoner,
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
  new FortuneTeller({
    name: "Brett",
    checks: [
      {
        left: "Danielle",
        right: "Gwilym",
        yes: false,
        name: "brett_fortune_teller",
        demonRole: Imp,
        registers: true,
        poisonContext: NIGHT_1,
      },
    ],
  }),
  new Empath({
    name: "Rob",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => Empath.learnsCount(game, "Rob", 0, "rob_empath_night_1") },
      { poisonContext: NIGHT_2, learned: (game) => Empath.learnsCount(game, "Rob", 0, "rob_empath_night_2") },
    ],
  }),
  new Chef({ name: "Lav", count: 1, poisonContext: NIGHT_1 }),
  new Investigator({ name: "Lydia", role: Marionette, among: ["You", "Danielle"], poisonContext: NIGHT_1 }),
  new Slayer({
    name: "You",
    infoClaims: [{ poisonContext: NIGHT_1, learned: (game) => game.registersAsRole("Lydia", Imp, "you_slayer").not() }],
  }),
  new Washerwoman({ name: "Danielle", role: Empath, among: ["Rob", "Lav"], poisonContext: NIGHT_1 }),
  new Undertaker({ name: "Gwilym", player: "You", role: Slayer, poisonContext: NIGHT_2 }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Poisoner,
  Spy,
  ScarletWoman,
  Marionette,
  Drunk,
  Chef,
  Empath,
  FortuneTeller,
  Investigator,
  Slayer,
  Undertaker,
  Washerwoman,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.setCharacterCount(Drunk, 0);
  game.fixNotActual("You", Imp);
  game.fixNotActual("Brett", Imp);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2);
  applyClaims(game, PLAYERS);
  game.setPossibleActualRoles("You", [Slayer, Marionette]);
  for (const player of PLAYER_NAMES) {
    const [left, right] = game.neighbors(player);
    game.addImplication(
      game.actualIs(player, Marionette),
      game.anyOf([game.actualIs(left, Imp), game.actualIs(right, Imp)], `${player}_marionette_neighbors_imp`),
    );
  }

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-14-new-super-marionette-bros.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_2,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
