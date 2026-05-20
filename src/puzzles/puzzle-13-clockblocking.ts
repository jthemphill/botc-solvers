import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Baron,
  Clockmaker,
  Drunk,
  FortuneTeller,
  Imp,
  Investigator,
  Librarian,
  Poisoner,
  Ravenkeeper,
  Recluse,
  ScarletWoman,
  Slayer,
  Spy,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const PLAYERS = [
  new Ravenkeeper({ name: "Tim" }),
  new FortuneTeller({
    name: "Sarah",
    checks: [
      { left: "You", right: "Oscar", yes: false, demonRole: Imp, registers: true, poisonContext: NIGHT_1 },
      { left: "You", right: "Jasmine", yes: false, demonRole: Imp, registers: true, poisonContext: NIGHT_2 },
    ],
  }),
  new Slayer({ name: "Fraser" }),
  new Recluse({ name: "Aoife" }),
  new Investigator({ name: "You", role: ScarletWoman, among: ["Sarah", "Aoife"], poisonContext: NIGHT_1 }),
  new Clockmaker({ name: "Jasmine" }),
  new Librarian({ name: "Oscar", outsiderCount: 0, poisonContext: NIGHT_1 }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Poisoner,
  Spy,
  Baron,
  ScarletWoman,
  Drunk,
  Recluse,
  Clockmaker,
  FortuneTeller,
  Investigator,
  Librarian,
  Ravenkeeper,
  Slayer,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.fixNotActual("Aoife", Imp);
  game.fixNotActual("Tim", Imp);

  const outsiderCount = PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider));
  game.addEnforcedExactlyN(outsiderCount, 2, game.roleInPlay(Baron));
  game.addEnforcedExactlyN(outsiderCount, 0, game.roleInPlay(Baron).not());

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Aoife", Poisoner).not() });
  applyClaims(game, PLAYERS);
  game.setPossibleActualRoles("You", [Investigator, Drunk]);
  game.addTruthfulInfoClaim("Jasmine", Clockmaker, demonSitsStepsFromMinion(game, 3), {
    poisonContext: NIGHT_1,
  });
  game.addTruthfulInfoClaim("Tim", Ravenkeeper, game.registersAsRole("Oscar", Librarian, "tim_ravenkeeper"), {
    poisonContext: NIGHT_2,
  });

  const activeSlayer = game.allOf(
    [game.actualIs("Fraser", Slayer), game.poisoned("Fraser", NIGHT_2).not()],
    "fraser_active_slayer",
  );
  game.addImplication(activeSlayer, game.registersAsRole("Oscar", Imp, "fraser_slayer").not());

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function demonSitsStepsFromMinion(game: BOTCModel, steps: number) {
  return game.anyOf(
    PLAYER_NAMES.flatMap((demon, demonIndex) =>
      PLAYER_NAMES.flatMap((minion, minionIndex) => {
        const clockwise = (minionIndex - demonIndex + PLAYER_NAMES.length) % PLAYER_NAMES.length;
        const distance = Math.min(clockwise, PLAYER_NAMES.length - clockwise);
        return distance === steps
          ? [
              game.allOf(
                [
                  game.actualIs(demon, Imp),
                  game.anyOf(
                    MINION_ROLES.map((role) => game.actualIs(minion, role)),
                    `${minion}_is_minion`,
                  ),
                ],
                `${demon}_${minion}_demon_${steps}_from_minion`,
              ),
            ]
          : [];
      }),
    ),
    `demon_${steps}_steps_from_minion`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-13-clockblocking.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_2,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
