import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Baron,
  Butler,
  Drunk,
  Empath,
  FortuneTeller,
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
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const MINION_ROLES = [Baron, Poisoner, Spy, ScarletWoman];
export const PLAYERS = [
  new Saint({ name: "Hannah" }),
  new Librarian({
    name: "Fraser",
    role: Drunk,
    among: ["Jasmine", "Hannah"],
    poisonContext: NIGHT_1,
  }),
  new Empath({
    name: "Tim",
    infoClaims: [
      { poisonContext: NIGHT_1, learned: (game) => game.registeredEvilCount(["Fraser", "Josh"], 2, "tim_empath_n1") },
      { poisonContext: NIGHT_2, learned: (game) => game.registeredEvilCount(["Adam", "Hannah"], 1, "tim_empath_n2") },
    ],
  }),
  new Butler({ name: "Josh" }),
  new Slayer({
    name: "Adam",
    infoClaims: [
      { poisonContext: NIGHT_3, learned: (game) => game.registersAsRole("Matthew", Imp, "adam_slayer_matthew").not() },
    ],
  }),
  new Investigator({
    name: "You",
    role: ScarletWoman,
    among: ["Steph", "Fraser"],
    poisonContext: NIGHT_1,
  }),
  new FortuneTeller({
    name: "Matthew",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) =>
          game.allOf(
            [
              game.fortuneTellerNo(context as ReadonlyMap<string, BoolVar>, ["Tim", "Josh"], "matthew_ft_tim_josh_no"),
              game.fortuneTellerNo(
                context as ReadonlyMap<string, BoolVar>,
                ["Hannah", "Tim"],
                "matthew_ft_hannah_tim_no",
              ),
              game.fortuneTellerYes(
                context as ReadonlyMap<string, BoolVar>,
                ["You", "Matthew"],
                "matthew_ft_you_self_yes",
              ),
            ],
            "matthew_fortune_teller_checks",
          ),
      },
    ],
  }),
  new Recluse({ name: "Steph" }),
  new Washerwoman({
    name: "Jasmine",
    role: Empath,
    among: ["Tim", "Adam"],
    poisonContext: NIGHT_1,
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  Baron,
  Poisoner,
  Spy,
  ScarletWoman,
  Butler,
  Drunk,
  Recluse,
  Saint,
  Empath,
  FortuneTeller,
  Investigator,
  Librarian,
  Slayer,
  Washerwoman,
);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.addBaronOutsiderCounts({ withoutBaron: 2, withBaron: 4 });
  game.fixNotActual("You", Imp);
  for (const minion of MINION_ROLES) game.fixNotActual("You", minion);
  for (const deadBeforeFinalNight of ["Josh", "Fraser", "Jasmine", "Tim"]) game.fixNotActual(deadBeforeFinalNight, Imp);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Josh", Poisoner).not() });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [game.actualIs("Josh", Poisoner).not(), game.actualIs("Jasmine", Poisoner).not()],
      "poisoner_active_n3",
    ),
  });

  const redHerrings = game.addFortuneTellerRedHerring("Matthew");
  applyClaims(game, PLAYERS, { context: redHerrings });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-40-nine-lives.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_3,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk),
    ],
  });
