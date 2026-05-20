import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  Baron,
  Chef,
  Drunk,
  FortuneTeller,
  Imp,
  Poisoner,
  Ravenkeeper,
  Recluse,
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
    name: "Tom",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) => {
          const redHerrings = context as ReadonlyMap<string, BoolVar>;
          return game.allOf(
            [
              fortuneTellerLearnsCheck(game, redHerrings, "Tom", "Sula", false, "tom_ft_tom_sula"),
              fortuneTellerLearnsCheck(game, redHerrings, "Tom", "Josh", true, "tom_ft_tom_josh"),
            ],
            "tom_fortune_teller_checks",
          );
        },
      },
    ],
  }),
  new Chef({ name: "Sula", count: 0, poisonContext: NIGHT_1 }),
  new Recluse({ name: "Fraser" }),
  new Washerwoman({ name: "Josh", role: Undertaker, among: ["Dan", "Sula"], poisonContext: NIGHT_1 }),
  new Slayer({
    name: "You",
    infoClaims: [
      { poisonContext: NIGHT_2, learned: (game) => game.registersAsRole("Fraser", Imp, "you_slayer").not() },
    ],
  }),
  new Ravenkeeper({
    name: "Matthew",
    infoClaims: [
      { poisonContext: NIGHT_2, learned: (game) => game.registersAsRole("Josh", Imp, "matthew_ravenkeeper") },
    ],
  }),
  new Undertaker({ name: "Dan", player: "Josh", role: Poisoner, poisonContext: NIGHT_2 }),
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
  Chef,
  FortuneTeller,
  Ravenkeeper,
  Slayer,
  Undertaker,
  Washerwoman,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Josh", Poisoner).not() });

  for (const deadPlayer of ["Josh", "Matthew"]) game.fixNotActual(deadPlayer, Imp);

  const redHerrings = addFortuneTellerRedHerring(game);
  applyClaims(game, PLAYERS, { context: redHerrings });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addFortuneTellerRedHerring(game: BOTCModel): ReadonlyMap<string, BoolVar> {
  const redHerrings = new Map(PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_red_herring`)] as const));
  for (const [player, redHerring] of redHerrings) game.addImplication(redHerring, game.isGood(player));
  const fortuneTellerInPlay = game.roleInPlay(FortuneTeller);
  game.addEnforcedExactlyN([...redHerrings.values()], 1, fortuneTellerInPlay);
  game.addEnforcedExactlyN([...redHerrings.values()], 0, fortuneTellerInPlay.not());
  return redHerrings;
}

function fortuneTellerLearnsCheck(
  game: BOTCModel,
  redHerrings: ReadonlyMap<string, BoolVar>,
  left: string,
  right: string,
  yes: boolean,
  name: string,
): BoolVar {
  const either = game.anyOf(
    [
      game.actualIs(left, Imp),
      game.actualIs(right, Imp),
      redHerrings.get(left) as BoolVar,
      redHerrings.get(right) as BoolVar,
    ],
    `${name}_either_demon_or_red_herring`,
  );
  return yes ? either : game.not(either, `${name}_neither_demon_nor_red_herring`);
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-10-dont-overcook-it.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_2,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
