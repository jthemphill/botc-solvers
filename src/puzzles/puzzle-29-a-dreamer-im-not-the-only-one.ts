import { forcedRole, printSolution } from "../display";
import { BOTCModel } from "../model";
import { Dreamer, Drunk, Imp, Poisoner, playerNames, script } from "../characters";
import { KissatBackend, type SatBackend } from "../sat";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const PLAYERS = ["Sula", "Steph", "Hannah", "Fraser", "You", "Jasmine", "Adam", "Sarah"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(Imp, Poisoner, Drunk, Dreamer);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, {
    characters: CHARACTERS,
    seating: PLAYER_NAMES,
    uniqueCharacters: false,
    backend,
  });
  game.setCharacterCount(Imp, 1);
  game.setCharacterCount(Poisoner, 1);
  game.setCharacterCount(Drunk, 1);
  game.addEnforcedExactlyN(
    PLAYER_NAMES.map((player) => game.actualIs(player, Dreamer)),
    5,
    game.constantBool(true, "five_dreamers"),
  );

  for (const player of PLAYER_NAMES) {
    game.setApparentRole(player, Dreamer);
    game.setPossibleActualRoles(player, player === "You" ? [Dreamer, Drunk] : [Dreamer, Drunk, Imp, Poisoner]);
  }
  game.fixNotActual("Jasmine", Imp);
  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Jasmine", Poisoner).not() });

  addDreamerInfo(game, "Sula", NIGHT_1, "Jasmine", [Drunk, Poisoner]);
  addDreamerInfo(game, "Sula", NIGHT_2, "Hannah", [Drunk, Poisoner]);
  addDreamerInfo(game, "Steph", NIGHT_1, "Jasmine", [Drunk, Imp]);
  addDreamerInfo(game, "Steph", NIGHT_2, "Sula", [Dreamer, Poisoner]);
  addDreamerInfo(game, "Hannah", NIGHT_1, "Adam", [Drunk, Poisoner]);
  addDreamerInfo(game, "Hannah", NIGHT_2, "Sula", [Drunk, Imp]);
  addDreamerInfo(game, "Fraser", NIGHT_1, "Hannah", [Drunk, Imp]);
  addDreamerInfo(game, "Fraser", NIGHT_2, "Jasmine", [Drunk, Poisoner]);
  addDreamerInfo(game, "You", NIGHT_1, "Jasmine", [Dreamer, Poisoner]);
  addDreamerInfo(game, "Jasmine", NIGHT_1, "Sula", [Drunk, Imp]);
  addDreamerInfo(game, "Adam", NIGHT_1, "Jasmine", [Dreamer, Imp]);
  addDreamerInfo(game, "Adam", NIGHT_2, "Fraser", [Dreamer, Imp]);
  addDreamerInfo(game, "Sarah", NIGHT_1, "Jasmine", [Drunk, Poisoner]);
  addDreamerInfo(game, "Sarah", NIGHT_2, "Adam", [Drunk, Imp]);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addDreamerInfo(
  game: BOTCModel,
  player: string,
  poisonContext: string,
  target: string,
  roles: readonly [typeof Dreamer | typeof Drunk, typeof Drunk | typeof Imp | typeof Poisoner],
): void {
  game.addTruthfulInfoClaim(
    player,
    Dreamer,
    Dreamer.learnsOneOf(game, target, roles, `${player}_${poisonContext}_dreamer`),
    {
      poisonContext,
    },
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-29-a-dreamer-im-not-the-only-one.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", Poisoner, { includeRole: true }),
      forcedRole("Outsider", Drunk, { includeRole: true }),
    ],
  });
