import { forcedRole, printSolution } from "../display";
import { type BoolLike, BOTCModel } from "../model";
import { differentAlignments } from "../predicates";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Artist,
  Juggler,
  Klutz,
  Mathematician,
  Mutant,
  NoDashii,
  Oracle,
  Philosopher,
  Sage,
  Seamstress,
  Witch,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const PLAYERS = ["Fraser", "Tom", "Sula", "Hannah", "You", "Jasmine", "Matt", "Aoife"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const EVIL_ROLES = [NoDashii, Witch];
export const CHARACTERS = script(
  NoDashii,
  Witch,
  Mutant,
  Klutz,
  Artist,
  Juggler,
  Mathematician,
  Oracle,
  Philosopher,
  Sage,
  Seamstress,
);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(NoDashii, 1);
  game.setCharacterCount(Witch, 1);
  game.forceOutsiderCount(1);
  game.fixNotActual("You", NoDashii);
  game.fixNotActual("You", Witch);
  game.fixNotActual("You", Mutant);
  for (const deadBeforeFinalNight of ["Tom", "Aoife", "Fraser", "Sula"])
    game.fixNotActual(deadBeforeFinalNight, NoDashii);
  for (const deadPlayer of ["Tom", "Aoife", "Fraser"]) game.fixNotActual(deadPlayer, Mutant);

  game.addClaim("Fraser", Sage, [Sage, NoDashii, Witch]);
  game.addClaim("Tom", Artist, [Artist, NoDashii, Witch]);
  game.addClaim("Sula", Mathematician, [Mathematician, NoDashii, Witch]);
  game.addClaim("Hannah", Klutz, [Klutz, NoDashii, Witch]);
  game.addClaim("You", Oracle, [Oracle, Klutz]);
  game.addClaim("Jasmine", Juggler, [Juggler, Mutant, NoDashii, Witch]);
  game.addClaim("Matt", Philosopher, [Philosopher, Mutant, NoDashii, Witch]);
  game.addClaim("Aoife", Seamstress, [Seamstress, NoDashii, Witch]);

  const aoifeInfo = differentAlignments(game, "Matt", "Hannah");
  const fraserInfo = game.anyOf(
    [game.actualIs("Jasmine", NoDashii), game.actualIs("Matt", NoDashii)],
    "fraser_sage_demon_pair",
  );
  const tomInfo = game.anyOf(
    [game.actualIs("Jasmine", Mutant), game.actualIs("Matt", Mutant), game.actualIs("Aoife", Mutant)],
    "tom_artist_mutant_yes",
  );
  const youInfo = game.boolSumEquals(
    ["Tom", "Aoife", "Fraser"].map((player) => game.isEvil(player)),
    1,
    "you_oracle_one_dead_evil",
  );

  const nightOneMalfunctions = [
    game.addNoDashiiInfoClaim("Aoife", Seamstress, aoifeInfo, NIGHT_1),
    game.addNoDashiiInfoClaim("Fraser", Sage, fraserInfo, NIGHT_1),
  ];
  const nightTwoMalfunctions = [
    game.addNoDashiiInfoClaim("You", Oracle, youInfo, NIGHT_2),
    game.addNoDashiiInfoClaim(
      "Jasmine",
      Juggler,
      Juggler.learnsCorrectCount(
        game,
        { You: Witch, Aoife: Witch, Tom: Witch, Fraser: Sage, Hannah: Klutz },
        3,
        "jasmine_juggler_count",
      ),
      NIGHT_2,
    ),
  ];

  game.addNoDashiiInfoClaim("Tom", Artist, tomInfo, NIGHT_1);
  game.addNoDashiiInfoClaim("Matt", Philosopher, differentAlignments(game, "Aoife", "Tom"), NIGHT_1);
  addMathematicianInfo(game, nightOneMalfunctions, 0, NIGHT_1);
  addMathematicianInfo(game, nightTwoMalfunctions, 1, NIGHT_2);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addMathematicianInfo(game: BOTCModel, malfunctions: readonly BoolLike[], count: number, name: string): void {
  game.addImplication(
    game.allOf(
      [game.actualIs("Sula", Mathematician), game.noDashiiPoisoned("Sula").not()],
      `sula_mathematician_${name}_active`,
    ),
    game.boolSumEquals(malfunctions, count, `sula_mathematician_${name}_${count}`),
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-39-squid-game.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", NoDashii, { includeRole: true }),
      forcedRole("Minion", Witch),
      forcedRole("Outsider", [Klutz, Mutant], { includeRole: true }),
    ],
  });
