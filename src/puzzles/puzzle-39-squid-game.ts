import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BOTCModel } from "../model";
import { differentAlignments } from "../predicates";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  type AppliedInfoClaim,
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
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";

export const EVIL_ROLES = [NoDashii, Witch];
type Night = typeof NIGHT_1 | typeof NIGHT_2;
interface ClaimContext {
  readonly malfunctions: Record<Night, BoolLike[]>;
}

export const PLAYERS = [
  new Sage({
    name: "Fraser",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game) =>
          game.anyOf([game.actualIs("Jasmine", NoDashii), game.actualIs("Matt", NoDashii)], "fraser_sage_demon_pair"),
      },
    ],
  }),
  new Artist({
    name: "Tom",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game) =>
          game.anyOf(
            [game.actualIs("Jasmine", Mutant), game.actualIs("Matt", Mutant), game.actualIs("Aoife", Mutant)],
            "tom_artist_mutant_yes",
          ),
      },
    ],
  }),
  new Mathematician({
    name: "Sula",
    infoClaims: [
      {
        poisonContext: NIGHT_1,
        learned: (game, context) =>
          game.boolSumEquals((context as ClaimContext).malfunctions[NIGHT_1], 0, "sula_mathematician_night_1_0"),
      },
      {
        poisonContext: NIGHT_2,
        learned: (game, context) =>
          game.boolSumEquals((context as ClaimContext).malfunctions[NIGHT_2], 1, "sula_mathematician_night_2_1"),
      },
    ],
  }),
  new Klutz({ name: "Hannah" }),
  new Oracle({
    name: "You",
    infoClaims: [
      {
        poisonContext: NIGHT_2,
        learned: (game) =>
          game.boolSumEquals(
            ["Tom", "Aoife", "Fraser"].map((player) => game.isEvil(player)),
            1,
            "you_oracle_one_dead_evil",
          ),
      },
    ],
  }),
  new Juggler({
    name: "Jasmine",
    guesses: { You: Witch, Aoife: Witch, Tom: Witch, Fraser: Sage, Hannah: Klutz },
    correctCount: 3,
    poisonContext: NIGHT_2,
  }),
  new Philosopher({
    name: "Matt",
    infoClaims: [{ poisonContext: NIGHT_1, learned: (game) => differentAlignments(game, "Aoife", "Tom") }],
  }),
  new Seamstress({
    name: "Aoife",
    among: ["Matt", "Hannah"],
    aligned: false,
    poisonContext: NIGHT_1,
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
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
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);
  game.fixNotActual("You", NoDashii);
  game.fixNotActual("You", Witch);
  game.fixNotActual("You", Mutant);
  for (const deadBeforeFinalNight of ["Tom", "Aoife", "Fraser", "Sula"])
    game.fixNotActual(deadBeforeFinalNight, NoDashii);
  for (const deadPlayer of ["Tom", "Aoife", "Fraser"]) game.fixNotActual(deadPlayer, Mutant);

  const context: ClaimContext = { malfunctions: { [NIGHT_1]: [], [NIGHT_2]: [] } };
  applyClaims(
    game,
    PLAYERS.filter((claim) => claim.name === "You"),
    { evilRoles: [], extraPossibleActualRoles: [Klutz], info: addInfoClaim, context },
  );
  applyClaims(
    game,
    PLAYERS.filter((claim) => claim.name === "Jasmine" || claim.name === "Matt"),
    { extraPossibleActualRoles: [Mutant], info: addInfoClaim, context },
  );
  applyClaims(
    game,
    PLAYERS.filter(
      (claim) =>
        !(claim instanceof Mathematician) && claim.name !== "You" && claim.name !== "Jasmine" && claim.name !== "Matt",
    ),
    { info: addInfoClaim, context },
  );
  applyClaims(
    game,
    PLAYERS.filter((claim) => claim instanceof Mathematician),
    { info: addInfoClaim, context },
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addInfoClaim(game: BOTCModel, claim: AppliedInfoClaim): void {
  const poisonContext = claim.poisonContext as Night;
  if (claim.role === Mathematician) {
    game.addImplication(
      game.allOf(
        [game.actualIs(claim.player, Mathematician), game.noDashiiPoisoned(claim.player).not()],
        `sula_mathematician_${poisonContext}_active`,
      ),
      claim.learned,
    );
    return;
  }

  const malfunction = game.addNoDashiiInfoClaim(claim.player, claim.role, claim.learned, poisonContext);
  (claim.context as ClaimContext).malfunctions[poisonContext].push(malfunction);
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-39-squid-game.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", NoDashii, { includeRole: true }),
      forcedRole("Minion", Witch),
      forcedRole("Outsider", [Klutz, Mutant], { includeRole: true }),
    ],
  });
