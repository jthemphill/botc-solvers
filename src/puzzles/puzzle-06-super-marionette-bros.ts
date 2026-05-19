import { CharacterType, type RoleRef, roleName } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Drunk,
  Empath,
  Investigator,
  Juggler,
  Knight,
  Librarian,
  Marionette,
  NoDashii,
  Noble,
  Pukka,
  Saint,
  Seamstress,
  Steward,
  Vortox,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const PLAYERS = [
  new Investigator({ name: "Aoife", role: Marionette, among: ["Dan", "Matthew"] }),
  new Juggler({
    name: "Sula",
    guesses: { You: Librarian, Tim: Marionette, Dan: Vortox, Fraser: Drunk, Matthew: Pukka },
    correctCount: 2,
  }),
  new Knight({ name: "Steph", noDemonAmong: ["Sarah", "Dan"] }),
  new Empath({ name: "Fraser", count: 0 }),
  new Steward({ name: "Matthew", goodPlayer: "Dan" }),
  new Librarian({ name: "You", role: Drunk, among: ["Sula", "Fraser"] }),
  new Saint({ name: "Sarah" }),
  new Noble({ name: "Tim", oneEvilAmong: ["Aoife", "Sula", "Fraser"] }),
  new Seamstress({ name: "Dan", aligned: false, among: ["Aoife", "Tim"] }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Pukka,
  NoDashii,
  Vortox,
  Marionette,
  Drunk,
  Saint,
  Empath,
  Investigator,
  Juggler,
  Knight,
  Librarian,
  Noble,
  Seamstress,
  Steward,
);
export const DEMON_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Demon });
export const NIGHT_1 = "night_1";

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isDemon(player)),
    1,
  );
  game.setCharacterCount(Marionette, 1);
  game.setCharacterCount(Drunk, 1);
  game.setCharacterCount(Saint, 1);
  game.allowPoisonInContext(NIGHT_1);

  for (const claim of PLAYERS) game.addRoleClaim({ player: claim.name, apparentRole: claim });
  game.setPossibleActualRoles("You", [Librarian, Drunk, Marionette]);
  for (const deadPlayer of ["Fraser", "Steph"])
    for (const demonRole of DEMON_ROLES) game.fixNotActual(deadPlayer, demonRole);
  for (const player of PLAYER_NAMES) {
    const [left, right] = game.neighbors(player);
    game.addImplication(
      game.actualIs(player, Marionette),
      game.anyOf([game.isDemon(left), game.isDemon(right)], `${player}_marionette_neighbors_demon`),
    );
  }
  addDemonPoisoning(game);

  addVortoxAwareInfo(
    game,
    "Aoife",
    Investigator,
    Investigator.learnsRoleAmong(game, ["Dan", "Matthew"], Marionette, "aoife_investigator_marionette"),
  );
  addVortoxAwareInfo(
    game,
    "Sula",
    Juggler,
    Juggler.learnsCorrectCount(
      game,
      { You: Librarian, Tim: Marionette, Dan: Vortox, Fraser: Drunk, Matthew: Pukka },
      2,
      "sula_juggler_count",
    ),
  );
  addVortoxAwareInfo(game, "Steph", Knight, Knight.learnsNoDemonAmong(game, ["Sarah", "Dan"], "steph_knight_no_demon"));
  addVortoxAwareInfo(game, "Fraser", Empath, Empath.learnsCount(game, "Fraser", 0, "fraser_empath"));
  addVortoxAwareInfo(game, "Matthew", Steward, Steward.learnsGoodPlayer(game, "Dan"));
  addVortoxAwareInfo(
    game,
    "You",
    Librarian,
    Librarian.learnsRoleAmong(game, ["Sula", "Fraser"], Drunk, "you_librarian_drunk"),
  );
  addVortoxAwareInfo(game, "Tim", Noble, Noble.learnsEvilCount(game, ["Aoife", "Sula", "Fraser"], 1));
  addVortoxAwareInfo(game, "Dan", Seamstress, Seamstress.learnsDifferentAlignment(game, "Aoife", "Tim"));
  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addVortoxAwareInfo(game: BOTCModel, player: string, apparentRole: RoleRef, claimTruth: BoolLike): void {
  const active = game.allOf(
    [game.actualIs(player, apparentRole), game.poisoned(player, NIGHT_1).not()],
    `${player}_${roleName(apparentRole)}_active_non_vortox_claim`,
  );
  const vortoxInPlay = game.roleInPlay(Vortox);
  game.addImplication(game.allOf([active, vortoxInPlay.not()], `${player}_truthful_info`), claimTruth);
  game.addImplication(
    game.allOf([active, vortoxInPlay], `${player}_vortox_false_info`),
    game.not(claimTruth, `${player}_claim_false`),
  );
}

function addDemonPoisoning(game: BOTCModel): void {
  for (const player of PLAYER_NAMES) {
    const sources: BoolLike[] = [];
    if (player === "Steph") sources.push(game.roleInPlay(Pukka));
    for (const demon of PLAYER_NAMES) {
      const [left, right] = game.neighbors(demon);
      if (player !== left && player !== right) continue;
      sources.push(
        game.allOf(
          [game.actualIs(demon, NoDashii), game.hasCharacterType(player, CharacterType.Townsfolk)],
          `${player}_neighboring_no_dashii_${demon}`,
        ),
      );
    }
    const poisoned = game.poisoned(player, NIGHT_1);
    const poisonedByDemon = game.anyOf(sources, `${player}_poisoned_by_demon`);
    game.addImplication(poisonedByDemon, poisoned);
    game.addImplication(poisoned, poisonedByDemon);
  }
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-06-super-marionette-bros.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_1,
    forcedRoles: [
      forcedRole("Demon", DEMON_ROLES, { includeRole: true }),
      forcedRole("Minion", Marionette, { includeRole: true }),
    ],
  });
