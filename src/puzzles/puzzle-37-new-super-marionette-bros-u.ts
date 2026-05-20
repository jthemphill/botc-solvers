import { CharacterType, type RoleRef } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { chefCountRegistersAs } from "../predicates";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Chef,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Librarian,
  Marionette,
  Poisoner,
  Ravenkeeper,
  ScarletWoman,
  Spy,
  Undertaker,
  Washerwoman,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const PLAYERS = ["Sula", "Aoife", "Fraser", "Jasmine", "You", "Matt", "Steph", "Adam"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const MINION_ROLES = [Poisoner, Spy, ScarletWoman, Marionette];
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
  Librarian,
  Ravenkeeper,
  Undertaker,
  Washerwoman,
);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.setCharacterCount(Drunk, 1);
  game.addImplication(game.roleInPlay(Marionette), marionetteNeighborsDemon(game));

  addClaim(game, "Sula", Librarian, [Librarian, Drunk, Imp, ...MINION_ROLES]);
  addClaim(game, "Aoife", FortuneTeller, [FortuneTeller, Drunk, Imp, ...MINION_ROLES]);
  addClaim(game, "Fraser", Empath, [Empath, Drunk, Imp, ...MINION_ROLES]);
  addClaim(game, "Jasmine", Imp, [Imp, ...MINION_ROLES]);
  addClaim(game, "You", Undertaker, [Undertaker, Drunk, Marionette]);
  addClaim(game, "Matt", Washerwoman, [Washerwoman, Drunk, Imp, ...MINION_ROLES]);
  addClaim(game, "Steph", Chef, [Chef, Drunk, Imp, ...MINION_ROLES]);
  addClaim(game, "Adam", Ravenkeeper, [Ravenkeeper, Drunk, Imp, ...MINION_ROLES]);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, {
    activeIf: game.allOf(
      [game.actualIs("Matt", Poisoner).not(), game.actualIs("Adam", Poisoner).not()],
      "poisoner_active_night_2",
    ),
  });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [
        game.actualIs("Matt", Poisoner).not(),
        game.actualIs("Adam", Poisoner).not(),
        game.actualIs("Aoife", Poisoner).not(),
        game.actualIs("Sula", Poisoner).not(),
        game.actualIs("Adam", Imp).not(),
        isDemonOnNightThree(game, "Sula").not(),
      ],
      "poisoner_active_night_3",
    ),
  });

  const redHerrings = addFortuneTellerRedHerring(game);

  game.addTruthfulInfoClaim(
    "Sula",
    Librarian,
    Librarian.learnsRoleAmong(game, ["Jasmine", "Steph"], Drunk, "sula_librarian"),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim(
    "Aoife",
    FortuneTeller,
    fortuneTellerYes(game, redHerrings, NIGHT_1, ["You", "Jasmine"], "aoife_ft_you_jasmine_yes"),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim(
    "Aoife",
    FortuneTeller,
    fortuneTellerNo(game, redHerrings, NIGHT_2, ["Jasmine", "Sula"], "aoife_ft_jasmine_sula_no"),
    { poisonContext: NIGHT_2 },
  );
  game.addTruthfulInfoClaim("Fraser", Empath, empathCount(game, ["Jasmine", "Aoife"], 1, "fraser_empath_n1"), {
    poisonContext: NIGHT_1,
  });
  game.addTruthfulInfoClaim("Fraser", Empath, empathCount(game, ["Jasmine", "Aoife"], 1, "fraser_empath_n2"), {
    poisonContext: NIGHT_2,
  });
  game.addTruthfulInfoClaim("Fraser", Empath, empathCount(game, ["Jasmine", "Steph"], 1, "fraser_empath_n3"), {
    poisonContext: NIGHT_3,
  });
  game.addTruthfulInfoClaim("You", Undertaker, game.actualIs("Matt", Spy), { poisonContext: NIGHT_2 });
  game.addTruthfulInfoClaim("You", Undertaker, game.actualIs("Aoife", Marionette), { poisonContext: NIGHT_3 });
  game.addTruthfulInfoClaim(
    "Matt",
    Washerwoman,
    Washerwoman.learnsRoleAmong(game, ["You", "Fraser"], Undertaker, "matt_washerwoman"),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim("Steph", Chef, chefCountRegistersAs(game, 1, "steph_chef"), { poisonContext: NIGHT_1 });
  game.addTruthfulInfoClaim("Adam", Ravenkeeper, game.registersAsRole("Fraser", Empath, "adam_ravenkeeper"), {
    poisonContext: NIGHT_2,
  });

  game.addTruth(
    game.anyOf(
      PLAYER_NAMES.map((player) => isDemonOnNightTwo(game, player)),
      "night_2_demon_exists_to_kill_adam",
    ),
  );
  game.addTruth(
    game.anyOf(
      PLAYER_NAMES.map((player) => isDemonOnNightThree(game, player)),
      "night_3_demon_exists_to_kill_sula",
    ),
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addClaim(game: BOTCModel, player: string, apparentRole: RoleRef, possibleRoles: readonly RoleRef[]): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, possibleRoles);
  if (possibleRoles.includes(Drunk)) game.addDrunkThinksOutOfPlayRole(player, apparentRole, Drunk);
}

function marionetteNeighborsDemon(game: BOTCModel): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((player) => {
      const [left, right] = game.neighbors(player);
      return game.allOf(
        [
          game.actualIs(player, Marionette),
          game.anyOf([game.actualIs(left, Imp), game.actualIs(right, Imp)], `${player}_neighbor_imp`),
        ],
        `${player}_marionette_neighbors_imp`,
      );
    }),
    "marionette_neighbors_demon",
  );
}

function empathCount(game: BOTCModel, players: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.registersAsEvil(player, `${name}_${player}`)),
    count,
    name,
  );
}

function addFortuneTellerRedHerring(game: BOTCModel): ReadonlyMap<string, BoolVar> {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Aoife", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerYes(
  game: BOTCModel,
  redHerrings: ReadonlyMap<string, BoolVar>,
  poisonContext: string,
  players: readonly [string, string],
  name: string,
): BoolVar {
  return game.anyOf(
    [
      ...players.map((player) => isDemonAtContext(game, player, poisonContext)),
      ...players.map((player) => redHerrings.get(player) as BoolVar),
    ],
    name,
  );
}

function fortuneTellerNo(
  game: BOTCModel,
  redHerrings: ReadonlyMap<string, BoolVar>,
  poisonContext: string,
  players: readonly [string, string],
  name: string,
): BoolVar {
  return game.not(fortuneTellerYes(game, redHerrings, poisonContext, players, `${name}_yes`), name);
}

function isDemonAtContext(game: BOTCModel, player: string, poisonContext: string): BoolVar {
  if (poisonContext === NIGHT_1) return game.actualIs(player, Imp);
  if (poisonContext === NIGHT_2) return isDemonOnNightTwo(game, player);
  return isDemonOnNightThree(game, player);
}

function isDemonOnNightTwo(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf([game.actualIs(player, Imp), game.actualIs("Matt", Imp).not()], `${player}_starting_imp_night_2`),
      player === "Matt"
        ? game.constantBool(false, "matt_dead_before_night_2")
        : game.allOf([game.actualIs("Matt", Imp), game.actualIs(player, ScarletWoman)], `${player}_sw_after_matt`),
    ],
    `${player}_demon_night_2`,
  );
}

function isDemonOnNightThree(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf(
        [
          game.actualIs(player, Imp),
          game.actualIs("Matt", Imp).not(),
          game.actualIs("Adam", Imp).not(),
          game.actualIs("Aoife", Imp).not(),
        ],
        `${player}_starting_imp_night_3`,
      ),
      player === "Matt" || player === "Adam" || player === "Aoife"
        ? game.constantBool(false, `${player}_cannot_be_adam_starpass_night_3`)
        : game.allOf([game.actualIs("Adam", Imp), game.isMinion(player)], `${player}_adam_starpass_night_3`),
      player === "Matt" || player === "Adam" || player === "Aoife"
        ? game.constantBool(false, `${player}_cannot_be_scarlet_woman_night_3`)
        : game.allOf(
            [game.actualIs("Matt", Imp), game.actualIs(player, ScarletWoman)],
            `${player}_sw_after_matt_night_3`,
          ),
      player === "Matt" || player === "Adam" || player === "Aoife"
        ? game.constantBool(false, `${player}_cannot_be_sw_after_aoife_night_3`)
        : game.allOf(
            [isDemonOnNightTwo(game, "Aoife"), game.actualIs(player, ScarletWoman)],
            `${player}_sw_after_aoife`,
          ),
    ],
    `${player}_demon_night_3`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-37-new-super-marionette-bros-u.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_3,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk),
    ],
  });
