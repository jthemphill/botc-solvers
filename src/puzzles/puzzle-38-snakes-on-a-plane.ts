import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Baron,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Poisoner,
  Ravenkeeper,
  Recluse,
  Saint,
  ScarletWoman,
  SnakeCharmer,
  Spy,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const NIGHT_3 = "night_3";

export const PLAYERS = ["Tim", "Fraser", "Sula", "Matt", "You", "Hannah", "Dan", "Adam"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const MINION_ROLES = [Baron, Poisoner, Spy, ScarletWoman];
export const CHARACTERS = script(
  Imp,
  Baron,
  Poisoner,
  Spy,
  ScarletWoman,
  Drunk,
  Recluse,
  Saint,
  Empath,
  FortuneTeller,
  Investigator,
  Ravenkeeper,
  SnakeCharmer,
);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, seating: PLAYER_NAMES, backend });
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );
  game.addBaronOutsiderCounts({ withoutBaron: 1, withBaron: 3 });
  game.fixNotActual("You", Imp);
  for (const minion of MINION_ROLES) game.fixNotActual("You", minion);
  game.fixNotActual("You", Drunk);

  game.addClaim("Tim", SnakeCharmer, [SnakeCharmer, Drunk, Imp, ...MINION_ROLES]);
  game.addClaim("Fraser", SnakeCharmer, [SnakeCharmer, Drunk, Imp, ...MINION_ROLES]);
  game.addClaim("Sula", FortuneTeller, [FortuneTeller, Drunk, Imp, ...MINION_ROLES]);
  game.addClaim("Matt", Saint, [Saint, Imp, ...MINION_ROLES]);
  game.addClaim("You", Recluse, [Recluse]);
  game.addClaim("Hannah", Empath, [Empath, Drunk, Imp, ...MINION_ROLES]);
  game.addClaim("Dan", Ravenkeeper, [Ravenkeeper, Drunk, Imp, ...MINION_ROLES]);
  game.addClaim("Adam", Investigator, [Investigator, Drunk, Imp, ...MINION_ROLES]);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2, { activeIf: game.actualIs("Dan", Poisoner).not() });
  game.addPoisonerEffect(NIGHT_3, {
    activeIf: game.allOf(
      [
        game.actualIs("Dan", Poisoner).not(),
        game.actualIs("Sula", Poisoner).not(),
        isDemonOnNightThree(game, "Matt").not(),
      ],
      "poisoner_active_n3",
    ),
  });

  const redHerrings = game.addFortuneTellerRedHerring("Sula");

  addSnakeCharmerPicks(game, "Tim", [
    [NIGHT_1, "Matt"],
    [NIGHT_2, "Sula"],
    [NIGHT_3, "Hannah"],
  ]);
  addSnakeCharmerPicks(game, "Fraser", [
    [NIGHT_1, "Sula"],
    [NIGHT_2, "Hannah"],
    [NIGHT_3, "Adam"],
  ]);

  game.addTruthfulInfoClaim(
    "Sula",
    FortuneTeller,
    game.fortuneTellerNo(redHerrings, ["You", "Tim"], "sula_ft_you_tim_no", (player) =>
      isDemonAtContext(game, player, NIGHT_1),
    ),
    { poisonContext: NIGHT_1 },
  );
  game.addTruthfulInfoClaim(
    "Sula",
    FortuneTeller,
    game.fortuneTellerNo(redHerrings, ["Fraser", "Matt"], "sula_ft_fraser_matt_no", (player) =>
      isDemonAtContext(game, player, NIGHT_2),
    ),
    { poisonContext: NIGHT_2 },
  );
  game.addTruthfulInfoClaim("Hannah", Empath, game.registeredEvilCount(["You", "Dan"], 0, "hannah_empath_n1"), {
    poisonContext: NIGHT_1,
  });
  game.addTruthfulInfoClaim("Hannah", Empath, game.registeredEvilCount(["Adam", "Matt"], 1, "hannah_empath_n2"), {
    poisonContext: NIGHT_2,
  });
  game.addTruthfulInfoClaim("Hannah", Empath, game.registeredEvilCount(["Adam", "Fraser"], 1, "hannah_empath_n3"), {
    poisonContext: NIGHT_3,
  });
  game.addTruthfulInfoClaim("Dan", Ravenkeeper, game.actualIs("Fraser", Poisoner), { poisonContext: NIGHT_2 });
  game.addTruthfulInfoClaim(
    "Adam",
    Investigator,
    Investigator.learnsRoleAmong(game, ["Tim", "Sula"], Baron, "adam_investigator"),
    { poisonContext: NIGHT_1 },
  );

  game.addTruth(
    game.anyOf(
      PLAYER_NAMES.map((player) => isDemonOnNightThree(game, player)),
      "night_3_demon_exists_to_kill_matt",
    ),
  );

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addSnakeCharmerPicks(game: BOTCModel, player: string, picks: readonly (readonly [string, string])[]): void {
  for (const [night, pick] of picks) {
    game.addImplication(
      game.allOf(
        [game.actualIs(player, SnakeCharmer), game.poisoned(player, night).not()],
        `${player}_active_snake_charmer_${night}`,
      ),
      isDemonAtContext(game, pick, night).not(),
    );
  }
}

function isDemonAtContext(game: BOTCModel, player: string, poisonContext: string): BoolVar {
  if (poisonContext === NIGHT_1) return game.actualIs(player, Imp);
  if (poisonContext === NIGHT_2) return isDemonOnNightTwo(game, player);
  return isDemonOnNightThree(game, player);
}

function isDemonOnNightTwo(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf([game.actualIs(player, Imp), game.actualIs("Dan", Imp).not()], `${player}_starting_imp_n2`),
      player === "Dan" || player === "You"
        ? game.constantBool(false, `${player}_cannot_be_dan_starpass_n2`)
        : game.allOf([game.actualIs("Dan", Imp), game.isMinion(player)], `${player}_dan_starpass_n2`),
    ],
    `${player}_demon_n2`,
  );
}

function isDemonOnNightThree(game: BOTCModel, player: string): BoolVar {
  return game.anyOf(
    [
      game.allOf(
        [game.actualIs(player, Imp), game.actualIs("Dan", Imp).not(), game.actualIs("Sula", Imp).not()],
        `${player}_starting_imp_n3`,
      ),
      player === "Dan" || player === "Sula" || player === "You"
        ? game.constantBool(false, `${player}_cannot_be_dan_starpass_n3`)
        : game.allOf([game.actualIs("Dan", Imp), game.isMinion(player)], `${player}_dan_starpass_n3`),
      player === "Dan" || player === "Sula" || player === "You"
        ? game.constantBool(false, `${player}_cannot_be_sw_after_sula_n3`)
        : game.allOf([isDemonOnNightTwo(game, "Sula"), game.actualIs(player, ScarletWoman)], `${player}_sw_after_sula`),
    ],
    `${player}_demon_n3`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-38-snakes-on-a-plane.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_3,
    forcedRoles: [
      forcedRole("Starting Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Drunk", Drunk),
    ],
  });
