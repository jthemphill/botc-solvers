import { CharacterType, type RoleRef, roleName } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Baron,
  Drunk,
  Imp,
  Investigator,
  Poisoner,
  Ravenkeeper,
  Saint,
  ScarletWoman,
  Spy,
  VillageIdiot,
  Virgin,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = "night_1";
export const NIGHT_2 = "night_2";
export const DRUNK_VILLAGE_IDIOT = "drunk_village_idiot";

export const PLAYERS = ["Melchior", "Mary", "Balthazar", "Gabriel", "You", "Caspar", "Joseph"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const VILLAGE_IDIOT_CLAIMANTS = ["Melchior", "Balthazar", "Caspar"];
export const CHARACTERS = script(
  Imp,
  Baron,
  Poisoner,
  ScarletWoman,
  Spy,
  Drunk,
  Saint,
  Investigator,
  Ravenkeeper,
  VillageIdiot,
  Virgin,
);
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, {
    characters: CHARACTERS,
    seating: PLAYER_NAMES,
    uniqueCharacters: false,
    backend,
  });
  enforceUniqueRolesExceptVillageIdiot(game);
  game.setCharacterCount(Imp, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isMinion(player)),
    1,
  );

  const outsiderCount = PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider));
  game.addEnforcedExactlyN(outsiderCount, 2, game.roleInPlay(Baron));
  game.addEnforcedExactlyN(outsiderCount, 0, game.roleInPlay(Baron).not());

  addClaim(game, "Melchior", VillageIdiot, [VillageIdiot, Drunk, Imp, Baron, Poisoner, ScarletWoman, Spy]);
  addClaim(game, "Mary", Virgin, [Virgin, Drunk, Imp, Baron, Poisoner, ScarletWoman, Spy]);
  addClaim(game, "Balthazar", VillageIdiot, [VillageIdiot, Drunk, Imp, Baron, Poisoner, ScarletWoman, Spy]);
  addClaim(game, "Gabriel", Ravenkeeper, [Ravenkeeper, Drunk, Imp, Baron, Poisoner, ScarletWoman, Spy]);
  addClaim(game, "You", Investigator, [Investigator, Drunk]);
  addClaim(game, "Caspar", VillageIdiot, [VillageIdiot, Drunk, Imp, Baron, Poisoner, ScarletWoman, Spy]);
  addClaim(game, "Joseph", Saint, [Saint, Imp, Baron, Poisoner, ScarletWoman, Spy]);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2);
  const drunkVillageIdiots = addVillageIdiotDrunkenness(game);

  addVillageIdiotCheck(game, drunkVillageIdiots, "Melchior", NIGHT_1, "Balthazar", true);
  addVillageIdiotCheck(game, drunkVillageIdiots, "Melchior", NIGHT_2, "Mary", true);
  addVirginNomination(game);
  addVillageIdiotCheck(game, drunkVillageIdiots, "Balthazar", NIGHT_1, "Joseph", true);
  addVillageIdiotCheck(game, drunkVillageIdiots, "Balthazar", NIGHT_2, "Caspar", true);
  game.addTruthfulInfoClaim("Gabriel", Ravenkeeper, game.registersAsRole("Balthazar", Drunk, "gabriel_ravenkeeper"), {
    poisonContext: NIGHT_2,
  });
  game.addTruthfulInfoClaim(
    "You",
    Investigator,
    Investigator.learnsRoleAmong(game, ["Mary", "Gabriel"], Baron, "you_investigator"),
    {
      poisonContext: NIGHT_1,
    },
  );
  addVillageIdiotCheck(game, drunkVillageIdiots, "Caspar", NIGHT_1, "Mary", true);
  addVillageIdiotCheck(game, drunkVillageIdiots, "Caspar", NIGHT_2, "Joseph", true);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function enforceUniqueRolesExceptVillageIdiot(game: BOTCModel): void {
  const always = game.constantBool(true, "unique_non_village_idiot_roles");
  for (const role of CHARACTERS) {
    if (roleName(role) === VillageIdiot.roleName) continue;
    game.addEnforcedAtMostN(
      PLAYER_NAMES.map((player) => game.actualIs(player, role)),
      1,
      always,
    );
  }
}

function addClaim(game: BOTCModel, player: string, apparentRole: RoleRef, possibleRoles: readonly RoleRef[]): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, possibleRoles);
}

function addVillageIdiotDrunkenness(game: BOTCModel): ReadonlyMap<string, BoolVar> {
  const drunkVillageIdiots = new Map(
    VILLAGE_IDIOT_CLAIMANTS.map((player) => [player, game.newBool(`${player}_${DRUNK_VILLAGE_IDIOT}`)] as const),
  );
  for (const [player, drunkVillageIdiot] of drunkVillageIdiots)
    game.addImplication(drunkVillageIdiot, game.actualIs(player, VillageIdiot));

  const actualVillageIdiots = VILLAGE_IDIOT_CLAIMANTS.map((player) => game.actualIs(player, VillageIdiot));
  const zeroVillageIdiots = game.boolSumEquals(actualVillageIdiots, 0, "zero_village_idiots");
  const oneVillageIdiot = game.boolSumEquals(actualVillageIdiots, 1, "one_village_idiot");
  const multipleVillageIdiots = game.not(
    game.anyOf([zeroVillageIdiots, oneVillageIdiot], "zero_or_one_village_idiot"),
    "multiple_village_idiots",
  );
  game.addEnforcedExactlyN([...drunkVillageIdiots.values()], 1, multipleVillageIdiots);
  game.addEnforcedExactlyN([...drunkVillageIdiots.values()], 0, multipleVillageIdiots.not());
  return drunkVillageIdiots;
}

function addVillageIdiotCheck(
  game: BOTCModel,
  drunkVillageIdiots: ReadonlyMap<string, BoolVar>,
  player: string,
  poisonContext: string,
  target: string,
  evil: boolean,
): void {
  const learned = evil
    ? game.registersAsEvil(target, `${player}_${target}`)
    : game.registersAsGood(target, `${player}_${target}`);
  addVillageIdiotInfoClaim(game, drunkVillageIdiots, player, poisonContext, learned);
}

function addVillageIdiotInfoClaim(
  game: BOTCModel,
  drunkVillageIdiots: ReadonlyMap<string, BoolVar>,
  player: string,
  poisonContext: string,
  learned: BoolLike,
): void {
  const active = game.allOf(
    [
      game.actualIs(player, VillageIdiot),
      game.poisoned(player, poisonContext).not(),
      (drunkVillageIdiots.get(player) as BoolVar).not(),
    ],
    `${player}_${poisonContext}_active_village_idiot`,
  );
  game.addImplication(active, learned);
}

function addVirginNomination(game: BOTCModel): void {
  const activeVirgin = game.allOf(
    [game.actualIs("Mary", Virgin), game.poisoned("Mary", NIGHT_1).not()],
    "mary_active_virgin",
  );
  game.addImplication(activeVirgin, game.hasCharacterType("Balthazar", CharacterType.Townsfolk).not());
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-20-the-three-wise-men.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    poisonContext: NIGHT_2,
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
