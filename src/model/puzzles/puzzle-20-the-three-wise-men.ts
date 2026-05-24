import { night, type Timing } from "../model";
import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, type BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  type AppliedInfoClaim,
  type InfoClaim,
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
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = night(1);
export const NIGHT_2 = night(2);
export const DRUNK_VILLAGE_IDIOT = "drunk_village_idiot";

const EVIL_ROLES = [Imp, Baron, Poisoner, ScarletWoman, Spy] as const;

export const PLAYERS = [
  new VillageIdiot({
    name: "Melchior",
    infoClaims: [
      villageIdiotCheck("Melchior", NIGHT_1, "Balthazar", true),
      villageIdiotCheck("Melchior", NIGHT_2, "Mary", true),
    ],
  }),
  new Virgin({
    name: "Mary",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) => game.hasCharacterType("Balthazar", CharacterType.Townsfolk).not(),
      },
    ],
  }),
  new VillageIdiot({
    name: "Balthazar",
    infoClaims: [
      villageIdiotCheck("Balthazar", NIGHT_1, "Joseph", true),
      villageIdiotCheck("Balthazar", NIGHT_2, "Caspar", true),
    ],
  }),
  new Ravenkeeper({
    timing: "night_2",
    name: "Gabriel",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => game.registersAsRole("Balthazar", Drunk, "gabriel_ravenkeeper"),
      },
    ],
  }),
  new Investigator({
    name: "You",
    role: Baron,
    among: ["Mary", "Gabriel"],
    timing: "night_1",
  }),
  new VillageIdiot({
    name: "Caspar",
    infoClaims: [
      villageIdiotCheck("Caspar", NIGHT_1, "Mary", true),
      villageIdiotCheck("Caspar", NIGHT_2, "Joseph", true),
    ],
  }),
  new Saint({ name: "Joseph" }),
];
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
export const PUZZLE = {
  players: PLAYER_NAMES,
  characters: CHARACTERS,
  seating: PLAYER_NAMES,
} satisfies PuzzleSpec;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2);
  const drunkVillageIdiots = addVillageIdiotDrunkenness(game);
  applyClaims(game, PLAYERS, { info: addInfoClaim, context: drunkVillageIdiots });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
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

function villageIdiotCheck(player: string, timing: Timing, target: string, evil: boolean): InfoClaim {
  const nightNumber = timing === NIGHT_1 ? 1 : 2;
  return {
    timing: `night_${nightNumber}`,
    learned: (game) =>
      evil ? game.registersAsEvil(target, `${player}_${target}`) : game.registersAsGood(target, `${player}_${target}`),
  };
}

function addInfoClaim(game: BOTCModel, claim: AppliedInfoClaim): void {
  const drunkVillageIdiots = claim.context as ReadonlyMap<string, BoolVar>;
  const activeConditions = [game.actualIs(claim.player, claim.role), game.poisoned(claim.player, claim.timing).not()];
  if (claim.role === VillageIdiot) activeConditions.push((drunkVillageIdiots.get(claim.player) as BoolVar).not());
  game.addImplication(game.allOf(activeConditions, `${claim.player}_${claim.timing}_active_claim`), claim.learned);
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-20-the-three-wise-men.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    timing: "night_2",
    forcedRoles: [
      forcedRole("Demon", Imp, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
