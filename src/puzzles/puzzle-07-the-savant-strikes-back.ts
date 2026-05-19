import { CharacterType, type RoleRef, roleName } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Dreamer,
  Drunk,
  FortuneTeller,
  Goblin,
  Investigator,
  Juggler,
  Leviathan,
  Mutant,
  Savant,
  Shugenja,
  VillageIdiot,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const PLAYERS = [
  new Juggler({ name: "Anna", guesses: { You: Savant, Tim: VillageIdiot }, correctCount: 1 }),
  new Shugenja({ name: "Aoife", evilDirection: "anticlockwise" }),
  new Dreamer({ name: "Steph" }),
  new VillageIdiot({
    name: "Tim",
    checks: [
      { player: "Anna", good: true },
      { player: "Sarah", good: true },
      { player: "You", good: true },
    ],
  }),
  new Savant({ name: "You" }),
  new VillageIdiot({
    name: "Fraser",
    checks: [
      { player: "Sarah", good: true },
      { player: "Aoife", good: true },
      { player: "You", good: true },
    ],
  }),
  new FortuneTeller({ name: "Sarah" }),
  new Investigator({ name: "Oscar", role: Goblin, among: ["Fraser", "Steph"] }),
];

export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Leviathan,
  Goblin,
  Mutant,
  Drunk,
  Dreamer,
  FortuneTeller,
  Investigator,
  Juggler,
  Savant,
  Shugenja,
  VillageIdiot,
);

export const RED_HERRING = "red_herring";
export const DRUNK_VILLAGE_IDIOT = "drunk_village_idiot";

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, {
    characters: CHARACTERS,
    seating: PLAYER_NAMES,
    uniqueCharacters: false,
    backend,
  });
  enforceUniqueRolesExceptVillageIdiot(game);
  game.setCharacterCount(Leviathan, 1);
  game.setCharacterCount(Goblin, 1);
  game.setCharacterCount(Mutant, 1);
  game.setCharacterCount(Drunk, 0);
  game.fixActual("You", Savant);

  for (const claim of PLAYERS)
    game.addRoleClaim({ player: claim.name, apparentRole: claim }, { extraPossibleActualRoles: [Mutant] });

  const redHerrings = addFortuneTellerRedHerring(game);
  const drunkVillageIdiots = addVillageIdiotDrunkenness(game);

  for (const claim of PLAYERS) {
    if (claim instanceof Dreamer) {
      addInfoClaim(
        game,
        claim.name,
        Dreamer,
        game.allOf(
          [
            Dreamer.learnsOneOf(game, "Sarah", [FortuneTeller, Leviathan], "steph_dreamer_sarah"),
            Dreamer.learnsOneOf(game, "You", [Savant, Goblin], "steph_dreamer_you"),
            Dreamer.learnsOneOf(game, "Fraser", [Mutant, Goblin], "steph_dreamer_fraser"),
          ],
          "steph_dreamer_all_checks",
        ),
      );
    } else if (claim instanceof FortuneTeller) {
      addInfoClaim(
        game,
        claim.name,
        FortuneTeller,
        game.allOf(
          [
            fortuneTellerLearnsCheck(game, redHerrings, "Oscar", "Aoife", false, "sarah_ft_oscar_aoife"),
            fortuneTellerLearnsCheck(game, redHerrings, "You", "Sarah", true, "sarah_ft_you_sarah"),
            fortuneTellerLearnsCheck(game, redHerrings, "Fraser", "Tim", false, "sarah_ft_fraser_tim"),
          ],
          "sarah_fortune_teller_checks",
        ),
      );
    } else if (claim instanceof Savant) {
      addInfoClaim(game, claim.name, Savant, savantInfo(game, redHerrings, drunkVillageIdiots));
    } else if (claim instanceof VillageIdiot) {
      const learned = claim.learnedInfo(game);
      if (learned !== undefined)
        addVillageIdiotInfoClaim(game, claim.name, learned, drunkVillageIdiots.get(claim.name));
    } else {
      const learned = claim.learnedInfo(game);
      if (learned !== undefined) addInfoClaim(game, claim.name, claim, learned);
    }
  }

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

function addFortuneTellerRedHerring(game: BOTCModel): ReadonlyMap<string, BoolVar> {
  const redHerrings = new Map(
    PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_${RED_HERRING}`)] as const),
  );
  for (const [player, redHerring] of redHerrings) game.addImplication(redHerring, game.isGood(player));
  const fortuneTellerInPlay = game.roleInPlay(FortuneTeller);
  game.addEnforcedExactlyN([...redHerrings.values()], 1, fortuneTellerInPlay);
  game.addEnforcedExactlyN([...redHerrings.values()], 0, fortuneTellerInPlay.not());
  return redHerrings;
}

function addVillageIdiotDrunkenness(game: BOTCModel): ReadonlyMap<string, BoolVar> {
  const drunkVillageIdiots = new Map(
    ["Tim", "Fraser"].map((player) => [player, game.newBool(`${player}_${DRUNK_VILLAGE_IDIOT}`)] as const),
  );
  for (const [player, drunkVillageIdiot] of drunkVillageIdiots)
    game.addImplication(drunkVillageIdiot, game.actualIs(player, VillageIdiot));
  const bothVillageIdiots = game.allOf(
    ["Tim", "Fraser"].map((player) => game.actualIs(player, VillageIdiot)),
    "tim_and_fraser_village_idiots",
  );
  game.addEnforcedExactlyN([...drunkVillageIdiots.values()], 1, bothVillageIdiots);
  game.addEnforcedExactlyN([...drunkVillageIdiots.values()], 0, bothVillageIdiots.not());
  return drunkVillageIdiots;
}

function addInfoClaim(game: BOTCModel, player: string, apparentRole: RoleRef, learned: BoolLike): void {
  game.addTruthfulInfoClaim(player, apparentRole, learned);
}

function addVillageIdiotInfoClaim(
  game: BOTCModel,
  player: string,
  learned: BoolLike,
  drunkVillageIdiot: BoolVar | undefined,
): void {
  if (drunkVillageIdiot === undefined) {
    game.addTruthfulInfoClaim(player, VillageIdiot, learned);
    return;
  }
  const active = game.allOf(
    [game.actualIs(player, VillageIdiot), game.poisoned(player).not(), drunkVillageIdiot.not()],
    `${player}_sober_village_idiot`,
  );
  game.addImplication(active, learned);
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
      game.actualIs(left, Leviathan),
      game.actualIs(right, Leviathan),
      redHerrings.get(left) as BoolVar,
      redHerrings.get(right) as BoolVar,
    ],
    `${name}_either_demon_or_red_herring`,
  );
  return yes ? either : game.not(either, `${name}_neither_demon_nor_red_herring`);
}

function savantInfo(
  game: BOTCModel,
  redHerrings: ReadonlyMap<string, BoolVar>,
  drunkVillageIdiots: ReadonlyMap<string, BoolVar>,
): BoolVar {
  return game.allOf(
    [
      Savant.learnsExactlyOne(
        game,
        [
          game.boolSumEquals(
            ["Fraser", "Anna", "Steph"].map((player) => game.isEvil(player)),
            1,
            "savant_statement_1_evil_count",
          ),
          leviathanSitsSpacesFromGoblin(game, 3),
        ],
        "savant_statement_1",
      ),
      Savant.learnsExactlyOne(
        game,
        [redHerrings.get("Sarah") as BoolVar, drunkVillageIdiots.get("Fraser") as BoolVar],
        "savant_statement_2",
      ),
      Savant.learnsExactlyOne(
        game,
        [
          game.boolSumEquals(
            [game.roleInPlay(Juggler).not(), game.roleInPlay(Shugenja).not(), game.roleInPlay(VillageIdiot).not()],
            1,
            "savant_statement_3_role_not_in_play_count",
          ),
          game.boolSumEquals(
            ["Oscar", "Anna", "Tim"].map((player) => game.hasCharacterType(player, CharacterType.Townsfolk)),
            2,
            "savant_statement_3_townsfolk_count",
          ),
        ],
        "savant_statement_3",
      ),
    ],
    "you_savant_all_statements",
  );
}

function leviathanSitsSpacesFromGoblin(game: BOTCModel, spaces: number): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.flatMap((left, leftIndex) =>
      PLAYER_NAMES.flatMap((right, rightIndex) => {
        if (left === right) return [];
        const clockwise = (rightIndex - leftIndex + PLAYER_NAMES.length) % PLAYER_NAMES.length;
        const distance = Math.min(clockwise, PLAYER_NAMES.length - clockwise);
        return distance === spaces
          ? [
              game.allOf(
                [game.actualIs(left, Leviathan), game.actualIs(right, Goblin)],
                `${left}_${right}_leviathan_${spaces}_from_goblin`,
              ),
            ]
          : [];
      }),
    ),
    `leviathan_${spaces}_spaces_from_goblin`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-07-the-savant-strikes-back.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Leviathan, { includeRole: true }),
      forcedRole("Minion", Goblin, { includeRole: true }),
    ],
  });
