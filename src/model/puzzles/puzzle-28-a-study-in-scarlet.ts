import { night } from "../model";
import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, type BOTCModel, type Timing } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel, type PuzzleSpec } from "../setup";
import {
  type AppliedInfoClaim,
  Chambermaid,
  Clockmaker,
  Drunk,
  Empath,
  FortuneTeller,
  Juggler,
  Librarian,
  NoDashii,
  Oracle,
  Pukka,
  ScarletWoman,
  Undertaker,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const NIGHT_1 = night(1);
export const NIGHT_2 = night(2);
export const NIGHT_3 = night(3);

export const PLAYERS = [
  new Clockmaker({
    name: "Adam",
    infoClaims: [{ timing: "night_1", learned: (game) => demonOppositeMinion(game) }],
  }),
  new Empath({
    name: "Oscar",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) => empathAliveNeighborCount(game, ["Adam", "Olivia"], 1, "oscar_empath_n1"),
      },
      {
        timing: "night_2",
        learned: (game) => empathAliveNeighborCount(game, ["Aoife", "Olivia"], 2, "oscar_empath_n2"),
      },
      {
        timing: "night_3",
        learned: (game) => empathAliveNeighborCount(game, ["Fraser", "Olivia"], 1, "oscar_empath_n3"),
      },
    ],
  }),
  new FortuneTeller({
    name: "Olivia",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game, context) =>
          fortuneTellerCheck(game, context as RedHerring, NIGHT_1, ["Olivia", "Sarah"], false, "olivia_ft_n1"),
      },
      {
        timing: "night_2",
        learned: (game, context) =>
          fortuneTellerCheck(game, context as RedHerring, NIGHT_2, ["Olivia", "Aoife"], false, "olivia_ft_n2"),
      },
      {
        timing: "night_3",
        learned: (game, context) =>
          fortuneTellerCheck(game, context as RedHerring, NIGHT_3, ["Matt", "Oscar"], false, "olivia_ft_n3"),
      },
    ],
  }),
  new Oracle({
    name: "Sarah",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => deadEvilCount(game, ["Adam", "You"], 1, "sarah_oracle_n2"),
      },
    ],
  }),
  new Chambermaid({
    name: "You",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) => chambermaidWokeCount(game, ["Adam", "Sarah"], 1, "you_chambermaid"),
      },
    ],
  }),
  new Juggler({
    name: "Matt",
    guesses: { Fraser: Undertaker, Oscar: NoDashii },
    correctCount: 2,
    timing: "night_1",
  }),
  new Undertaker({
    name: "Fraser",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) =>
          game.allOf([game.actualIs("Adam", Drunk), game.actualIs("Aoife", NoDashii)], "fraser_undertaker_claims"),
      },
    ],
  }),
  new Librarian({
    name: "Aoife",
    role: Drunk,
    among: ["Matt", "Adam"],
    timing: "night_1",
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Pukka,
  NoDashii,
  ScarletWoman,
  Drunk,
  Chambermaid,
  Clockmaker,
  Empath,
  FortuneTeller,
  Juggler,
  Librarian,
  Oracle,
  Undertaker,
);
export const DEMON_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Demon });
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const PUZZLE = { players: PLAYER_NAMES, characters: CHARACTERS, seating: PLAYER_NAMES } satisfies PuzzleSpec;

type RedHerring = ReadonlyMap<string, BoolVar>;

export function buildModel(backend: SatBackend): BOTCModel {
  const game = buildPuzzleModel(PUZZLE, backend);

  game.allowPoisonAt(NIGHT_1);
  game.allowPoisonAt(NIGHT_2);
  game.allowPoisonAt(NIGHT_3);
  game.addImplication(game.roleInPlay(Pukka), game.poisoned("You", NIGHT_1));
  game.addImplication(game.roleInPlay(Pukka), game.poisoned("Sarah", NIGHT_2));
  for (const player of PLAYER_NAMES) {
    if (player !== "You") game.addImplication(game.roleInPlay(Pukka), game.poisoned(player, NIGHT_1).not());
    if (player !== "Sarah") game.addImplication(game.roleInPlay(Pukka), game.poisoned(player, NIGHT_2).not());
    game.addImplication(game.roleInPlay(Pukka), game.poisoned(player, NIGHT_3).not());
    game.addImplication(game.roleInPlay(NoDashii), game.poisoned(player, NIGHT_1).not());
    game.addImplication(game.roleInPlay(NoDashii), game.poisoned(player, NIGHT_2).not());
    game.addImplication(game.roleInPlay(NoDashii), game.poisoned(player, NIGHT_3).not());
  }

  const redHerrings = addFortuneTellerRedHerring(game);
  applyClaims(game, PLAYERS, { info: addInfo, context: redHerrings });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addInfo(game: BOTCModel, claim: AppliedInfoClaim): void {
  const timing = claim.timing;
  const active = game.allOf(
    [
      game.actualIs(claim.player, claim.role),
      game.poisoned(claim.player, timing).not(),
      noDashiiPoisoned(game, claim.player, timing).not(),
    ],
    `${claim.player}_${timing}_active_info`,
  );
  game.addImplication(active, claim.learned);
}

function noDashiiPoisoned(game: BOTCModel, player: string, timing: Timing): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.flatMap((demon) => {
      const [left, right] = game.neighbors(demon);
      return player === left || player === right
        ? [
            game.allOf(
              [isNoDashiiAtTiming(game, demon, timing), game.hasCharacterType(player, CharacterType.Townsfolk)],
              `${player}_poisoned_by_no_dashii_${demon}`,
            ),
          ]
        : [];
    }),
    `${player}_poisoned_by_no_dashii`,
  );
}

function isNoDashiiAtTiming(game: BOTCModel, player: string, timing: Timing): BoolVar {
  const timingName = timing;
  if (timing === NIGHT_1) return game.actualIs(player, NoDashii);
  return game.anyOf(
    [
      player === "Adam" ? game.constantBool(false, `${player}_dead_${timingName}`) : game.actualIs(player, NoDashii),
      game.allOf(
        [game.actualIs("Adam", NoDashii), game.actualIs(player, ScarletWoman)],
        `${player}_sw_no_dashii_${timingName}`,
      ),
      timing === NIGHT_3
        ? game.allOf(
            [game.actualIs("Aoife", NoDashii), game.actualIs(player, ScarletWoman)],
            `${player}_sw_after_aoife_no_dashii`,
          )
        : game.constantBool(false, `${player}_no_aoife_sw_${timingName}`),
    ],
    `${player}_no_dashii_${timingName}`,
  );
}

function empathAliveNeighborCount(
  game: BOTCModel,
  aliveNeighbors: readonly string[],
  count: number,
  name: string,
): BoolVar {
  return game.boolSumEquals(
    aliveNeighbors.map((player) => game.registersAsEvil(player, name)),
    count,
    `${name}_alive_neighbor_count`,
  );
}

function deadEvilCount(game: BOTCModel, deadPlayers: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    deadPlayers.map((player) => game.isEvil(player)),
    count,
    name,
  );
}

function chambermaidWokeCount(game: BOTCModel, players: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    players.map((player) =>
      game.anyOf(
        [Pukka, NoDashii, Chambermaid, Clockmaker, Empath, FortuneTeller, Librarian].map((role) =>
          game.actualIs(player, role),
        ),
        `${name}_${player}_woke`,
      ),
    ),
    count,
    name,
  );
}

function demonOppositeMinion(game: BOTCModel): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((demon, index) =>
      game.allOf(
        [game.isDemon(demon), game.actualIs(PLAYER_NAMES[(index + 4) % PLAYER_NAMES.length] as string, ScarletWoman)],
        `${demon}_opposite_minion`,
      ),
    ),
    "demon_opposite_minion",
  );
}

function addFortuneTellerRedHerring(game: BOTCModel): RedHerring {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Olivia", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerCheck(
  game: BOTCModel,
  redHerrings: RedHerring,
  timing: Timing,
  players: readonly [string, string],
  yes: boolean,
  name: string,
): BoolVar {
  const either = game.anyOf(
    [
      ...players.map((player) => isDemonAtTiming(game, player, timing)),
      ...players.map((player) => redHerrings.get(player) as BoolVar),
    ],
    `${name}_yes`,
  );
  return yes ? either : game.not(either, `${name}_no`);
}

function isDemonAtTiming(game: BOTCModel, player: string, timing: Timing): BoolVar {
  const timingName = timing;
  if (timing === NIGHT_1) return game.isDemon(player);
  return game.anyOf(
    [
      player === "Adam" ? game.constantBool(false, `${player}_dead_demon_${timingName}`) : game.isDemon(player),
      game.allOf(
        [
          game.anyOf([game.actualIs("Adam", Pukka), game.actualIs("Adam", NoDashii)], "adam_starting_demon"),
          game.actualIs(player, ScarletWoman),
        ],
        `${player}_sw_demon_${timingName}`,
      ),
      timing === NIGHT_3
        ? game.allOf(
            [
              game.anyOf([game.actualIs("Aoife", Pukka), game.actualIs("Aoife", NoDashii)], "aoife_starting_demon"),
              game.actualIs(player, ScarletWoman),
            ],
            `${player}_sw_after_aoife_demon`,
          )
        : game.constantBool(false, `${player}_no_aoife_demon_${timingName}`),
    ],
    `${player}_demon_${timingName}`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-28-a-study-in-scarlet.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", DEMON_ROLES, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
      forcedRole("Outsider", Drunk, { includeRole: true }),
    ],
  });
