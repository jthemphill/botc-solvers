import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel, type World } from "../model";
import { differentCharacterTypes } from "../predicates";
import { KissatBackend, type SatBackend } from "../sat";
import {
  type InfoClaim,
  Balloonist,
  Drunk,
  FortuneTeller,
  Investigator,
  Juggler,
  Leviathan,
  Librarian,
  Recluse,
  Saint,
  SnakeCharmer,
  Xaan,
  applyClaims,
  playerNames,
  roleNames,
  script,
} from "../characters";

export const PLAYERS = [
  new Balloonist({
    name: "Aoife",
    infoClaims: [
      nightInfo(2, "aoife_balloonist_n2", (game) => differentCharacterTypes(game, "Olivia", "Aoife")),
      nightInfo(3, "aoife_balloonist_n3", (game) => differentCharacterTypes(game, "You", "Aoife")),
    ],
  }),
  new Saint({ name: "Tim" }),
  new Investigator({
    name: "Olivia",
    infoClaims: [
      nightInfo(1, "olivia_investigator_n1", (game) =>
        Investigator.learnsRoleAmong(game, ["Fraser", "Aoife"], Xaan, "olivia_investigator"),
      ),
    ],
  }),
  new Recluse({ name: "Sarah" }),
  new Librarian({
    name: "You",
    infoClaims: [
      nightInfo(1, "you_librarian_n1", (game) =>
        Librarian.learnsRoleAmong(game, ["Aoife", "Tim"], Drunk, "you_librarian"),
      ),
    ],
  }),
  new Juggler({
    timing: "night_2",
    name: "Steph",
    infoClaims: [
      nightInfo(2, "steph_juggler_n2", (game) =>
        Juggler.learnsCorrectCount(
          game,
          {
            Fraser: Leviathan,
            Aoife: Balloonist,
            Tim: Xaan,
          },
          2,
          "steph_juggler",
        ),
      ),
    ],
  }),
  new SnakeCharmer({
    name: "Fraser",
    infoClaims: [
      nightInfo(1, "fraser_snake_charmer_n1", (game) => game.actualIs("Olivia", Leviathan).not()),
      nightInfo(2, "fraser_snake_charmer_n2", (game) => game.actualIs("Steph", Leviathan).not()),
      nightInfo(3, "fraser_snake_charmer_n3", (game) => game.actualIs("Aoife", Leviathan).not()),
    ],
  }),
  new FortuneTeller({
    name: "Dan",
    infoClaims: [
      nightInfo(1, "dan_ft_n1_info", (game, context) =>
        fortuneTellerCheck(game, (context as ClaimContext).redHerrings, ["Tim", "Sarah"], false, "dan_ft_n1"),
      ),
      nightInfo(2, "dan_ft_n2_info", (game, context) =>
        fortuneTellerCheck(game, (context as ClaimContext).redHerrings, ["Steph", "Aoife"], false, "dan_ft_n2"),
      ),
      nightInfo(3, "dan_ft_n3_info", (game, context) =>
        fortuneTellerCheck(game, (context as ClaimContext).redHerrings, ["Fraser", "Olivia"], false, "dan_ft_n3"),
      ),
    ],
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Leviathan,
  Xaan,
  Drunk,
  Saint,
  Recluse,
  Balloonist,
  FortuneTeller,
  Investigator,
  Juggler,
  Librarian,
  SnakeCharmer,
);
export const DEMON_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Demon });
export const MINION_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Minion });
export const OUTSIDER_ROLES = roleNames(CHARACTERS, { characterType: CharacterType.Outsider });

type Night = 1 | 2 | 3;
type XVars = Readonly<Record<Night, BoolVar>>;
type RedHerring = ReadonlyMap<string, BoolVar>;
interface ClaimContext {
  readonly x: XVars;
  readonly redHerrings: RedHerring;
}

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, backend });
  game.setCharacterCount(Leviathan, 1);
  game.setCharacterCount(Xaan, 1);
  for (const evilRole of [Leviathan, Xaan]) game.fixNotActual("You", evilRole);

  const x = addXBranches(game);
  const redHerrings = addFortuneTellerRedHerring(game);
  applyClaims(game, PLAYERS, { context: { x, redHerrings } });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addXBranches(game: BOTCModel): XVars {
  const x = {
    1: game.newBool("x_is_1"),
    2: game.newBool("x_is_2"),
    3: game.newBool("x_is_3"),
  } satisfies Record<Night, BoolVar>;
  game.addExactlyOne([x[1], x[2], x[3]]);
  const outsiders = PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider));
  game.addEnforcedExactlyN(outsiders, 1, x[1]);
  game.addEnforcedExactlyN(outsiders, 2, x[2]);
  game.addEnforcedExactlyN(outsiders, 3, x[3]);
  return x;
}

function nightInfo(night: Night, name: string, info: (game: BOTCModel, context: unknown) => BoolLike): InfoClaim {
  return {
    timing: `night_${night}`,
    learned: (game, context) => {
      const { x } = context as ClaimContext;
      return game.anyOf([x[night], info(game, context)], name);
    },
  };
}

function addFortuneTellerRedHerring(game: BOTCModel): RedHerring {
  const entries = PLAYER_NAMES.map((player) => [player, game.newBool(`${player}_fortune_teller_red_herring`)] as const);
  const redHerrings = new Map(entries);
  game.addEnforcedExactlyN(
    entries.map(([, variable]) => variable),
    1,
    game.actualIs("Dan", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerCheck(
  game: BOTCModel,
  redHerrings: RedHerring,
  players: readonly [string, string],
  yes: boolean,
  name: string,
): BoolVar {
  const either = game.anyOf(
    [
      ...players.map((player) => game.actualIs(player, Leviathan)),
      ...players.map((player) => redHerrings.get(player) as BoolVar),
    ],
    `${name}_yes`,
  );
  return yes ? either : game.not(either, `${name}_no`);
}

export function forcedX(worlds: readonly World[]): number | undefined {
  const values = new Set(worlds.map((world) => outsiderCount(world)));
  return values.size === 1 ? [...values][0] : undefined;
}

function outsiderCount(world: World): number {
  return PLAYER_NAMES.filter((player) => OUTSIDER_ROLES.includes(world.actualRole(player))).length;
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-18-x-and-the-city.ts")) {
  const worlds = await solve();
  printSolution(worlds, PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", DEMON_ROLES, { includeRole: true }),
      forcedRole("Minion", MINION_ROLES, { includeRole: true }),
    ],
  });
  console.log(`\nX: ${forcedX(worlds) ?? "not forced"}`);
}
