import { night } from "../model";
import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { type BoolVar, BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import {
  Clockmaker,
  Drunk,
  Empath,
  FortuneTeller,
  Imp,
  Investigator,
  Librarian,
  LordOfTyphon,
  Poisoner,
  Ravenkeeper,
  Saint,
  Spy,
  Undertaker,
  applyClaims,
  playerNames,
  script,
} from "../characters";

export const NIGHT_1 = night(1);
export const NIGHT_2 = night(2);

const EVIL_ROLES = [Imp, LordOfTyphon, Poisoner, Spy] as const;

export const PLAYERS = [
  new Ravenkeeper({
    timing: "night_2",
    name: "Oscar",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => game.registersAsRole("Sula", Imp, "oscar_ravenkeeper_sula_imp"),
      },
    ],
  }),
  new Saint({ name: "Olivia" }),
  new Investigator({
    name: "Sarah",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) =>
          game.anyOf(
            [
              game.registersAsRole("Olivia", Spy, "sarah_investigator_olivia_spy"),
              game.registersAsRole("Jasmine", Spy, "sarah_investigator_jasmine_spy"),
            ],
            "sarah_investigator_spy",
          ),
      },
    ],
  }),
  new Empath({
    name: "Jasmine",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) => empathCount(game, ["Sarah", "You"], 2, "jasmine_empath_n1"),
      },
      {
        timing: "night_2",
        learned: (game) => empathCount(game, ["Sarah", "Tim"], 2, "jasmine_empath_n2"),
      },
    ],
  }),
  new Librarian({
    name: "You",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game) =>
          game.anyOf(
            [
              game.registersAsRole("Sula", Drunk, "you_librarian_sula_drunk"),
              game.registersAsRole("Oscar", Drunk, "you_librarian_oscar_drunk"),
            ],
            "you_librarian_drunk",
          ),
      },
    ],
  }),
  new Clockmaker({
    name: "Tim",
    infoClaims: [{ timing: "night_1", learned: (game) => demonSitsStepsFromMinion(game, 4) }],
  }),
  new Undertaker({
    name: "Sula",
    infoClaims: [
      {
        timing: "night_2",
        learned: (game) => game.registersAsRole("You", Spy, "sula_undertaker_you_spy"),
      },
    ],
  }),
  new FortuneTeller({
    name: "Fraser",
    infoClaims: [
      {
        timing: "night_1",
        learned: (game, context) =>
          game.allOf(
            [
              fortuneTellerNo(
                game,
                context as ReadonlyMap<string, BoolVar>,
                ["Sula", "Oscar"],
                "fraser_ft_sula_oscar_no",
              ),
              fortuneTellerNo(
                game,
                context as ReadonlyMap<string, BoolVar>,
                ["Sarah", "Jasmine"],
                "fraser_ft_sarah_jasmine_no",
              ),
            ],
            "fraser_fortune_teller_checks",
          ),
      },
    ],
  }),
];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(
  Imp,
  LordOfTyphon,
  Poisoner,
  Spy,
  Drunk,
  Saint,
  Clockmaker,
  Empath,
  FortuneTeller,
  Investigator,
  Librarian,
  Ravenkeeper,
  Undertaker,
);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, { characters: CHARACTERS, backend });
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.isDemon(player)),
    1,
  );
  game.addImplication(game.roleInPlay(Imp), impSetup(game));
  game.addImplication(game.roleInPlay(LordOfTyphon), lordOfTyphonSetup(game));
  game.addImplication(game.roleInPlay(Imp), outsiderCount(game, 1));
  game.fixNotActual("You", Imp);
  game.fixNotActual("You", LordOfTyphon);
  game.fixNotActual("Oscar", Imp);
  game.fixNotActual("Oscar", LordOfTyphon);
  for (const evilRole of EVIL_ROLES) game.fixNotActual("You", evilRole);

  game.addPoisonerEffect(NIGHT_1);
  game.addPoisonerEffect(NIGHT_2);

  const redHerrings = addFortuneTellerRedHerring(game);
  applyClaims(game, PLAYERS, { context: redHerrings });

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function impSetup(game: BOTCModel): BoolVar {
  return game.allOf(
    [
      game.boolSumEquals(
        PLAYER_NAMES.map((player) => game.isMinion(player)),
        1,
        "imp_minion_count_1",
      ),
      game.anyOf([game.roleInPlay(Poisoner), game.roleInPlay(Spy)], "imp_has_supported_minion"),
    ],
    "imp_setup",
  );
}

function lordOfTyphonSetup(game: BOTCModel): BoolVar {
  return game.allOf(
    [
      game.roleInPlay(Poisoner),
      game.roleInPlay(Spy),
      game.boolSumEquals(
        PLAYER_NAMES.map((player) => game.isMinion(player)),
        2,
        "lord_of_typhon_minion_count_2",
      ),
      lordOfTyphonSitsBetweenMinions(game),
    ],
    "lord_of_typhon_setup",
  );
}

function outsiderCount(game: BOTCModel, count: number): BoolVar {
  return game.boolSumEquals(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Outsider)),
    count,
    `outsider_count_${count}`,
  );
}

function lordOfTyphonSitsBetweenMinions(game: BOTCModel): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.map((player) => {
      const [left, right] = game.neighbors(player);
      return game.allOf(
        [game.actualIs(player, LordOfTyphon), game.isMinion(left), game.isMinion(right)],
        `${player}_lord_of_typhon_between_minions`,
      );
    }),
    "lord_of_typhon_between_minions",
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
    game.actualIs("Fraser", FortuneTeller),
  );
  for (const [player, redHerring] of entries) game.addImplication(redHerring, game.isGood(player));
  return redHerrings;
}

function fortuneTellerNo(
  game: BOTCModel,
  redHerrings: ReadonlyMap<string, BoolVar>,
  players: readonly [string, string],
  name: string,
): BoolVar {
  return game.not(
    game.anyOf(
      [
        ...players.map((player) => game.registersAsCharacterType(player, CharacterType.Demon, `${name}_${player}`)),
        ...players.map((player) => redHerrings.get(player) as BoolVar),
      ],
      `${name}_yes`,
    ),
    name,
  );
}

function demonSitsStepsFromMinion(game: BOTCModel, steps: number): BoolVar {
  return game.anyOf(
    PLAYER_NAMES.flatMap((demon, demonIndex) =>
      PLAYER_NAMES.flatMap((minion, minionIndex) => {
        const clockwise = (minionIndex - demonIndex + PLAYER_NAMES.length) % PLAYER_NAMES.length;
        const distance = Math.min(clockwise, PLAYER_NAMES.length - clockwise);
        return distance === steps
          ? [game.allOf([game.isDemon(demon), game.isMinion(minion)], `${demon}_${minion}_demon_${steps}_from_minion`)]
          : [];
      }),
    ),
    `demon_${steps}_steps_from_minion`,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-35-typhon-season.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", [Imp, LordOfTyphon], { includeRole: true }),
      forcedRole("Poisoner", Poisoner),
      forcedRole("Spy", Spy),
      forcedRole("Drunk", Drunk),
    ],
  });
