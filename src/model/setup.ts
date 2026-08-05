import { CharacterType, type RoleRef, roleName } from "./core";
import { BOTCModel, type BoolLike } from "./model";
import type { SatBackend } from "./sat";

const SETUP_TYPES = [
  CharacterType.Townsfolk,
  CharacterType.Outsider,
  CharacterType.Minion,
  CharacterType.Demon,
] as const;

export type StandardSetupCounts = Readonly<Record<(typeof SETUP_TYPES)[number], number>>;

export const STANDARD_SETUP_COUNTS = new Map<number, StandardSetupCounts>([
  [
    5,
    {
      [CharacterType.Townsfolk]: 3,
      [CharacterType.Outsider]: 0,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    6,
    {
      [CharacterType.Townsfolk]: 3,
      [CharacterType.Outsider]: 1,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    7,
    {
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 0,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    8,
    {
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 1,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    9,
    {
      [CharacterType.Townsfolk]: 5,
      [CharacterType.Outsider]: 2,
      [CharacterType.Minion]: 1,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    10,
    {
      [CharacterType.Townsfolk]: 7,
      [CharacterType.Outsider]: 0,
      [CharacterType.Minion]: 2,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    11,
    {
      [CharacterType.Townsfolk]: 7,
      [CharacterType.Outsider]: 1,
      [CharacterType.Minion]: 2,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    12,
    {
      [CharacterType.Townsfolk]: 7,
      [CharacterType.Outsider]: 2,
      [CharacterType.Minion]: 2,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    13,
    {
      [CharacterType.Townsfolk]: 9,
      [CharacterType.Outsider]: 0,
      [CharacterType.Minion]: 3,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    14,
    {
      [CharacterType.Townsfolk]: 9,
      [CharacterType.Outsider]: 1,
      [CharacterType.Minion]: 3,
      [CharacterType.Demon]: 1,
    },
  ],
  [
    15,
    {
      [CharacterType.Townsfolk]: 9,
      [CharacterType.Outsider]: 2,
      [CharacterType.Minion]: 3,
      [CharacterType.Demon]: 1,
    },
  ],
]);

interface SetupModifier {
  readonly roleName: string;
  readonly activeWhenInPlay: boolean;
  readonly deltas: readonly Partial<Record<CharacterType, number>>[];
}

const STANDARD_SETUP_MODIFIERS: readonly SetupModifier[] = [
  {
    roleName: "Baron",
    activeWhenInPlay: true,
    deltas: [
      {
        [CharacterType.Townsfolk]: -2,
        [CharacterType.Outsider]: 2,
      },
    ],
  },
  {
    roleName: "Fang Gu",
    activeWhenInPlay: true,
    deltas: [
      {
        [CharacterType.Townsfolk]: -1,
        [CharacterType.Outsider]: 1,
      },
    ],
  },
  {
    roleName: "Vigormortis",
    activeWhenInPlay: true,
    deltas: [
      {
        [CharacterType.Townsfolk]: 1,
        [CharacterType.Outsider]: -1,
      },
    ],
  },
  {
    roleName: "Godfather",
    activeWhenInPlay: true,
    deltas: [
      {
        [CharacterType.Townsfolk]: 1,
        [CharacterType.Outsider]: -1,
      },
      {
        [CharacterType.Townsfolk]: -1,
        [CharacterType.Outsider]: 1,
      },
    ],
  },
  {
    roleName: "Balloonist",
    activeWhenInPlay: false,
    deltas: [
      {
        [CharacterType.Townsfolk]: -1,
        [CharacterType.Outsider]: 1,
      },
    ],
  },
];

export interface PuzzleSpec {
  readonly players: readonly string[];
  readonly characters: readonly RoleRef[];
  readonly uniqueCharacters?: boolean;
  readonly setup?: "standard" | false;
}

export function buildPuzzleModel(spec: PuzzleSpec, backend: SatBackend): BOTCModel {
  const game = new BOTCModel(spec.players, {
    characters: spec.characters,
    uniqueCharacters: spec.uniqueCharacters,
    backend,
  });
  if ((spec.setup ?? "standard") === "standard") applyStandardSetup(game);
  return game;
}

export function standardSetupCounts(playerCount: number): StandardSetupCounts {
  const counts = STANDARD_SETUP_COUNTS.get(playerCount);
  if (counts === undefined) {
    throw new Error(`Standard setup is only defined for 5-15 players, received ${playerCount}.`);
  }
  return counts;
}

export function applyStandardSetup(game: BOTCModel): void {
  const baseCounts = standardSetupCounts(game.players.length);
  const scriptRoleNames = new Set([...game.characters.keys()]);
  const modifiers = STANDARD_SETUP_MODIFIERS.filter((modifier) => scriptRoleNames.has(modifier.roleName));
  if (scriptRoleNames.has("Marionette")) enforceMarionetteNeighborsDemon(game);

  const kazaliInPlay = scriptRoleNames.has("Kazali") ? game.roleInPlay("Kazali") : undefined;
  const xaanInPlay = scriptRoleNames.has("Xaan") ? game.roleInPlay("Xaan") : undefined;
  const lordOfTyphonInPlay = scriptRoleNames.has("Lord of Typhon") ? game.roleInPlay("Lord of Typhon") : undefined;
  const specialDemonConditions: BoolLike[] = [];
  if (kazaliInPlay !== undefined) specialDemonConditions.push(kazaliInPlay);
  if (xaanInPlay !== undefined) specialDemonConditions.push(xaanInPlay);
  if (lordOfTyphonInPlay !== undefined) specialDemonConditions.push(lordOfTyphonInPlay);
  const ordinarySetup =
    specialDemonConditions.length === 0
      ? undefined
      : game.allOf(
          specialDemonConditions.map((condition) => negateBoolLike(condition)),
          "standard_setup_without_special_demon",
        );

  applyStandardSetupBranches(game, baseCounts, modifiers, ordinarySetup);
  if (kazaliInPlay !== undefined) enforceVariableOutsiderSetup(game, baseCounts, kazaliInPlay);
  if (xaanInPlay !== undefined) enforceVariableOutsiderSetup(game, baseCounts, xaanInPlay);
  if (lordOfTyphonInPlay !== undefined) enforceLordOfTyphonSetup(game, baseCounts, lordOfTyphonInPlay);
}

function enforceVariableOutsiderSetup(game: BOTCModel, baseCounts: StandardSetupCounts, condition: BoolLike): void {
  const demonPlayers = game.players.map((player) => game.hasCharacterType(player, CharacterType.Demon));
  const minionPlayers = game.players.map((player) => game.hasCharacterType(player, CharacterType.Minion));

  game.addEnforcedExactlyN(demonPlayers, baseCounts[CharacterType.Demon], condition);
  game.addEnforcedExactlyN(minionPlayers, baseCounts[CharacterType.Minion], condition);
}

function applyStandardSetupBranches(
  game: BOTCModel,
  baseCounts: StandardSetupCounts,
  modifiers: readonly SetupModifier[],
  baseCondition?: BoolLike,
): void {
  if (modifiers.length === 0) {
    enforceSetupCounts(game, baseCounts, baseCondition);
    return;
  }

  const branchCount = 1 << modifiers.length;
  const activeVariables = new Map(
    modifiers.map((modifier) => [modifier.roleName, setupModifierActive(game, modifier)] as const),
  );
  for (let mask = 0; mask < branchCount; mask += 1) {
    const activeModifiers = modifiers.filter((_modifier, index) => (mask & (1 << index)) !== 0);
    const condition = game.allOf(
      [
        ...(baseCondition === undefined ? [] : [baseCondition]),
        ...modifiers.map((modifier, index) => {
          const active = activeVariables.get(modifier.roleName) as BoolLike;
          return (mask & (1 << index)) !== 0 ? active : negateBoolLike(active);
        }),
      ],
      `standard_setup_${activeModifiers.map((modifier) => roleName(modifier.roleName)).join("_") || "base"}`,
    );
    const countOptions = adjustedSetupCountOptions(baseCounts, activeModifiers).filter((counts) =>
      SETUP_TYPES.every((type) => counts[type] >= 0 && counts[type] <= game.players.length),
    );
    if (countOptions.length === 0) {
      game.addFalse(condition);
      continue;
    }
    if (countOptions.length === 1) {
      enforceSetupCounts(game, countOptions[0] as StandardSetupCounts, condition);
      continue;
    }
    game.addImplication(
      condition,
      game.anyOf(
        countOptions.map((counts, index) => setupCountsMatch(game, counts, `standard_setup_option_${mask}_${index}`)),
        `standard_setup_options_${mask}`,
      ),
    );
  }
}

function enforceLordOfTyphonSetup(game: BOTCModel, baseCounts: StandardSetupCounts, condition: BoolLike): void {
  const demonPlayers = game.players.map((player) => game.hasCharacterType(player, CharacterType.Demon));
  const minionPlayers = game.players.map((player) => game.hasCharacterType(player, CharacterType.Minion));
  const minionCount = baseCounts[CharacterType.Minion] + 1;

  game.addEnforcedExactlyN(demonPlayers, 1, condition);
  game.addEnforcedExactlyN(minionPlayers, minionCount, condition);
  enforceLordOfTyphonLine(game, minionCount, condition);
}

function enforceLordOfTyphonLine(game: BOTCModel, minionCount: number, condition: BoolLike): void {
  for (const [playerIndex, player] of game.players.entries()) {
    const playerIsLordOfTyphon = game.allOf(
      [condition, game.actualIs(player, "Lord of Typhon")],
      `${player}_lord_of_typhon_line_active`,
    );
    const lineOptions = Array.from({ length: minionCount - 1 }, (_, index) => index + 1).map((leftCount) => {
      const rightCount = minionCount - leftCount;
      const minionSeats = [
        ...Array.from(
          { length: leftCount },
          (_, offset) => game.players[(playerIndex - offset - 1 + game.players.length) % game.players.length] as string,
        ),
        ...Array.from(
          { length: rightCount },
          (_, offset) => game.players[(playerIndex + offset + 1) % game.players.length] as string,
        ),
      ];
      return game.allOf(
        minionSeats.map((minion) => game.isMinion(minion)),
        `${player}_lord_of_typhon_${leftCount}_left_${rightCount}_right`,
      );
    });
    game.addImplication(playerIsLordOfTyphon, game.anyOf(lineOptions, `${player}_lord_of_typhon_line`));
  }
}

function enforceMarionetteNeighborsDemon(game: BOTCModel): void {
  for (const player of game.players) {
    const [left, right] = game.neighbors(player);
    game.addImplication(
      game.actualIs(player, "Marionette"),
      game.anyOf([game.isDemon(left), game.isDemon(right)], `${player}_marionette_neighbors_demon`),
    );
  }
}

function setupModifierActive(game: BOTCModel, modifier: SetupModifier): BoolLike {
  const inPlay = game.roleInPlay(modifier.roleName);
  if (modifier.activeWhenInPlay) return inPlay;

  const active = game.newBool(`${modifier.roleName}_setup_modifier_active`);
  game.addImplication(active, inPlay);
  return active;
}

function negateBoolLike(value: BoolLike): BoolLike {
  return typeof value === "number" ? -value : value.not();
}

function adjustedSetupCountOptions(
  baseCounts: StandardSetupCounts,
  modifiers: readonly SetupModifier[],
): readonly StandardSetupCounts[] {
  let options: StandardSetupCounts[] = [{ ...baseCounts }];
  for (const modifier of modifiers) {
    options = options.flatMap((counts) =>
      modifier.deltas.map(
        (delta) =>
          Object.fromEntries(
            SETUP_TYPES.map((type) => [type, counts[type] + (delta[type] ?? 0)]),
          ) as unknown as StandardSetupCounts,
      ),
    );
  }
  return [...new Map(options.map((counts) => [SETUP_TYPES.map((type) => counts[type]).join(","), counts])).values()];
}

function setupCountsMatch(game: BOTCModel, counts: StandardSetupCounts, name: string): BoolLike {
  return game.allOf(
    SETUP_TYPES.map((type) =>
      game.boolSumEquals(
        game.players.map((player) => game.hasCharacterType(player, type)),
        counts[type],
        `${name}_${type}`,
      ),
    ),
    name,
  );
}

function enforceSetupCounts(game: BOTCModel, counts: StandardSetupCounts, condition?: BoolLike): void {
  for (const type of SETUP_TYPES) {
    const playersOfType = game.players.map((player) => game.hasCharacterType(player, type));
    if (condition === undefined) {
      game.addExactlyN(playersOfType, counts[type]);
    } else {
      game.addEnforcedExactlyN(playersOfType, counts[type], condition);
    }
  }
}
