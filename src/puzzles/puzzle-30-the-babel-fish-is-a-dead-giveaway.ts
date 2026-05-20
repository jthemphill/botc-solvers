import { CharacterType, roleName } from "../core";
import { printSolution } from "../display";
import { type BoolVar, type BOTCModel, type World } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { buildPuzzleModel } from "../setup";
import {
  Artist,
  Atheist,
  Clockmaker,
  Drunk,
  Imp,
  Knight,
  Noble,
  Seamstress,
  Spy,
  applyClaims,
  playerNames,
  script,
} from "../characters";

export type GameSide = "left" | "right";

export interface Puzzle30Solution {
  readonly atheistGame: GameSide;
  readonly nonAtheistGame: GameSide;
  readonly world: World;
}

export const LEFT_PLAYERS = [
  new Seamstress({
    name: "Sarah",
    infoClaims: [(game) => sameAlignment(game, "Oli", "Callum", "sarah_seamstress")],
  }),
  new Artist({
    name: "Max",
    infoClaims: [(game) => game.registersAsRole("Erika", Drunk, "max_artist")],
  }),
  new Noble({
    name: "Erika",
    infoClaims: [(game) => evilRegisterCount(game, ["Lav", "Callum", "Sarah"], 1, "erika_noble")],
  }),
  new Clockmaker({
    name: "Lav",
    infoClaims: [(game) => demonOppositeMinion(game, "lav_clockmaker")],
  }),
  new Atheist({ name: "Oli" }),
  new Knight({
    name: "Callum",
    infoClaims: [(game) => noDemonAmong(game, ["Lav", "Max"], "callum_knight")],
  }),
];
export const RIGHT_PLAYERS = [
  new Clockmaker({
    name: "Ben",
    infoClaims: [(game) => demonOppositeMinion(game, "ben_clockmaker")],
  }),
  new Noble({
    name: "Owen",
    infoClaims: [(game) => evilRegisterCount(game, ["Lydia", "Louisa", "Shan"], 1, "owen_noble")],
  }),
  new Seamstress({
    name: "Lydia",
    infoClaims: [(game) => sameAlignment(game, "Finn", "Ben", "lydia_seamstress")],
  }),
  new Atheist({ name: "Finn" }),
  new Knight({
    name: "Louisa",
    infoClaims: [(game) => noDemonAmong(game, ["Lydia", "Shan"], "louisa_knight")],
  }),
  new Artist({
    name: "Shan",
    infoClaims: [(game) => game.registersAsRole("Louisa", Drunk, "shan_artist")],
  }),
];
export const CHARACTERS = script(Imp, Spy, Drunk, Artist, Atheist, Clockmaker, Knight, Noble, Seamstress);

export async function solve(): Promise<Puzzle30Solution[]> {
  const backend = await KissatBackend.create();
  const leftWorlds = await buildNonAtheistModel("left", backend).solveAll();
  const rightWorlds = await buildNonAtheistModel("right", backend).solveAll();
  return [
    ...leftWorlds.map((world) => ({ atheistGame: "right" as const, nonAtheistGame: "left" as const, world })),
    ...rightWorlds.map((world) => ({ atheistGame: "left" as const, nonAtheistGame: "right" as const, world })),
  ];
}

export function buildNonAtheistModel(side: GameSide, backend: SatBackend): BOTCModel {
  const players = playerNames(side === "left" ? LEFT_PLAYERS : RIGHT_PLAYERS);
  const game = buildPuzzleModel({ players, characters: CHARACTERS, seating: players }, backend);
  game.setCharacterCount(Atheist, 0);

  for (const role of [Artist, Clockmaker, Knight, Noble, Seamstress]) {
    game.addEnforcedAtMostN(
      players.map((player) => game.actualIs(player, role)),
      1,
      game.constantBool(true, `${side}_${roleName(role)}_unique`),
    );
  }

  applyClaims(game, side === "left" ? LEFT_PLAYERS : RIGHT_PLAYERS);
  return game;
}

function sameAlignment(game: BOTCModel, left: string, right: string, name: string): BoolVar {
  return game.anyOf(
    [
      game.allOf([game.registersAsGood(left, name), game.registersAsGood(right, name)], `${name}_both_good`),
      game.allOf([game.registersAsEvil(left, name), game.registersAsEvil(right, name)], `${name}_both_evil`),
    ],
    name,
  );
}

function evilRegisterCount(game: BOTCModel, players: readonly string[], count: number, name: string): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.registersAsEvil(player, name)),
    count,
    name,
  );
}

function noDemonAmong(game: BOTCModel, players: readonly string[], name: string): BoolVar {
  return game.boolSumEquals(
    players.map((player) => game.registersAsCharacterType(player, CharacterType.Demon, name)),
    0,
    name,
  );
}

function demonOppositeMinion(game: BOTCModel, name: string): BoolVar {
  const players = game.seating;
  return game.anyOf(
    players.map((demon, index) => {
      const opposite = players[(index + players.length / 2) % players.length] as string;
      return game.allOf(
        [
          game.registersAsCharacterType(demon, CharacterType.Demon, `${name}_${demon}`),
          game.registersAsCharacterType(opposite, CharacterType.Minion, `${name}_${opposite}`),
        ],
        `${name}_${demon}_opposite_${opposite}`,
      );
    }),
    name,
  );
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-30-the-babel-fish-is-a-dead-giveaway.ts")) {
  const solutions = await solve();
  console.log(`${solutions.length} satisfying paired solution(s)`);
  for (const [index, solution] of solutions.entries()) {
    console.log(`\nSolution ${index + 1}: ${solution.atheistGame} game is the Atheist game`);
    printSolution([solution.world], playerNames(solution.nonAtheistGame === "left" ? LEFT_PLAYERS : RIGHT_PLAYERS));
  }
}
