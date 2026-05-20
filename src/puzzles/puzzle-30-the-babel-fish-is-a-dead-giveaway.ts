import { CharacterType, type RoleRef, roleName } from "../core";
import { printSolution } from "../display";
import { type BoolLike, type BoolVar, BOTCModel, type World } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
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
  playerNames,
  script,
} from "../characters";

export type GameSide = "left" | "right";

export interface Puzzle30Solution {
  readonly atheistGame: GameSide;
  readonly nonAtheistGame: GameSide;
  readonly world: World;
}

export const LEFT_PLAYERS = ["Sarah", "Max", "Erika", "Lav", "Oli", "Callum"];
export const RIGHT_PLAYERS = ["Ben", "Owen", "Lydia", "Finn", "Louisa", "Shan"];
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
  const game = new BOTCModel(players, { characters: CHARACTERS, seating: players, backend });
  game.setCharacterCount(Imp, 1);
  game.setCharacterCount(Spy, 1);
  game.setCharacterCount(Drunk, 1);
  game.setCharacterCount(Atheist, 0);

  for (const role of [Artist, Clockmaker, Knight, Noble, Seamstress]) {
    game.addEnforcedAtMostN(
      players.map((player) => game.actualIs(player, role)),
      1,
      game.constantBool(true, `${side}_${roleName(role)}_unique`),
    );
  }

  if (side === "left") addLeftGame(game);
  else addRightGame(game);
  return game;
}

function addLeftGame(game: BOTCModel): void {
  addClaim(game, "Sarah", Seamstress);
  addClaim(game, "Callum", Knight);
  addAtheistClaim(game, "Oli");
  addClaim(game, "Lav", Clockmaker);
  addClaim(game, "Erika", Noble);
  addClaim(game, "Max", Artist);

  addInfo(game, "Sarah", Seamstress, sameAlignment(game, "Oli", "Callum", "sarah_seamstress"));
  addInfo(game, "Callum", Knight, noDemonAmong(game, ["Lav", "Max"], "callum_knight"));
  addInfo(game, "Lav", Clockmaker, demonOppositeMinion(game, "lav_clockmaker"));
  addInfo(game, "Erika", Noble, evilRegisterCount(game, ["Lav", "Callum", "Sarah"], 1, "erika_noble"));
  addInfo(game, "Max", Artist, game.registersAsRole("Erika", Drunk, "max_artist"));
}

function addRightGame(game: BOTCModel): void {
  addClaim(game, "Ben", Clockmaker);
  addClaim(game, "Owen", Noble);
  addClaim(game, "Lydia", Seamstress);
  addAtheistClaim(game, "Finn");
  addClaim(game, "Louisa", Knight);
  addClaim(game, "Shan", Artist);

  addInfo(game, "Ben", Clockmaker, demonOppositeMinion(game, "ben_clockmaker"));
  addInfo(game, "Owen", Noble, evilRegisterCount(game, ["Lydia", "Louisa", "Shan"], 1, "owen_noble"));
  addInfo(game, "Lydia", Seamstress, sameAlignment(game, "Finn", "Ben", "lydia_seamstress"));
  addInfo(game, "Louisa", Knight, noDemonAmong(game, ["Lydia", "Shan"], "louisa_knight"));
  addInfo(game, "Shan", Artist, game.registersAsRole("Louisa", Drunk, "shan_artist"));
}

function addClaim(game: BOTCModel, player: string, apparentRole: RoleRef): void {
  game.setApparentRole(player, apparentRole);
  game.setPossibleActualRoles(player, [apparentRole, Drunk, Imp, Spy]);
}

function addAtheistClaim(game: BOTCModel, player: string): void {
  game.setApparentRole(player, Atheist);
  game.setPossibleActualRoles(player, [Drunk, Imp, Spy]);
}

function addInfo(game: BOTCModel, player: string, role: RoleRef, info: BoolLike): void {
  game.addTruthfulInfoClaim(player, role, info);
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
    printSolution([solution.world], solution.nonAtheistGame === "left" ? LEFT_PLAYERS : RIGHT_PLAYERS);
  }
}
