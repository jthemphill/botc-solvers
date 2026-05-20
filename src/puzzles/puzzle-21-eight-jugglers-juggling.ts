import { CharacterType } from "../core";
import { forcedRole, printSolution } from "../display";
import { BOTCModel } from "../model";
import { KissatBackend, type SatBackend } from "../sat";
import { Drunk, Goblin, Juggler, Leviathan, playerNames, script } from "../characters";

export const PLAYERS = ["Tim", "Matt", "Olivia", "Oscar", "You", "Fraser", "Aoife", "Josh"];
export const PLAYER_NAMES = playerNames(PLAYERS);
export const CHARACTERS = script(Leviathan, Goblin, Drunk, Juggler);

export function buildModel(backend: SatBackend): BOTCModel {
  const game = new BOTCModel(PLAYER_NAMES, {
    characters: CHARACTERS,
    seating: PLAYER_NAMES,
    uniqueCharacters: false,
    backend,
  });
  game.setCharacterCount(Leviathan, 1);
  game.setCharacterCount(Goblin, 1);
  game.setCharacterCount(Drunk, 1);
  game.addExactlyN(
    PLAYER_NAMES.map((player) => game.hasCharacterType(player, CharacterType.Townsfolk)),
    5,
  );

  for (const player of PLAYER_NAMES) {
    game.setApparentRole(player, Juggler);
    game.setPossibleActualRoles(player, player === "You" ? [Juggler, Drunk] : [Juggler, Drunk, Leviathan, Goblin]);
  }

  addJugglerInfo(game, "Tim", { You: Leviathan, Josh: Juggler }, 0);
  addJugglerInfo(game, "Matt", { Josh: Goblin, Tim: Juggler }, 0);
  addJugglerInfo(game, "Olivia", { You: Juggler, Aoife: Drunk }, 2);
  addJugglerInfo(game, "Oscar", { Josh: Goblin, Matt: Juggler }, 0);
  addJugglerInfo(game, "You", { Matt: Goblin, Oscar: Goblin }, 0);
  addJugglerInfo(game, "Fraser", { Olivia: Juggler, Oscar: Drunk }, 1);
  addJugglerInfo(game, "Aoife", { Olivia: Leviathan, Oscar: Leviathan }, 0);
  addJugglerInfo(game, "Josh", { Tim: Goblin, Oscar: Juggler }, 1);

  return game;
}

export async function solve() {
  return buildModel(await KissatBackend.create()).solveAll();
}

function addJugglerInfo(
  game: BOTCModel,
  player: string,
  guesses: Parameters<typeof Juggler.learnsCorrectCount>[1],
  count: number,
): void {
  game.addTruthfulInfoClaim(player, Juggler, Juggler.learnsCorrectCount(game, guesses, count, `${player}_juggler`));
}

if (import.meta.main && process.argv[1]?.endsWith("puzzle-21-eight-jugglers-juggling.ts"))
  printSolution(await solve(), PLAYER_NAMES, {
    forcedRoles: [
      forcedRole("Demon", Leviathan, { includeRole: true }),
      forcedRole("Minion", Goblin, { includeRole: true }),
      forcedRole("Outsider", Drunk, { includeRole: true }),
    ],
  });
