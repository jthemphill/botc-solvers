import { CharacterType } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import type { SerializableWorld } from "../worker/protocol";

export function actualRole(world: SerializableWorld, player: string): string | undefined {
  return world.actual.find(([name]) => name === player)?.[1];
}

export function apparentRole(world: SerializableWorld, player: string): string | undefined {
  return world.apparent.find(([name]) => name === player)?.[1];
}

export function roleCharacterType(role: string | undefined): CharacterType | undefined {
  return role === undefined ? undefined : ROLE_CLASSES.get(role)?.characterType;
}

export function isEvilRole(role: string | undefined): boolean {
  const type = roleCharacterType(role);
  return type === CharacterType.Minion || type === CharacterType.Demon;
}

export function isDemonRole(role: string | undefined): boolean {
  return roleCharacterType(role) === CharacterType.Demon;
}

/** Number of worlds in which each player is a Demon. Players with zero are omitted. */
export function demonWorldCounts(
  worlds: readonly SerializableWorld[],
  players: readonly string[],
): ReadonlyMap<string, number> {
  const counts = new Map<string, number>();
  for (const world of worlds) {
    for (const player of players) {
      if (isDemonRole(actualRole(world, player))) {
        counts.set(player, (counts.get(player) ?? 0) + 1);
      }
    }
  }
  return counts;
}

/** The player's actual role if it is the same in every world, else undefined. */
export function certainRole(worlds: readonly SerializableWorld[], player: string): string | undefined {
  if (worlds.length === 0) return undefined;
  const first = actualRole(worlds[0] as SerializableWorld, player);
  if (first === undefined) return undefined;
  return worlds.every((world) => actualRole(world, player) === first) ? first : undefined;
}

export interface WorldVerdict {
  readonly headline: string;
  readonly detail?: string;
}

export function worldVerdict(
  worlds: readonly SerializableWorld[],
  players: readonly string[],
  capped: boolean,
): WorldVerdict {
  if (worlds.length === 0) {
    return { headline: "No world fits", detail: "The claims contradict each other" };
  }
  const demonCounts = demonWorldCounts(worlds, players);
  const candidates = players.filter((player) => (demonCounts.get(player) ?? 0) > 0);
  if (worlds.length === 1) {
    const world = worlds[0] as SerializableWorld;
    const demon = candidates[0];
    const role = demon === undefined ? undefined : actualRole(world, demon);
    return {
      headline: "Solved",
      detail: demon === undefined ? "One world remains" : `${demon} is the ${role ?? "Demon"}`,
    };
  }
  const worldCount = capped ? `${worlds.length}+ worlds` : `${worlds.length} worlds`;
  if (candidates.length === 0) return { headline: worldCount };
  return {
    headline: worldCount,
    detail: `Demon: ${candidates
      .map((player) => `${player} in ${demonCounts.get(player)}`)
      .join(", ")} of ${worlds.length}`,
  };
}
