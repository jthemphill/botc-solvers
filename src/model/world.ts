import { roleName, type RoleRef } from "./core";
import { type ChoiceWitness } from "./actions";
import { type TraceWitness } from "./trace";
import { type Timing } from "./timing";
import { lit, type BoolLike, type BoolVar } from "./boolean";

export class World {
  constructor(
    readonly actual: ReadonlyMap<string, string>,
    readonly apparent: ReadonlyMap<string, string>,
    readonly poisoned: ReadonlySet<string>,
    readonly poisonedByTiming: ReadonlyMap<string, ReadonlySet<string>> = new Map(),
    readonly drunk: ReadonlySet<string> = new Set(),
    readonly drunkByTiming: ReadonlyMap<string, ReadonlySet<string>> = new Map(),
    readonly trace?: TraceWitness,
    readonly actions: readonly ChoiceWitness[] = [],
  ) {}

  holder(role: RoleRef): string | undefined {
    const roleRef = roleName(role);
    const holders = [...this.actual.entries()]
      .filter(([, actualRole]) => actualRole === roleRef)
      .map(([player]) => player);
    return holders.length === 1 ? holders[0] : undefined;
  }

  actualRole(player: string): string {
    const actual = this.actual.get(player);
    if (actual === undefined) throw new KeyError(`Unknown player: ${player}`);
    return actual;
  }

  isPoisoned(player: string, timing?: Timing): boolean {
    if (timing === undefined) return this.poisoned.has(player);
    return this.poisonedByTiming.get(timing)?.has(player) ?? false;
  }

  isDrunk(player: string, timing?: Timing): boolean {
    if (this.drunk.has(player)) return true;
    if (timing === undefined) return false;
    return this.drunkByTiming.get(timing)?.has(player) ?? false;
  }
}

export class KeyError extends Error {}

export function forcedRoleHolders(
  worlds: readonly World[],
  roles: readonly RoleRef[],
): Record<string, string | undefined> {
  const summary: Record<string, string | undefined> = {};
  for (const role of roles) {
    const roleRef = roleName(role);
    const holders = new Set(worlds.map((world) => world.holder(roleRef)));
    summary[roleRef] = holders.size === 1 ? [...holders][0] : undefined;
  }
  return summary;
}

export function flavorByTiming(
  model: ReadonlySet<number>,
  sourceMaps: readonly ReadonlyMap<string, readonly BoolLike[]>[],
  queryVars: ReadonlyMap<string, BoolVar>,
): Map<string, ReadonlySet<string>> {
  const satisfied = (value: BoolLike): boolean => {
    const literal = lit(value);
    return literal > 0 ? model.has(literal) : !model.has(-literal);
  };
  const keys = new Set([...sourceMaps.flatMap((sources) => [...sources.keys()]), ...queryVars.keys()]);
  const result = new Map<string, Set<string>>();
  for (const key of [...keys].sort()) {
    const [timing, player] = key.split("\u0000") as [string, string];
    let players = result.get(timing);
    if (players === undefined) result.set(timing, (players = new Set()));
    const queryVar = queryVars.get(key);
    const affected =
      (queryVar !== undefined && model.has(queryVar.id)) ||
      sourceMaps.some((sources) => (sources.get(key) ?? []).some(satisfied));
    if (affected) players.add(player);
  }
  return result;
}
