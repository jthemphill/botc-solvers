import { isTimelineDeathEvent, type PuzzleDoc, type TimelineEventDoc } from "../schema/puzzleDoc";
import { timingOrder, type Timing } from "../model/timing";

export function deathEventOrder(event: TimelineEventDoc): number {
  return timingOrder(event.timing as Timing) + 0.5;
}

export class TimelineFacts {
  readonly timings: readonly Timing[];
  readonly nights: readonly Timing[];
  readonly finalLiving: readonly string[];
  private readonly life = new Map<Timing, { dead: ReadonlySet<string>; living: readonly string[] }>();
  private readonly reports = new Map<string, Set<string>>();

  constructor(private readonly doc: PuzzleDoc) {
    this.timings = collectTimings(doc);
    const lastRound = Math.max(1, ...this.timings.map((timing) => Math.floor(timingOrder(timing) / 2)));
    this.nights = Array.from({ length: lastRound }, (_, index) => `night_${index + 1}` as Timing);
    for (const event of doc.timeline ?? []) {
      const key = `${event.type}:${event.timing}`;
      const players = this.reports.get(key) ?? new Set<string>();
      for (const player of event.players) players.add(player);
      this.reports.set(key, players);
    }
    const finalDead = this.deadBeforeOrder(Infinity);
    this.finalLiving = doc.players.filter((player) => !finalDead.has(player));
  }

  reportedPlayers(type: TimelineEventDoc["type"], timing: Timing): ReadonlySet<string> | undefined {
    return this.reports.get(`${type}:${timing}`);
  }

  nightDeaths(timing: Timing): ReadonlySet<string> {
    return this.reportedPlayers("nightDeath", timing) ?? new Set();
  }

  executions(timing: Timing): ReadonlySet<string> {
    return this.reportedPlayers("execution", timing) ?? new Set();
  }

  previousTiming(timing: Timing): Timing | undefined {
    return this.timings.filter((candidate) => timingOrder(candidate) < timingOrder(timing)).at(-1);
  }

  deadBefore(timing: Timing): ReadonlySet<string> {
    return this.lifeAt(timing).dead;
  }

  livingAt(timing: Timing): readonly string[] {
    return this.lifeAt(timing).living;
  }

  neighbors(player: string, dead: ReadonlySet<string>): [string, string] {
    const index = this.doc.players.indexOf(player);
    if (index === -1) throw new Error(`Unknown player '${player}'.`);
    return [-1, 1].map((direction) =>
      livingNeighborInDirection(this.doc.players, index, direction as -1 | 1, dead),
    ) as [string, string];
  }

  private lifeAt(timing: Timing): { dead: ReadonlySet<string>; living: readonly string[] } {
    let state = this.life.get(timing);
    if (state === undefined) {
      const dead = this.deadBeforeOrder(timingOrder(timing));
      state = { dead, living: this.doc.players.filter((player) => !dead.has(player)) };
      this.life.set(timing, state);
    }
    return state;
  }

  private deadBeforeOrder(order: number): Set<string> {
    const dead = new Set<string>();
    for (const event of this.doc.timeline ?? []) {
      if (deathEventOrder(event) >= order) continue;
      if (isTimelineDeathEvent(event)) {
        for (const player of event.players) dead.add(player);
      } else if (event.type === "resurrection") {
        for (const player of event.players) dead.delete(player);
      }
    }
    return dead;
  }
}

function collectTimings(doc: PuzzleDoc): readonly Timing[] {
  const timings = new Set<Timing>();
  const add = (value: unknown) => {
    if (typeof value === "string" && /^(night|day)_[1-9]\d*$/.test(value)) timings.add(value as Timing);
  };
  // Read phase values from the timing, roleTiming, and drunkTimings fields.
  const visit = (value: unknown): void => {
    if (Array.isArray(value)) {
      for (const item of value) visit(item);
      return;
    }
    if (typeof value !== "object" || value === null) return;
    for (const [key, child] of Object.entries(value)) {
      if (key === "timing" || key === "roleTiming") add(child);
      else if (key === "drunkTimings" && Array.isArray(child)) child.forEach(add);
      else if (typeof child === "object") visit(child);
    }
  };
  for (const claim of doc.claims) {
    const fields = claim as unknown as Record<string, unknown>;
    for (const key of ["checks", "counts", "malfunctions"]) {
      const entries = fields[key];
      if (Array.isArray(entries))
        entries.forEach((entry: { timing?: string }, index: number) =>
          add(entry.timing ?? claim.timing ?? `night_${index + 1}`),
        );
    }
    if (claim.type === "Juggler") add(claim.timing ?? "night_2");
  }
  visit(doc.claims);
  visit(doc.timeline);
  return [...timings].sort((left, right) => timingOrder(left) - timingOrder(right));
}

function livingNeighborInDirection(
  players: readonly string[],
  playerIndex: number,
  direction: -1 | 1,
  deadPlayers: ReadonlySet<string>,
): string {
  for (let offset = 1; offset < players.length; offset += 1) {
    const neighbor = players[(playerIndex + direction * offset + players.length) % players.length] as string;
    if (!deadPlayers.has(neighbor)) return neighbor;
  }
  throw new Error("Empath claims need at least one living neighbor in each direction.");
}
