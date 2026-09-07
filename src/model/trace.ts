import { timingOrder } from "./timing";
import type { BoolLike, BoolVar, BOTCModel, Timing } from "./model";

export interface CharacterTransition {
  readonly player: string;
  readonly character: string;
  readonly timing: Timing;
  readonly active: BoolLike;
  readonly rule: string;
}

export interface CharacterSnapshot {
  readonly timing: Timing;
  readonly characters: Readonly<Record<string, string>>;
}

export interface TraceWitness {
  readonly initial: Readonly<Record<string, string>>;
  readonly transitions: readonly Omit<CharacterTransition, "active">[];
  readonly snapshots: readonly CharacterSnapshot[];
}

/**
 * The trace contains each player's character at each phase boundary.
 * Each transition replaces the character and keeps the player's alignment.
 * A query with `before = true` reads the character before the phase boundary.
 */
export class CharacterTrace {
  private readonly transitions: CharacterTransition[] = [];
  private readonly queries = new Map<
    string,
    { player: string; character: string; timing: Timing; before: boolean; variable: BoolVar }
  >();
  private closed = false;

  constructor(private readonly game: BOTCModel) {}

  replace(change: CharacterTransition): void {
    if (this.closed) throw new Error("Cannot change a finalized character trace.");
    this.game.actualIs(change.player, change.character); // Examine the player and character references.
    timingOrder(change.timing);
    this.transitions.push(change);
  }

  at(player: string, character: string, timing?: Timing, before = false): BoolVar {
    if (timing === undefined) return this.game.actualIs(player, character);
    this.game.actualIs(player, character);
    const key = JSON.stringify([player, character, timing, before]);
    let query = this.queries.get(key);
    if (!query) {
      if (this.closed) throw new Error("Declare temporal queries before finalizing the model.");
      query = {
        player,
        character,
        timing,
        before,
        variable: this.game.newBool(`${player}_${character}_${timing}_${before ? "before" : "after"}`),
      };
      this.queries.set(key, query);
    }
    return query.variable;
  }

  /** After all transitions are available, examine the interval for character changes. */
  retainedThrough(player: string, character: string, from: Timing, through: Timing): BoolLike {
    const interruptions = this.transitions.filter(
      (change) =>
        change.player === player &&
        change.character !== character &&
        timingOrder(change.timing) >= timingOrder(from) &&
        timingOrder(change.timing) <= timingOrder(through),
    );
    return this.game
      .anyOf(
        interruptions.map((change) => change.active),
        "source_character_lost",
      )
      .not();
  }

  finalize(): void {
    if (this.closed) return;
    // Make a full snapshot for each necessary phase boundary.
    const timings = new Set([...this.queries.values()].map((query) => query.timing));
    for (const transition of this.transitions) timings.add(transition.timing);
    for (const timing of timings)
      for (const player of this.game.players) {
        for (const character of this.game.characters.keys()) this.at(player, character, timing);
      }
    const groups = new Map<string, CharacterTransition[]>();
    for (const transition of this.transitions) {
      const key = JSON.stringify([transition.player, transition.timing]);
      groups.set(key, [...(groups.get(key) ?? []), transition]);
    }
    for (const group of groups.values()) {
      // Put the causes that give the same character in one group.
      const byCharacter = [...new Set(group.map((change) => change.character))].map((character) =>
        this.game.anyOf(
          group.filter((change) => change.character === character).map((change) => change.active),
          "transition_result",
        ),
      );
      this.game.addEnforcedAtMostN(byCharacter, 1, this.game.constantBool(true, "one_character_transition"));
    }
    for (const query of this.queries.values()) {
      let state: BoolLike = this.game.actualIs(query.player, query.character);
      const changes = [...groups.values()]
        .filter((group) => {
          const change = group[0] as CharacterTransition;
          return (
            change.player === query.player &&
            (query.before
              ? timingOrder(change.timing) < timingOrder(query.timing)
              : timingOrder(change.timing) <= timingOrder(query.timing))
          );
        })
        .sort((a, b) => timingOrder(a[0]!.timing) - timingOrder(b[0]!.timing));
      for (const group of changes) {
        const changed = this.game.anyOf(
          group.map((change) => change.active),
          "character_changed",
        );
        const becomes = this.game.anyOf(
          group.filter((change) => change.character === query.character).map((change) => change.active),
          "becomes_character",
        );
        state = this.game.anyOf(
          [becomes, this.game.allOf([state, changed.not()], "character_persists")],
          "character_state",
        );
      }
      this.game.equate(query.variable, state);
    }
    this.closed = true;
  }

  decode(model: ReadonlySet<number>, initial: ReadonlyMap<string, string>): TraceWitness {
    const trueIn = (value: BoolLike) =>
      typeof value === "number" ? model.has(Math.abs(value)) === value > 0 : model.has(value.id);
    const timings = [
      ...new Set([...this.queries.values()].filter((query) => !query.before).map((query) => query.timing)),
    ].sort((a, b) => timingOrder(a) - timingOrder(b));
    return {
      initial: Object.fromEntries(initial),
      transitions: this.transitions.filter((change) => trueIn(change.active)).map(({ active: _, ...change }) => change),
      snapshots: timings.map((timing) => ({
        timing,
        characters: Object.fromEntries(
          this.game.players.map((player) => {
            const matches = [...this.queries.values()].filter(
              (query) => !query.before && query.player === player && query.timing === timing && trueIn(query.variable),
            );
            if (matches.length !== 1) throw new Error(`Expected one character for ${player} at ${timing}.`);
            return [player, matches[0]!.character];
          }),
        ),
      })),
    };
  }
}

/** Compare each snapshot with the initial characters and active transitions. */
export function validateTraceWitness(witness: TraceWitness): readonly string[] {
  const errors: string[] = [];
  for (const snapshot of witness.snapshots) {
    const expected = { ...witness.initial };
    const changes = [...witness.transitions]
      .filter((change) => timingOrder(change.timing) <= timingOrder(snapshot.timing))
      .sort((a, b) => timingOrder(a.timing) - timingOrder(b.timing));
    const atBoundary = new Map<string, string>();
    for (const change of changes) {
      const key = JSON.stringify([change.player, change.timing]);
      const prior = atBoundary.get(key);
      if (prior !== undefined && prior !== change.character)
        errors.push(`Conflicting changes for ${change.player} at ${change.timing}.`);
      atBoundary.set(key, change.character);
      if (!(change.player in expected)) errors.push(`Unknown transition player ${change.player}.`);
      expected[change.player] = change.character;
    }
    if (Object.keys(snapshot.characters).length !== Object.keys(expected).length)
      errors.push(`Incomplete snapshot at ${snapshot.timing}.`);
    for (const [player, character] of Object.entries(expected)) {
      if (snapshot.characters[player] !== character)
        errors.push(`Character does not persist for ${player} at ${snapshot.timing}.`);
    }
  }
  return errors;
}
