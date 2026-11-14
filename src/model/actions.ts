import { type BooleanConstraints, type BoolVar } from "./boolean";
import type { BoolLike, BOTCModel, Timing } from "./model";

/**
 * One selection from a list of candidates.
 * An action with `ability` is a choice of players that the actor makes at night with that character's ability.
 */
export interface ChoiceAction {
  readonly rule: string;
  readonly actor: string;
  readonly timing: Timing;
  readonly active: BoolLike;
  /** The largest number of selections while the action is active. */
  readonly count: number;
  /** The smallest number of selections while the action is active. The default is `count`. */
  readonly minCount?: number;
  readonly choices: ReadonlyMap<string, BoolLike>;
  readonly ability?: string;
}

export function constrainSelection(
  game: BooleanConstraints,
  choices: readonly BoolLike[],
  count: number,
  active: BoolLike,
): void {
  for (const selected of choices) game.addImplication(selected, active);
  game.addEnforcedExactlyN(choices, count, active);
}

export function select(
  game: BooleanConstraints,
  candidates: readonly string[],
  active: BoolLike,
  count: number,
): ReadonlyMap<string, BoolVar> {
  const choices = new Map(candidates.map((candidate) => [candidate, game.newBool()]));
  constrainSelection(game, [...choices.values()], count, active);
  return choices;
}

/** Make choices for an action from its candidate list and specified count. */
export function choose(
  game: BOTCModel,
  action: Omit<ChoiceAction, "choices">,
  candidates: readonly string[],
): ChoiceAction {
  const choices = select(game, candidates, action.active, action.count);
  const result = { ...action, choices };
  game.registerChoiceAction(result);
  return result;
}

export interface ChoiceWitness {
  readonly rule: string;
  readonly actor: string;
  readonly timing: Timing;
  readonly active: boolean;
  readonly count: number;
  readonly minCount?: number;
  readonly candidates: readonly string[];
  readonly selected: readonly string[];
}

/** Do a check of the action time, specified count, and selected targets in the witness. */
export function validateChoiceWitness(action: ChoiceWitness): readonly string[] {
  const required =
    action.rule === "Shabaloth:targets"
      ? 2
      : /^(Pit-Hag|Cerenovus):(player|character)$/.test(action.rule)
        ? 1
        : action.count;
  if (action.count !== required) return [`Incorrect rule cardinality for ${action.rule}.`];
  if (
    action.active &&
    action.timing === "night_1" &&
    (action.rule.startsWith("Pit-Hag:") || action.rule.startsWith("Shabaloth:"))
  )
    return [`${action.rule} cannot act on the first night.`];
  const least = action.active ? (action.minCount ?? action.count) : 0;
  const most = action.active ? action.count : 0;
  if (action.selected.length < least || action.selected.length > most)
    return [`Wrong choice count for ${action.rule}.`];
  if (new Set(action.selected).size !== action.selected.length) return [`Duplicate choice for ${action.rule}.`];
  if (action.selected.some((candidate) => !action.candidates.includes(candidate)))
    return [`Illegal target for ${action.rule}.`];
  return [];
}
