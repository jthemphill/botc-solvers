import type { BoolLike, BOTCModel, Timing } from "./model";

export interface ChoiceAction {
  readonly rule: string;
  readonly actor: string;
  readonly timing: Timing;
  readonly active: BoolLike;
  readonly count: number;
  readonly choices: ReadonlyMap<string, BoolLike>;
}

/** Make choices for an action from its candidate list and specified count. */
export function choose(
  game: BOTCModel,
  action: Omit<ChoiceAction, "choices">,
  candidates: readonly string[],
): ChoiceAction {
  const choices = new Map(
    candidates.map((candidate) => [
      candidate,
      game.newBool(`${action.rule}_${action.actor}_${action.timing}_${candidate}`),
    ]),
  );
  for (const selected of choices.values()) game.addImplication(selected, action.active);
  game.addEnforcedExactlyN([...choices.values()], action.count, action.active);
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
  if (action.selected.length !== (action.active ? action.count : 0)) return [`Wrong choice count for ${action.rule}.`];
  if (new Set(action.selected).size !== action.selected.length) return [`Duplicate choice for ${action.rule}.`];
  if (action.selected.some((candidate) => !action.candidates.includes(candidate)))
    return [`Illegal target for ${action.rule}.`];
  return [];
}
