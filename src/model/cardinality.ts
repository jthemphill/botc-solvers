import type { Clause, Literal } from "./sat";

/**
 * This sequential counter uses the Sinz method.
 * Each signed literal counts once for each occurrence in the input.
 * The counter has its own auxiliary variables.
 * A guard on each clause controls the full constraint.
 */
export function atMostClauses(inputs: readonly Literal[], count: number, fresh: () => Literal): Clause[] {
  if (!Number.isInteger(count)) throw new Error("Cardinality must be an integer.");
  if (count < 0) return [[]];
  if (count >= inputs.length) return [];
  if (count === 0) return inputs.map((input) => [-input]);
  // At least one input must be false.
  if (count === inputs.length - 1) return [inputs.map((input) => -input)];
  // Use the pairwise method for an at-most-one constraint with up to six inputs.
  if (count === 1 && inputs.length <= 6) {
    return inputs.flatMap((input, i) => inputs.slice(i + 1).map((other) => [-input, -other]));
  }
  const clauses: Clause[] = [];
  let previous: Literal[] = [];
  for (let i = 0; i < inputs.length; i++) {
    const input = inputs[i] as Literal;
    if (previous.length === count) clauses.push([-input, -(previous[count - 1] as Literal)]);
    if (i === inputs.length - 1) break;
    const row = Array.from({ length: Math.min(i + 1, count) }, fresh);
    clauses.push([-input, row[0] as Literal]);
    for (let level = 0; level < row.length; level++) {
      if (level < previous.length) clauses.push([-(previous[level] as Literal), row[level] as Literal]);
      if (level > 0) clauses.push([-input, -(previous[level - 1] as Literal), row[level] as Literal]);
    }
    previous = row;
  }
  return clauses;
}
