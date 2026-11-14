import type { Clause, Literal, SatProblem } from "./sat";

export interface SimplifiedProblem {
  readonly problem: SatProblem;
  /** The projection literals in the simplified problem. Fixed literals are absent. */
  readonly projection: readonly Literal[];
  /** Give the true variables of the initial problem for a model of the simplified problem. */
  expand(model: ReadonlySet<number>): ReadonlySet<number>;
}

/**
 * Remove each variable that has a fixed value or that is equal to a different literal.
 * A unit clause fixes a variable. Two binary clauses (a, -b) and (-a, b) make a equal to b.
 * Each remaining clause keeps the origin of its initial clause.
 */
export function simplify(problem: SatProblem, projection: readonly number[]): SimplifiedProblem {
  const count = problem.variableCount;
  const TRUE = count + 1;
  // Each entry is the literal that replaces the variable. A root variable replaces itself.
  const replacement = Int32Array.from({ length: count + 2 }, (_, variable) => variable);
  const find = (literal: Literal): Literal => {
    let root = literal;
    while (replacement[Math.abs(root)] !== Math.abs(root)) root = Math.sign(root) * replacement[Math.abs(root)]!;
    if (root !== literal) replacement[Math.abs(literal)] = Math.sign(literal) * root;
    return root;
  };
  let consistent = true;
  let changed = true;
  const equate = (left: Literal, right: Literal): void => {
    const [a, b] = [find(left), find(right)];
    if (a === -b) consistent = false;
    if (Math.abs(a) === Math.abs(b)) return;
    // The constant has the largest number. Thus it is always the root.
    const [from, to] = Math.abs(a) < Math.abs(b) ? [a, b] : [b, a];
    replacement[Math.abs(from)] = Math.sign(from) * to;
    changed = true;
  };

  // The finalized arrays are frozen. A read from a copy is faster.
  let clauses: readonly Clause[] = problem.clauses.slice();
  let origins = problem.origins?.slice();
  const binaryKey = (a: Literal, b: Literal) => (Math.min(a, b) + TRUE) * (2 * TRUE + 1) + Math.max(a, b) + TRUE;
  // A unit clause is frequently later than the clauses that it simplifies. Find the unit clauses first.
  for (const clause of clauses) if (clause.length === 1) equate(clause[0]!, TRUE);
  // Each binary clause stays true after a replacement. Thus this set is correct for all passes.
  const binary = new Set<number>();
  for (let first = true; changed && consistent; first = false) {
    changed = false;
    const kept: Clause[] = [];
    const keptOrigins: NonNullable<typeof origins>[number][] = [];
    for (let index = 0; index < clauses.length; index += 1) {
      const clause = clauses[index]!;
      const literals: Literal[] = [];
      let satisfied = false;
      // After the first pass, a clause changes only if one of its variables has a replacement.
      let changes = first;
      for (let position = 0; !changes && position < clause.length; position += 1)
        changes = replacement[Math.abs(clause[position]!)] !== Math.abs(clause[position]!);
      if (changes) {
        for (let position = 0; !satisfied && position < clause.length; position += 1) {
          const literal = find(clause[position]!);
          if (literal === TRUE || literals.includes(-literal)) satisfied = true;
          else if (literal !== -TRUE && !literals.includes(literal)) literals.push(literal);
        }
        if (satisfied) continue;
        if (literals.length === 0) consistent = false;
        if (literals.length === 1) equate(literals[0]!, TRUE);
        if (literals.length < 2) continue;
        if (literals.length === 2) {
          if (binary.has(binaryKey(-literals[0]!, -literals[1]!))) {
            equate(literals[0]!, -literals[1]!);
            continue;
          }
          binary.add(binaryKey(literals[0]!, literals[1]!));
        }
      }
      kept.push(literals.length > 0 ? literals : clause);
      if (origins) keptOrigins.push(origins[index]!);
    }
    clauses = kept;
    if (origins) origins = keptOrigins;
  }
  if (!consistent) return { problem: { variableCount: 0, clauses: [[]] }, projection: [], expand: () => new Set() };

  // Give consecutive numbers to the remaining variables.
  const renumbered = new Int32Array(count + 1);
  let variableCount = 0;
  const renumber = (literal: Literal): Literal =>
    Math.sign(literal) * (renumbered[Math.abs(literal)] ||= ++variableCount);
  const compact = clauses.map((clause) => clause.map(renumber));
  const projected = new Set<Literal>();
  for (const variable of projection) if (Math.abs(find(variable)) !== TRUE) projected.add(renumber(find(variable)));
  return {
    problem: { variableCount, clauses: compact, origins },
    projection: [...projected],
    expand(model) {
      const expanded = new Set<number>();
      for (let variable = 1; variable <= count; variable += 1) {
        const literal = find(variable);
        const value = Math.abs(literal) === TRUE || model.has(renumbered[Math.abs(literal)]!);
        if (value === literal > 0) expanded.add(variable);
      }
      return expanded;
    },
  };
}
