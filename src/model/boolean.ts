import { type Clause, type Literal, type ConstraintOrigin, type SatProblem, negate } from "./sat";
import { keyOf } from "./keys";

/** A signed literal. A negative `id` is the negation of a variable. */
export class BoolVar {
  constructor(readonly id: Literal) {}

  not(): Literal {
    return -this.id;
  }

  get lit(): Literal {
    return this.id;
  }
}

export type BoolLike = BoolVar | Literal;
export function lit(value: BoolLike): Literal {
  return typeof value === "number" ? value : value.lit;
}

export class BooleanConstraints {
  protected prepared: SatProblem | undefined;
  private readonly origins: ConstraintOrigin[] = [];
  private origin: ConstraintOrigin = { kind: "rule", id: "model.core" };
  private variableCount = 0;
  private readonly clauses: Clause[] = [];
  private readonly gateCache = new Map<string, BoolVar>();
  private trueConstant: BoolVar | undefined;
  private falseConstant: BoolVar | undefined;

  newBool(): BoolVar {
    this.assertBuilding();
    this.variableCount += 1;
    return new BoolVar(this.variableCount);
  }

  constantBool(value: boolean): BoolVar {
    const existing = value ? this.trueConstant : this.falseConstant;
    if (existing !== undefined) return existing;
    const result = this.newBool();
    this.addClause([value ? result.lit : result.not()]);
    if (value) this.trueConstant = result;
    else this.falseConstant = result;
    return result;
  }

  private constantValueOf(literal: Literal): boolean | undefined {
    if (this.trueConstant !== undefined && Math.abs(literal) === this.trueConstant.id) return literal > 0;
    if (this.falseConstant !== undefined && Math.abs(literal) === this.falseConstant.id) return literal < 0;
    return undefined;
  }

  // Return the variable for an AND or OR gate with these inputs.
  // If an equivalent gate is available, use its variable.
  // The identity element is true for AND and false for OR.
  // Remove each input that has the value of the identity element.
  // An absorbing operand or a complementary pair gives a constant result.
  private gate(
    kind: string,
    values: readonly BoolLike[],
    identity: boolean,
    build: (literals: readonly Literal[], result: BoolVar) => void,
  ): BoolVar {
    const unique = new Set(values.map(lit));
    const literals: Literal[] = [];
    for (const literal of unique) {
      const constant = this.constantValueOf(literal);
      if (constant === identity) continue;
      if (constant === !identity || unique.has(-literal)) return this.constantBool(!identity);
      literals.push(literal);
    }
    literals.sort((left, right) => left - right);
    if (literals.length === 0) return this.constantBool(identity);
    if (literals.length === 1) return new BoolVar(literals[0] as Literal);
    const key = keyOf([kind, ...literals.map(String)]);
    let cached = this.gateCache.get(key);
    if (cached === undefined) {
      cached = this.newBool();
      build(literals, cached);
      this.gateCache.set(key, cached);
    }
    return cached;
  }

  addTruth(value: BoolLike): void {
    this.addClause([lit(value)]);
  }

  addFalse(value: BoolLike): void {
    this.addClause([negate(lit(value))]);
  }

  addImplication(condition: BoolLike, conclusion: BoolLike): void {
    this.addClause([negate(lit(condition)), lit(conclusion)]);
  }

  equate(left: BoolLike, right: BoolLike): void {
    this.addImplication(left, right);
    this.addImplication(right, left);
  }

  addExactlyOne(values: readonly BoolLike[]): void {
    this.addExactlyN(values, 1);
  }

  addExactlyN(values: readonly BoolLike[], count: number): void {
    this.addAtMostN(values, count);
    this.addAtLeastN(values, count);
  }

  addEnforcedExactlyN(values: readonly BoolLike[], count: number, condition: BoolLike): void {
    this.assertBuilding();
    for (const clause of this.exactlyNClauses(values.map(lit), count))
      this.addClause([negate(lit(condition)), ...clause]);
  }

  addEnforcedAtLeastN(values: readonly BoolLike[], count: number, condition: BoolLike): void {
    this.assertBuilding();
    for (const clause of this.atLeastNClauses(values.map(lit), count))
      this.addClause([negate(lit(condition)), ...clause]);
  }

  addEnforcedAtMostN(values: readonly BoolLike[], count: number, condition: BoolLike): void {
    this.assertBuilding();
    for (const clause of this.atMostNClauses(values.map(lit), count))
      this.addClause([negate(lit(condition)), ...clause]);
  }

  /** Each occurrence of a literal counts as a separate input. */
  boolSumEquals(values: readonly BoolLike[], count: number): BoolVar {
    const literals = values.map(lit).sort((left, right) => left - right);
    if (count < 0 || count > literals.length) return this.constantBool(false);
    const bounds: Literal[] = [];
    if (count > 0) bounds.push(this.atLeast(literals, count));
    if (count < literals.length) bounds.push(-this.atLeast(literals, count + 1));
    return this.allOf(bounds);
  }

  allOf(values: readonly BoolLike[]): BoolVar {
    return this.gate("all_of", values, true, (literals, result) => {
      for (const literal of literals) this.addClause([result.not(), literal]);
      this.addClause([result.lit, ...literals.map(negate)]);
    });
  }

  anyOf(values: readonly BoolLike[]): BoolVar {
    return this.gate("any_of", values, false, (literals, result) => {
      this.addClause([result.not(), ...literals]);
      for (const literal of literals) this.addClause([result.lit, negate(literal)]);
    });
  }

  not(value: BoolLike): BoolVar {
    const literal = lit(value);
    const constant = this.constantValueOf(literal);
    return constant === undefined ? new BoolVar(-literal) : this.constantBool(!constant);
  }

  xor(left: BoolLike, right: BoolLike): BoolVar {
    return this.boolSumEquals([left, right], 1);
  }

  withProvenance<T>(origin: ConstraintOrigin, operation: () => T): T {
    const previous = this.origin;
    this.origin = origin;
    try {
      return operation();
    } finally {
      this.origin = previous;
    }
  }

  protected assertBuilding(): void {
    if (this.prepared !== undefined)
      throw new Error("The model is finalized; build a new model to change facts or rules.");
  }

  protected addClause(clause: readonly Literal[]): void {
    this.assertBuilding();
    this.clauses.push([...clause]);
    this.origins.push(this.origin);
  }

  protected addAtMostN(values: readonly BoolLike[], count: number): void {
    this.assertBuilding();
    for (const clause of this.atMostNClauses(values.map(lit), count)) this.addClause(clause);
  }

  private addAtLeastN(values: readonly BoolLike[], count: number): void {
    this.assertBuilding();
    for (const clause of this.atLeastNClauses(values.map(lit), count)) this.addClause(clause);
  }

  private atMostNClauses(literals: readonly Literal[], count: number): Clause[] {
    if (!Number.isInteger(count)) throw new Error("Cardinality must be an integer.");
    if (count < 0) return [[]];
    if (count >= literals.length) return [];
    if (count === 0) return literals.map((literal) => [-literal]);
    // At least one input must be false.
    if (count === literals.length - 1) return [literals.map(negate)];
    if (count > 1) return [[-this.atLeast(literals, count + 1)]];
    // Use the pairwise method for an at-most-one constraint with up to six inputs.
    if (literals.length <= 6)
      return literals.flatMap((literal, index) => literals.slice(index + 1).map((other) => [-literal, -other]));
    // Give each input a different binary code. Two true inputs give two values to one bit.
    const bits = Array.from({ length: Math.ceil(Math.log2(literals.length)) }, () => this.newBool().lit);
    return literals.flatMap((literal, index) =>
      bits.map((bit, position) => [-literal, (index >> position) & 1 ? bit : -bit]),
    );
  }

  private atLeastNClauses(literals: readonly Literal[], count: number): Clause[] {
    // The complementary bound needs no counter for these counts.
    if (count <= 1 || count >= literals.length - 1)
      return this.atMostNClauses(literals.map(negate), literals.length - count);
    return [[this.atLeast(literals, count)]];
  }

  private exactlyNClauses(literals: readonly Literal[], count: number): Clause[] {
    return [...this.atMostNClauses(literals, count), ...this.atLeastNClauses(literals, count)];
  }

  // Give the literal that is true only if at least `count` inputs are true, where 1 <= count <= inputs.
  // Each counter cell uses the two cells for the inputs without the last input.
  // Constraints on the same inputs use the same cells.
  private atLeast(literals: readonly Literal[], count: number): Literal {
    if (count === 1) return this.anyOf(literals).lit;
    if (count === literals.length) return this.allOf(literals).lit;
    const key = keyOf(["at_least", String(count), ...literals.map(String)]);
    let cached = this.gateCache.get(key);
    if (cached === undefined) {
      const last = literals.at(-1) as Literal;
      const without = this.atLeast(literals.slice(0, -1), count);
      const withLast = this.atLeast(literals.slice(0, -1), count - 1);
      cached = this.newBool();
      this.addClause([cached.lit, -without]);
      this.addClause([cached.lit, -last, -withLast]);
      this.addClause([-cached.lit, without, last]);
      this.addClause([-cached.lit, without, withLast]);
      this.gateCache.set(key, cached);
    }
    return cached.lit;
  }

  protected addCountAtMostCount(leftValues: readonly BoolLike[], rightValues: readonly BoolLike[]): void {
    this.assertBuilding();
    // Use the equivalent bound: |left| + |complement(right)| <= right.length.
    this.addAtMostN([...leftValues, ...rightValues.map((value) => negate(lit(value)))], rightValues.length);
  }

  finalize(): SatProblem {
    return (this.prepared ??= { variableCount: this.variableCount, clauses: this.clauses, origins: this.origins });
  }
}
