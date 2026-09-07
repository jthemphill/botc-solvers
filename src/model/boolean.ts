import { atMostClauses } from "./cardinality";
import { type Clause, type Literal, type ConstraintOrigin, type SatProblem, negate } from "./sat";
import { slug, keyOf } from "./keys";

export class BoolVar {
  constructor(
    readonly id: number,
    readonly name: string,
  ) {}

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

  newBool(name: string): BoolVar {
    this.assertBuilding();
    this.variableCount += 1;
    return new BoolVar(this.variableCount, `${slug(name)}__${this.variableCount}`);
  }

  constantBool(value: boolean, name: string): BoolVar {
    const existing = value ? this.trueConstant : this.falseConstant;
    if (existing !== undefined) return existing;
    const result = this.newBool(name);
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

  private literalBool(literal: Literal, name: string): BoolVar {
    if (literal > 0) return new BoolVar(literal, name);
    const key = keyOf(["not", String(-literal)]);
    let cached = this.gateCache.get(key);
    if (cached === undefined) {
      cached = this.newBool(name);
      this.addClause([cached.not(), literal]);
      this.addClause([cached.lit, negate(literal)]);
      this.gateCache.set(key, cached);
    }
    return cached;
  }

  // Return the variable for an AND or OR gate with these inputs.
  // If an equivalent gate is available, use its variable.
  // The identity element is true for AND and false for OR.
  // Remove each input that has the value of the identity element.
  // An absorbing operand or a complementary pair gives a constant result.
  private gate(
    kind: string,
    values: readonly BoolLike[],
    name: string,
    identity: boolean,
    build: (literals: readonly Literal[], result: BoolVar) => void,
  ): BoolVar {
    const unique = new Set(values.map(lit));
    const literals: Literal[] = [];
    for (const literal of unique) {
      const constant = this.constantValueOf(literal);
      if (constant === identity) continue;
      if (constant === !identity || unique.has(-literal)) return this.constantBool(!identity, name);
      literals.push(literal);
    }
    literals.sort((left, right) => left - right);
    if (literals.length === 0) return this.constantBool(identity, name);
    if (literals.length === 1) return this.literalBool(literals[0] as Literal, name);
    const key = keyOf([kind, ...literals.map(String)]);
    let cached = this.gateCache.get(key);
    if (cached === undefined) {
      cached = this.newBool(name);
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

  boolSumEquals(values: readonly BoolLike[], count: number, name: string): BoolVar {
    const literals = values.map(lit).sort((left, right) => left - right);
    if (count < 0 || count > literals.length) return this.constantBool(false, name);
    if (literals.length === 0) return this.constantBool(true, name);
    if (literals.length === 1)
      return this.literalBool(count === 1 ? (literals[0] as Literal) : negate(literals[0] as Literal), name);
    const key = keyOf(["sum", String(count), ...literals.map(String)]);
    let cached = this.gateCache.get(key);
    if (cached === undefined) {
      cached = this.reifyExactCount(literals, count, name);
      this.gateCache.set(key, cached);
    }
    return cached;
  }

  allOf(values: readonly BoolLike[], name: string): BoolVar {
    return this.gate("all_of", values, name, true, (literals, result) => {
      for (const literal of literals) this.addClause([result.not(), literal]);
      this.addClause([result.lit, ...literals.map(negate)]);
    });
  }

  anyOf(values: readonly BoolLike[], name: string): BoolVar {
    return this.gate("any_of", values, name, false, (literals, result) => {
      this.addClause([result.not(), ...literals]);
      for (const literal of literals) this.addClause([result.lit, negate(literal)]);
    });
  }

  not(value: BoolLike, name: string): BoolVar {
    const literal = lit(value);
    const constant = this.constantValueOf(literal);
    if (constant !== undefined) return this.constantBool(!constant, name);
    return this.literalBool(negate(literal), name);
  }

  xor(left: BoolLike, right: BoolLike, name: string): BoolVar {
    return this.boolSumEquals([left, right], 1, name);
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
    return atMostClauses(literals, count, () => this.newBool("cardinality").lit);
  }

  private atLeastNClauses(literals: readonly Literal[], count: number): Clause[] {
    return this.atMostNClauses(literals.map(negate), literals.length - count);
  }

  private exactlyNClauses(literals: readonly Literal[], count: number): Clause[] {
    return [...this.atMostNClauses(literals, count), ...this.atLeastNClauses(literals, count)];
  }

  // Use a sequential counter to test if exactly `count` input literals are true.
  // Each row entry tests if at least `level` literals are true among the processed inputs.
  // Keep at most `count + 1` levels to limit the counter size.
  // Count each duplicate literal as a separate input.
  private reifyExactCount(literals: readonly Literal[], count: number, name: string): BoolVar {
    const maxLevel = Math.min(count + 1, literals.length);
    let row: BoolLike[] = [];
    for (let index = 0; index < literals.length; index += 1) {
      const literal = literals[index] as Literal;
      const levels = Math.min(index + 1, maxLevel);
      const next: BoolLike[] = [];
      for (let level = 1; level <= levels; level += 1) {
        const levelName = `${name}__ge_${level}_of_${index + 1}`;
        const carry: BoolLike = level === 1 ? literal : this.allOf([literal, row[level - 2] as BoolLike], levelName);
        next.push(level <= row.length ? this.anyOf([row[level - 1] as BoolLike, carry], levelName) : carry);
      }
      row = next;
    }
    const bounds: BoolLike[] = [];
    if (count > 0) bounds.push(row[count - 1] as BoolLike);
    if (count < literals.length) bounds.push(negate(lit(row[count] as BoolLike)));
    return this.allOf(bounds, name);
  }

  protected addCountAtMostCount(leftValues: readonly BoolLike[], rightValues: readonly BoolLike[]): void {
    this.assertBuilding();
    // Use the equivalent bound: |left| + |complement(right)| <= right.length.
    this.addAtMostN([...leftValues, ...rightValues.map((value) => negate(lit(value)))], rightValues.length);
  }

  finalize(): SatProblem {
    return (this.prepared ??= Object.freeze({
      variableCount: this.variableCount,
      clauses: Object.freeze(this.clauses.map((clause) => Object.freeze([...clause]))),
      origins: Object.freeze([...this.origins]),
    }));
  }
}
