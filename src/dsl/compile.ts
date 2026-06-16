import { CharacterType, type RoleClass } from "../model/core";
import { Chef } from "../model/characters";
import type { BoolLike, BoolVar, BOTCModel, Timing } from "../model/model";
import type { AstCall, AstNode, AstPath } from "./ast";
import { DslError, lex } from "./lex";
import { parse } from "./parse";
import type { Span } from "./tokens";

export interface CompileCtx {
  readonly players: readonly string[];
  readonly script: readonly string[];
  readonly nameRoot: string;
}

type DslValue =
  | { kind: "playerSet"; names: readonly string[]; span: Span }
  | { kind: "player"; name: string; span: Span }
  | { kind: "roleSet"; names: readonly string[]; span: Span }
  | { kind: "role"; name: string; span: Span }
  | { kind: "alignment"; value: "Good" | "Evil"; span: Span }
  | { kind: "type"; value: CharacterType; span: Span }
  | { kind: "playerRole"; player: string; span: Span }
  | { kind: "playerAlignment"; player: string; span: Span }
  | { kind: "playerType"; player: string; span: Span }
  | { kind: "bool"; value: BoolLike; span: Span }
  | { kind: "number"; value: number; span: Span };

const CHARACTER_TYPES: Record<string, CharacterType> = {
  Townsfolk: CharacterType.Townsfolk,
  Outsider: CharacterType.Outsider,
  Minion: CharacterType.Minion,
  Demon: CharacterType.Demon,
};

class Compiler {
  private counter = 0;

  constructor(
    private readonly game: BOTCModel,
    private readonly ctx: CompileCtx,
  ) {}

  private freshName(label: string): string {
    this.counter += 1;
    return `${this.ctx.nameRoot}_${label}_${this.counter}`;
  }

  compile(node: AstNode): BoolLike {
    const v = this.evalNode(node, new Map());
    if (v.kind !== "bool") throw new DslError(`Expression has type '${v.kind}', expected a boolean formula`, node.span);
    return v.value;
  }

  private evalNode(node: AstNode, env: ReadonlyMap<string, DslValue>): DslValue {
    switch (node.kind) {
      case "boollit":
        return {
          kind: "bool",
          value: this.game.constantBool(node.value, this.freshName(`lit_${node.value}`)),
          span: node.span,
        };
      case "number":
        return { kind: "number", value: node.value, span: node.span };
      case "path":
        return this.evalPath(node, env);
      case "setlit":
        return this.evalSetLit(
          node.elements.map((e) => this.evalNode(e, env)),
          node.span,
        );
      case "call":
        return this.evalCall(node, env);
      case "not": {
        const inner = this.expectBool(this.evalNode(node.inner, env));
        return { kind: "bool", value: this.game.not(inner.value, this.freshName("not")), span: node.span };
      }
      case "quant":
        return this.evalQuant(node, env);
      case "binop":
        return this.evalBinop(node, env);
    }
  }

  private evalPath(node: AstPath, env: ReadonlyMap<string, DslValue>): DslValue {
    const rootValue = this.resolveRoot(node.root, node.rootSpan, env);
    let cur = rootValue;
    let curSpan: Span = { start: node.rootSpan.start, end: node.rootSpan.end };
    for (const field of node.fields) {
      curSpan = { start: curSpan.start, end: field.span.end };
      cur = this.applyField(cur, field.name, field.span, curSpan);
    }
    return cur;
  }

  private resolveRoot(name: string, span: Span, env: ReadonlyMap<string, DslValue>): DslValue {
    const bound = env.get(name);
    if (bound !== undefined) return { ...bound, span };
    if (name === "players") return { kind: "playerSet", names: this.ctx.players, span };
    if (name === "Good" || name === "Evil") return { kind: "alignment", value: name, span };
    const type = CHARACTER_TYPES[name];
    if (type !== undefined) return { kind: "type", value: type, span };
    if (this.ctx.players.includes(name)) return { kind: "player", name, span };
    if (this.ctx.script.includes(name)) return { kind: "role", name, span };
    throw new DslError(
      `Unknown identifier '${name}'. Expected a player, role, 'players', 'Good'/'Evil', a character type, or a bound variable.`,
      span,
    );
  }

  private applyField(value: DslValue, field: string, fieldSpan: Span, fullSpan: Span): DslValue {
    if (value.kind === "player") {
      if (field === "left") {
        const [left] = this.game.neighbors(value.name);
        return { kind: "player", name: left, span: fullSpan };
      }
      if (field === "right") {
        const [, right] = this.game.neighbors(value.name);
        return { kind: "player", name: right, span: fullSpan };
      }
      if (field === "neighbors") {
        const [l, r] = this.game.neighbors(value.name);
        return { kind: "playerSet", names: [l, r], span: fullSpan };
      }
      if (field === "role") return { kind: "playerRole", player: value.name, span: fullSpan };
      if (field === "alignment") return { kind: "playerAlignment", player: value.name, span: fullSpan };
      if (field === "type") return { kind: "playerType", player: value.name, span: fullSpan };
      throw new DslError(`Unknown field '${field}' on a player`, fieldSpan);
    }
    throw new DslError(`Cannot apply '.${field}' to a ${value.kind}`, fieldSpan);
  }

  private evalSetLit(values: readonly DslValue[], span: Span): DslValue {
    if (values.length === 0) return { kind: "playerSet", names: [], span };
    const first = values[0] as DslValue;
    if (first.kind === "player") {
      const names: string[] = [];
      for (const v of values) {
        if (v.kind !== "player") throw new DslError(`Mixed-type set literal; expected a player`, v.span);
        if (!names.includes(v.name)) names.push(v.name);
      }
      return { kind: "playerSet", names, span };
    }
    if (first.kind === "role") {
      const names: string[] = [];
      for (const v of values) {
        if (v.kind !== "role") throw new DslError(`Mixed-type set literal; expected a role`, v.span);
        if (!names.includes(v.name)) names.push(v.name);
      }
      return { kind: "roleSet", names, span };
    }
    throw new DslError(`Set literals support only players or roles`, span);
  }

  private evalQuant(node: Extract<AstNode, { kind: "quant" }>, env: ReadonlyMap<string, DslValue>): DslValue {
    const set = this.evalNode(node.set, env);
    const atoms = setAtoms(set, node.set.span);
    const literals = atoms.elements.map((atom) => {
      const newEnv = new Map(env);
      newEnv.set(node.variable, atom);
      return this.expectBool(this.evalNode(node.body, newEnv)).value;
    });
    const label = `${node.quantifier}_${node.variable}`;
    let result: BoolLike;
    switch (node.quantifier) {
      case "some":
        result = this.game.anyOf(literals, this.freshName(label));
        break;
      case "all":
        result = this.game.allOf(literals, this.freshName(label));
        break;
      case "no":
        result = this.game.not(this.game.anyOf(literals, this.freshName(`${label}_any`)), this.freshName(label));
        break;
      case "one":
        result = this.game.boolSumEquals(literals, 1, this.freshName(label));
        break;
      case "lone":
        result = this.game.not(
          this.game.boolSumEquals(literals.length === 0 ? [] : literals, 2, this.freshName(`${label}_two`)),
          this.freshName(label),
        );
        break;
    }
    return { kind: "bool", value: result, span: node.span };
  }

  private evalBinop(node: Extract<AstNode, { kind: "binop" }>, env: ReadonlyMap<string, DslValue>): DslValue {
    const op = node.op;
    if (op === "and" || op === "or" || op === "implies") {
      const left = this.expectBool(this.evalNode(node.left, env));
      const right = this.expectBool(this.evalNode(node.right, env));
      if (op === "and")
        return {
          kind: "bool",
          value: this.game.allOf([left.value, right.value], this.freshName("and")),
          span: node.span,
        };
      if (op === "or")
        return {
          kind: "bool",
          value: this.game.anyOf([left.value, right.value], this.freshName("or")),
          span: node.span,
        };
      const notLeft = this.game.not(left.value, this.freshName("implies_lhs"));
      return {
        kind: "bool",
        value: this.game.anyOf([notLeft, right.value], this.freshName("implies")),
        span: node.span,
      };
    }
    if (op === "eq" || op === "neq") {
      const lhs = this.evalNode(node.left, env);
      const rhs = this.evalNode(node.right, env);
      const eq = this.compileEquality(lhs, rhs, node.span);
      if (op === "neq") return { kind: "bool", value: this.game.not(eq, this.freshName("neq")), span: node.span };
      return { kind: "bool", value: eq, span: node.span };
    }
    if (op === "in") {
      const lhs = this.evalNode(node.left, env);
      const rhs = this.evalNode(node.right, env);
      return { kind: "bool", value: this.compileMembership(lhs, rhs, node.span), span: node.span };
    }
    if (op === "plus") {
      const lhs = this.evalNode(node.left, env);
      const rhs = this.evalNode(node.right, env);
      if (lhs.kind === "player" && rhs.kind === "player") {
        const names = lhs.name === rhs.name ? [lhs.name] : [lhs.name, rhs.name];
        return { kind: "playerSet", names, span: node.span };
      }
      const a = setAtoms(lhs, node.left.span);
      const b = setAtoms(rhs, node.right.span);
      if (a.kind !== b.kind) throw new DslError(`Cannot union sets of different kinds`, node.span);
      const merged = [...a.elements];
      for (const el of b.elements) {
        const dup = merged.some((m) => sameAtom(m, el));
        if (!dup) merged.push(el);
      }
      return atomsToSet(merged, a.kind, node.span);
    }
    throw new DslError(`Operator '${op}' not supported here`, node.span);
  }

  private compileEquality(lhs: DslValue, rhs: DslValue, span: Span): BoolLike {
    const pair = orderPair(lhs, rhs);
    const a = pair[0];
    const b = pair[1];
    if (a.kind === "playerRole" && b.kind === "role") return this.game.actualIs(a.player, b.name);
    if (a.kind === "playerAlignment" && b.kind === "alignment")
      return b.value === "Evil" ? this.game.isEvil(a.player) : this.game.isGood(a.player);
    if (a.kind === "playerAlignment" && b.kind === "playerAlignment")
      return this.game.anyOf(
        [
          this.game.allOf([this.game.isGood(a.player), this.game.isGood(b.player)], this.freshName("both_good")),
          this.game.allOf([this.game.isEvil(a.player), this.game.isEvil(b.player)], this.freshName("both_evil")),
        ],
        this.freshName("same_alignment"),
      );
    if (a.kind === "playerType" && b.kind === "type") return this.game.hasCharacterType(a.player, b.value);
    if (a.kind === "playerType" && b.kind === "playerType")
      return this.game.anyOf(
        Object.values(CharacterType).map((type) =>
          this.game.allOf(
            [this.game.hasCharacterType(a.player, type), this.game.hasCharacterType(b.player, type)],
            this.freshName(`both_${type}`),
          ),
        ),
        this.freshName("same_type"),
      );
    if (a.kind === "player" && b.kind === "player")
      return this.game.constantBool(a.name === b.name, this.freshName("player_eq"));
    if (a.kind === "role" && b.kind === "role")
      return this.game.constantBool(a.name === b.name, this.freshName("role_eq"));
    if (a.kind === "alignment" && b.kind === "alignment")
      return this.game.constantBool(a.value === b.value, this.freshName("alignment_eq"));
    if (a.kind === "type" && b.kind === "type")
      return this.game.constantBool(a.value === b.value, this.freshName("type_eq"));
    throw new DslError(`Cannot compare ${lhs.kind} with ${rhs.kind}`, span);
  }

  private compileMembership(lhs: DslValue, rhs: DslValue, span: Span): BoolLike {
    if (lhs.kind === "player" && rhs.kind === "playerSet")
      return this.game.constantBool(rhs.names.includes(lhs.name), this.freshName("in_player"));
    if (lhs.kind === "role" && rhs.kind === "roleSet")
      return this.game.constantBool(rhs.names.includes(lhs.name), this.freshName("in_role"));
    throw new DslError(`'in' requires an atom on the left and a set on the right`, span);
  }

  private evalCall(node: AstCall, env: ReadonlyMap<string, DslValue>): DslValue {
    if (node.name === "role_count") {
      if (node.args.length < 3 || node.args.length % 2 !== 1)
        throw new DslError(`role_count() takes (n, player, role, ...)`, node.span);
      const countArg = node.args[0] as AstCall["args"][number];
      if (countArg.name !== undefined) throw new DslError(`role_count's first argument is positional`, countArg.span);
      const countVal = this.evalNode(countArg.value, env);
      if (countVal.kind !== "number") throw new DslError(`role_count expects a number first`, countArg.span);
      const literals: BoolLike[] = [];
      for (let index = 1; index < node.args.length; index += 2) {
        const playerArg = node.args[index] as AstCall["args"][number];
        const roleArg = node.args[index + 1] as AstCall["args"][number];
        if (playerArg.name !== undefined || roleArg.name !== undefined)
          throw new DslError(`role_count pair arguments are positional`, playerArg.span);
        const player = this.evalNode(playerArg.value, env);
        const role = this.evalNode(roleArg.value, env);
        if (player.kind !== "player") throw new DslError(`role_count expected a player`, player.span);
        if (role.kind !== "role") throw new DslError(`role_count expected a role`, role.span);
        literals.push(this.game.actualIs(player.name, role.name));
      }
      return {
        kind: "bool",
        value: this.game.boolSumEquals(literals, countVal.value, this.freshName(`role_count_${countVal.value}`)),
        span: node.span,
      };
    }
    if (node.name === "malfunctions") {
      if (node.args.length !== 2) throw new DslError(`malfunctions() takes (timing, n)`, node.span);
      const timingArg = node.args[0] as AstCall["args"][number];
      const countArg = node.args[1] as AstCall["args"][number];
      const timing = this.expectTimingArg(timingArg);
      const countVal = this.evalNode(countArg.value, env);
      if (countVal.kind !== "number") throw new DslError(`malfunctions expects a number second`, countArg.span);
      return {
        kind: "bool",
        value: this.game.malfunctionCountAt(timing, countVal.value, this.freshName(`malfunctions_${timing}`)),
        span: node.span,
      };
    }
    if (node.name === "registers_as") {
      if (node.args.length !== 2) throw new DslError(`registers_as() takes (player, role)`, node.span);
      const playerArg = node.args[0] as AstCall["args"][number];
      const roleArg = node.args[1] as AstCall["args"][number];
      if (playerArg.name !== undefined || roleArg.name !== undefined)
        throw new DslError(`registers_as arguments are positional`, node.span);
      const player = this.evalNode(playerArg.value, env);
      const role = this.evalNode(roleArg.value, env);
      if (player.kind !== "player") throw new DslError(`registers_as expected a player`, player.span);
      if (role.kind !== "role") throw new DslError(`registers_as expected a role`, role.span);
      return {
        kind: "bool",
        value: this.game.registersAsRole(player.name, role.name, this.freshName("registers_as")),
        span: node.span,
      };
    }
    if (node.name === "chef") {
      if (node.args.length === 0 || node.args.length > 2)
        throw new DslError(`chef() takes (n) or (n, registers: bool)`, node.span);
      const countArg = node.args[0] as AstCall["args"][number];
      if (countArg.name !== undefined) throw new DslError(`chef's first argument is positional`, countArg.span);
      const countVal = this.evalNode(countArg.value, env);
      if (countVal.kind !== "number") throw new DslError(`chef expects a number`, countArg.span);
      let registers = true;
      if (node.args.length === 2) {
        const second = node.args[1] as AstCall["args"][number];
        if (second.name !== "registers")
          throw new DslError(`chef's second argument must be 'registers: <bool>'`, second.span);
        if (second.value.kind !== "boollit")
          throw new DslError(`'registers' must be a literal true/false`, second.value.span);
        registers = second.value.value;
      }
      const name = this.freshName(`chef_${countVal.value}_${registers ? "reg" : "act"}`);
      const bv = Chef.learnsCount(this.game, countVal.value, name, { registers });
      return { kind: "bool", value: bv, span: node.span };
    }
    throw new DslError(`Unknown function '${node.name}'`, node.nameSpan);
  }

  private expectTimingArg(arg: AstCall["args"][number]): Timing {
    if (arg.name !== undefined) throw new DslError(`Timing argument is positional`, arg.span);
    const value = arg.value;
    if (value.kind !== "path" || value.fields.length > 0) throw new DslError(`Expected timing identifier`, arg.span);
    if (!/^(night|day)_[1-9][0-9]*$/.test(value.root)) throw new DslError(`Expected timing identifier`, arg.span);
    return value.root as Timing;
  }

  private expectBool(v: DslValue): { kind: "bool"; value: BoolLike; span: Span } {
    if (v.kind === "bool") return v;
    throw new DslError(`Expected a boolean formula, got ${v.kind}`, v.span);
  }
}

type AtomBundle =
  | { kind: "player"; elements: readonly (DslValue & { kind: "player" })[] }
  | { kind: "role"; elements: readonly (DslValue & { kind: "role" })[] };

function setAtoms(value: DslValue, span: Span): AtomBundle {
  if (value.kind === "playerSet")
    return { kind: "player", elements: value.names.map((n) => ({ kind: "player", name: n, span })) };
  if (value.kind === "player") return { kind: "player", elements: [value] };
  if (value.kind === "roleSet")
    return { kind: "role", elements: value.names.map((n) => ({ kind: "role", name: n, span })) };
  if (value.kind === "role") return { kind: "role", elements: [value] };
  throw new DslError(`Expected a set, got ${value.kind}`, span);
}

function atomsToSet(atoms: readonly DslValue[], kind: "player" | "role", span: Span): DslValue {
  const names = atoms.map((a) => (a as { name: string }).name);
  return kind === "player" ? { kind: "playerSet", names, span } : { kind: "roleSet", names, span };
}

function sameAtom(a: DslValue, b: DslValue): boolean {
  if (a.kind === "player" && b.kind === "player") return a.name === b.name;
  if (a.kind === "role" && b.kind === "role") return a.name === b.name;
  return false;
}

function orderPair(a: DslValue, b: DslValue): readonly [DslValue, DslValue] {
  const fieldKinds = new Set(["playerRole", "playerAlignment", "playerType"]);
  if (fieldKinds.has(a.kind)) return [a, b];
  if (fieldKinds.has(b.kind)) return [b, a];
  return [a, b];
}

export function compile(src: string, game: BOTCModel, ctx: CompileCtx): BoolLike {
  const tokens = lex(src);
  const ast = parse(tokens);
  return new Compiler(game, ctx).compile(ast);
}
