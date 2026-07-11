import { CharacterType, type RoleClass } from "../model/core";
import { Chef } from "../model/characters";
import type { BoolLike, BoolVar, BOTCModel, Timing } from "../model/model";
import { roleByName } from "../model/roleRegistry";
import type { AstCall, AstJoin, AstNode, AstPath } from "./ast";
import { DslError, lex } from "./lex";
import { parse } from "./parse";
import type { Span } from "./tokens";

export interface CompileCtx {
  readonly players: readonly string[];
  readonly script: readonly string[];
  readonly nameRoot: string;
}

type AtomKind = "player" | "role" | "type" | "alignment";
type AlignmentName = "Good" | "Evil";

type DslValue =
  | { kind: "playerSet"; names: readonly string[]; span: Span }
  | { kind: "player"; name: string; span: Span }
  | { kind: "roleSet"; names: readonly string[]; span: Span }
  | { kind: "role"; name: string; span: Span }
  | { kind: "typeSet"; values: readonly CharacterType[]; span: Span }
  | { kind: "alignmentSet"; values: readonly AlignmentName[]; span: Span }
  | { kind: "dynamicSet"; atomKind: AtomKind; elements: readonly SetElement[]; span: Span }
  | { kind: "cardinality"; literals: readonly BoolLike[]; span: Span }
  | { kind: "alignment"; value: AlignmentName; span: Span }
  | { kind: "type"; value: CharacterType; span: Span }
  | { kind: "playerRole"; player: string; span: Span }
  | { kind: "playerAlignment"; player: string; span: Span }
  | { kind: "playerType"; player: string; span: Span }
  | { kind: "bool"; value: BoolLike; span: Span }
  | { kind: "number"; value: number; span: Span };

type SetAtom = DslValue & ({ kind: "player" } | { kind: "role" } | { kind: "type" } | { kind: "alignment" });

interface SetElement {
  readonly atom: SetAtom;
  readonly present: BoolLike;
}

type PlayerSetElement = SetElement & { readonly atom: Extract<SetAtom, { kind: "player" }> };

const CHARACTER_TYPES: Record<string, CharacterType> = {
  Townsfolk: CharacterType.Townsfolk,
  Outsider: CharacterType.Outsider,
  Minion: CharacterType.Minion,
  Demon: CharacterType.Demon,
};

const ALL_CHARACTER_TYPES: readonly CharacterType[] = [
  CharacterType.Townsfolk,
  CharacterType.Outsider,
  CharacterType.Minion,
  CharacterType.Demon,
];

const ROLE_SET_TYPES: Readonly<Record<string, CharacterType>> = {
  townsfolk: CharacterType.Townsfolk,
  outsiders: CharacterType.Outsider,
  minions: CharacterType.Minion,
  demons: CharacterType.Demon,
};

const ALIGNMENTS: readonly AlignmentName[] = ["Good", "Evil"];

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
      case "join":
        return this.evalJoin(node, env);
      case "setlit":
        return this.evalSetLit(
          node.elements.map((e) => this.evalNode(e, env)),
          node.span,
        );
      case "comprehension":
        return this.evalComprehension(node, env);
      case "cardinality":
        return {
          kind: "cardinality",
          literals: this.setElements(this.evalNode(node.set, env), node.set.span).elements.map(
            (entry) => entry.present,
          ),
          span: node.span,
        };
      case "call":
        return this.evalCall(node, env);
      case "not": {
        const inner = this.expectBool(this.evalNode(node.inner, env));
        return { kind: "bool", value: this.game.not(inner.value, this.freshName("not")), span: node.span };
      }
      case "quant":
        return this.evalQuant(node, env);
      case "multiplicity":
        return this.evalMultiplicity(node, env);
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

  private evalJoin(node: AstJoin, env: ReadonlyMap<string, DslValue>): DslValue {
    const left = this.evalNode(node.left, env);
    return this.applyField(left, node.field, node.fieldSpan, node.span);
  }

  private resolveRoot(name: string, span: Span, env: ReadonlyMap<string, DslValue>): DslValue {
    const bound = env.get(name);
    if (bound !== undefined) return { ...bound, span };
    if (name === "players") return { kind: "playerSet", names: this.ctx.players, span };
    const roleSetType = ROLE_SET_TYPES[name];
    if (roleSetType !== undefined) {
      return {
        kind: "roleSet",
        names: this.ctx.script.filter((role) => roleByName(role).characterType === roleSetType),
        span,
      };
    }
    if (name === "Good" || name === "Evil") return { kind: "alignment", value: name, span };
    const type = CHARACTER_TYPES[name];
    if (type !== undefined) return { kind: "type", value: type, span };
    if (this.ctx.players.includes(name)) return { kind: "player", name, span };
    if (this.ctx.script.includes(name)) return { kind: "role", name, span };
    throw new DslError(
      `Unknown identifier '${name}'. Expected a player, role, static player/role set, 'Good'/'Evil', a character type, or a bound variable.`,
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
    if (value.kind === "playerSet" || (value.kind === "dynamicSet" && value.atomKind === "player")) {
      return this.applyPlayerSetField(value, field, fieldSpan, fullSpan);
    }
    throw new DslError(`Cannot apply '.${field}' to a ${value.kind}`, fieldSpan);
  }

  private applyPlayerSetField(value: DslValue, field: string, fieldSpan: Span, fullSpan: Span): DslValue {
    const source = this.setElements(value, value.span);
    if (source.kind !== "player") throw new DslError(`Cannot apply '.${field}' to a ${value.kind}`, fieldSpan);
    const playerEntries: readonly PlayerSetElement[] = source.elements.map((entry) => {
      if (entry.atom.kind !== "player") throw new DslError(`Cannot apply '.${field}' to a ${value.kind}`, fieldSpan);
      return entry as PlayerSetElement;
    });

    if (field === "left" || field === "right" || field === "neighbors") {
      const elements = playerEntries.flatMap((entry) => {
        const player = entry.atom.name;
        const [left, right] = this.game.neighbors(player);
        const names = field === "left" ? [left] : field === "right" ? [right] : [left, right];
        return names.map((name) => ({
          atom: { kind: "player" as const, name, span: fullSpan },
          present: entry.present,
        }));
      });
      return { kind: "dynamicSet", atomKind: "player", elements: this.mergeElements(elements), span: fullSpan };
    }

    if (field === "role") {
      const elements = playerEntries.flatMap((entry) =>
        this.ctx.script.map((name) => ({
          atom: { kind: "role" as const, name, span: fullSpan },
          present: this.game.allOf(
            [entry.present, this.game.actualIs(entry.atom.name, name)],
            this.freshName("join_role"),
          ),
        })),
      );
      return { kind: "dynamicSet", atomKind: "role", elements: this.mergeElements(elements), span: fullSpan };
    }

    if (field === "type") {
      const elements = playerEntries.flatMap((entry) =>
        ALL_CHARACTER_TYPES.map((type) => ({
          atom: { kind: "type" as const, value: type, span: fullSpan },
          present: this.game.allOf(
            [entry.present, this.game.hasCharacterType(entry.atom.name, type)],
            this.freshName("join_type"),
          ),
        })),
      );
      return { kind: "dynamicSet", atomKind: "type", elements: this.mergeElements(elements), span: fullSpan };
    }

    if (field === "alignment") {
      const elements = playerEntries.flatMap((entry) =>
        ALIGNMENTS.map((alignment) => ({
          atom: { kind: "alignment" as const, value: alignment, span: fullSpan },
          present: this.game.allOf(
            [
              entry.present,
              alignment === "Evil" ? this.game.isEvil(entry.atom.name) : this.game.isGood(entry.atom.name),
            ],
            this.freshName("join_alignment"),
          ),
        })),
      );
      return { kind: "dynamicSet", atomKind: "alignment", elements: this.mergeElements(elements), span: fullSpan };
    }

    throw new DslError(`Unknown field '${field}' on a player set`, fieldSpan);
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
    if (first.kind === "type") {
      const typeValues: CharacterType[] = [];
      for (const v of values) {
        if (v.kind !== "type") throw new DslError(`Mixed-type set literal; expected a character type`, v.span);
        if (!typeValues.includes(v.value)) typeValues.push(v.value);
      }
      return { kind: "typeSet", values: typeValues, span };
    }
    if (first.kind === "alignment") {
      const alignmentValues: AlignmentName[] = [];
      for (const v of values) {
        if (v.kind !== "alignment") throw new DslError(`Mixed-type set literal; expected an alignment`, v.span);
        if (!alignmentValues.includes(v.value)) alignmentValues.push(v.value);
      }
      return { kind: "alignmentSet", values: alignmentValues, span };
    }
    throw new DslError(`Set literals support only players, roles, character types, or alignments`, span);
  }

  private evalQuant(node: Extract<AstNode, { kind: "quant" }>, env: ReadonlyMap<string, DslValue>): DslValue {
    const atoms = this.setElements(this.evalNode(node.set, env), node.set.span);
    const entries = atoms.elements.map((entry) => {
      const newEnv = new Map(env);
      newEnv.set(node.variable, entry.atom);
      const body = this.expectBool(this.evalNode(node.body, newEnv)).value;
      return { present: entry.present, body };
    });
    const label = `${node.quantifier}_${node.variable}`;
    const matches = entries.map((entry) =>
      this.game.allOf([entry.present, entry.body], this.freshName(`${label}_entry`)),
    );
    let result: BoolLike;
    switch (node.quantifier) {
      case "some":
        result = this.game.anyOf(matches, this.freshName(label));
        break;
      case "all":
        result = this.game.allOf(
          entries.map((entry) =>
            this.game.anyOf(
              [this.game.not(entry.present, this.freshName(`${label}_absent`)), entry.body],
              this.freshName(`${label}_present_implies_body`),
            ),
          ),
          this.freshName(label),
        );
        break;
      case "no":
        result = this.game.not(this.game.anyOf(matches, this.freshName(`${label}_any`)), this.freshName(label));
        break;
      case "one":
        result = this.game.boolSumEquals(matches, 1, this.freshName(label));
        break;
      case "lone":
        result = this.game.anyOf(
          [
            this.game.boolSumEquals(matches, 0, this.freshName(`${label}_zero`)),
            this.game.boolSumEquals(matches, 1, this.freshName(`${label}_one`)),
          ],
          this.freshName(label),
        );
        break;
    }
    return { kind: "bool", value: result, span: node.span };
  }

  private evalMultiplicity(
    node: Extract<AstNode, { kind: "multiplicity" }>,
    env: ReadonlyMap<string, DslValue>,
  ): DslValue {
    const literals = this.setElements(this.evalNode(node.set, env), node.set.span).elements.map(
      (entry) => entry.present,
    );
    let result: BoolLike;
    switch (node.quantifier) {
      case "some":
        result = this.game.anyOf(literals, this.freshName("some_set"));
        break;
      case "no":
        result = this.game.not(this.game.anyOf(literals, this.freshName("no_set_any")), this.freshName("no_set"));
        break;
      case "one":
        result = this.game.boolSumEquals(literals, 1, this.freshName("one_set"));
        break;
      case "lone":
        result = this.game.anyOf(
          [
            this.game.boolSumEquals(literals, 0, this.freshName("lone_set_zero")),
            this.game.boolSumEquals(literals, 1, this.freshName("lone_set_one")),
          ],
          this.freshName("lone_set"),
        );
        break;
    }
    return { kind: "bool", value: result, span: node.span };
  }

  private evalComprehension(
    node: Extract<AstNode, { kind: "comprehension" }>,
    env: ReadonlyMap<string, DslValue>,
  ): DslValue {
    const source = this.setElements(this.evalNode(node.set, env), node.set.span);
    const elements = source.elements.map((entry) => {
      const newEnv = new Map(env);
      newEnv.set(node.variable, entry.atom);
      const body = this.expectBool(this.evalNode(node.body, newEnv)).value;
      return {
        atom: entry.atom,
        present: this.game.allOf([entry.present, body], this.freshName(`comprehension_${node.variable}`)),
      };
    });
    return { kind: "dynamicSet", atomKind: source.kind, elements, span: node.span };
  }

  private setElements(
    value: DslValue,
    span: Span,
  ): { readonly kind: AtomKind; readonly elements: readonly SetElement[] } {
    if (value.kind === "dynamicSet") return { kind: value.atomKind, elements: value.elements };
    if (value.kind === "playerSet")
      return {
        kind: "player",
        elements: value.names.map((name) => ({
          atom: { kind: "player", name, span },
          present: this.game.constantBool(true, this.freshName("static_player_set")),
        })),
      };
    if (value.kind === "player")
      return {
        kind: "player",
        elements: [{ atom: value, present: this.game.constantBool(true, this.freshName("static_player")) }],
      };
    if (value.kind === "roleSet")
      return {
        kind: "role",
        elements: value.names.map((name) => ({
          atom: { kind: "role", name, span },
          present: this.game.constantBool(true, this.freshName("static_role_set")),
        })),
      };
    if (value.kind === "role")
      return {
        kind: "role",
        elements: [{ atom: value, present: this.game.constantBool(true, this.freshName("static_role")) }],
      };
    if (value.kind === "typeSet")
      return {
        kind: "type",
        elements: value.values.map((type) => ({
          atom: { kind: "type", value: type, span },
          present: this.game.constantBool(true, this.freshName("static_type_set")),
        })),
      };
    if (value.kind === "type")
      return {
        kind: "type",
        elements: [{ atom: value, present: this.game.constantBool(true, this.freshName("static_type")) }],
      };
    if (value.kind === "alignmentSet")
      return {
        kind: "alignment",
        elements: value.values.map((alignment) => ({
          atom: { kind: "alignment", value: alignment, span },
          present: this.game.constantBool(true, this.freshName("static_alignment_set")),
        })),
      };
    if (value.kind === "alignment")
      return {
        kind: "alignment",
        elements: [{ atom: value, present: this.game.constantBool(true, this.freshName("static_alignment")) }],
      };
    if (value.kind === "playerRole")
      return {
        kind: "role",
        elements: this.ctx.script.map((name) => ({
          atom: { kind: "role", name, span },
          present: this.game.actualIs(value.player, name),
        })),
      };
    if (value.kind === "playerType")
      return {
        kind: "type",
        elements: ALL_CHARACTER_TYPES.map((type) => ({
          atom: { kind: "type", value: type, span },
          present: this.game.hasCharacterType(value.player, type),
        })),
      };
    if (value.kind === "playerAlignment")
      return {
        kind: "alignment",
        elements: ALIGNMENTS.map((alignment) => ({
          atom: { kind: "alignment", value: alignment, span },
          present: alignment === "Evil" ? this.game.isEvil(value.player) : this.game.isGood(value.player),
        })),
      };
    throw new DslError(`Expected a set, got ${value.kind}`, span);
  }

  private mergeElements(elements: readonly SetElement[]): readonly SetElement[] {
    return [...this.groupElements(elements).values()].map(({ atom, presences }) => ({
      atom,
      present:
        presences.length === 1 ? (presences[0] as BoolLike) : this.game.anyOf(presences, this.freshName("set_merge")),
    }));
  }

  private unionElements(left: readonly SetElement[], right: readonly SetElement[]): readonly SetElement[] {
    const groups = this.groupElements([...left, ...right]);
    return [...groups.values()].map(({ atom, presences }) => ({
      atom,
      present:
        presences.length === 1 ? (presences[0] as BoolLike) : this.game.anyOf(presences, this.freshName("set_union")),
    }));
  }

  private intersectElements(left: readonly SetElement[], right: readonly SetElement[]): readonly SetElement[] {
    const leftGroups = this.groupElements(left);
    const rightGroups = this.groupElements(right);
    const elements: SetElement[] = [];
    for (const [key, leftGroup] of leftGroups) {
      const rightGroup = rightGroups.get(key);
      if (rightGroup === undefined) continue;
      const leftPresent =
        leftGroup.presences.length === 1
          ? (leftGroup.presences[0] as BoolLike)
          : this.game.anyOf(leftGroup.presences, this.freshName("set_intersect_left"));
      const rightPresent =
        rightGroup.presences.length === 1
          ? (rightGroup.presences[0] as BoolLike)
          : this.game.anyOf(rightGroup.presences, this.freshName("set_intersect_right"));
      elements.push({
        atom: leftGroup.atom,
        present: this.game.allOf([leftPresent, rightPresent], this.freshName("set_intersect")),
      });
    }
    return elements;
  }

  private subtractElements(left: readonly SetElement[], right: readonly SetElement[]): readonly SetElement[] {
    const leftGroups = this.groupElements(left);
    const rightGroups = this.groupElements(right);
    const elements: SetElement[] = [];
    for (const [key, leftGroup] of leftGroups) {
      const leftPresent =
        leftGroup.presences.length === 1
          ? (leftGroup.presences[0] as BoolLike)
          : this.game.anyOf(leftGroup.presences, this.freshName("set_minus_left"));
      const rightGroup = rightGroups.get(key);
      if (rightGroup === undefined) {
        elements.push({ atom: leftGroup.atom, present: leftPresent });
        continue;
      }
      const rightPresent =
        rightGroup.presences.length === 1
          ? (rightGroup.presences[0] as BoolLike)
          : this.game.anyOf(rightGroup.presences, this.freshName("set_minus_right"));
      elements.push({
        atom: leftGroup.atom,
        present: this.game.allOf(
          [leftPresent, this.game.not(rightPresent, this.freshName("set_minus_absent"))],
          this.freshName("set_minus"),
        ),
      });
    }
    return elements;
  }

  private groupElements(
    elements: readonly SetElement[],
  ): Map<string, { readonly atom: SetAtom; readonly presences: BoolLike[] }> {
    const groups = new Map<string, { atom: SetAtom; presences: BoolLike[] }>();
    for (const element of elements) {
      const key = atomKey(element.atom);
      const group = groups.get(key);
      if (group === undefined) {
        groups.set(key, { atom: element.atom, presences: [element.present] });
      } else {
        group.presences.push(element.present);
      }
    }
    return groups;
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
      const a = this.setElements(lhs, node.left.span);
      const b = this.setElements(rhs, node.right.span);
      if (a.kind !== b.kind) throw new DslError(`Cannot union sets of different kinds`, node.span);
      return {
        kind: "dynamicSet",
        atomKind: a.kind,
        elements: this.unionElements(a.elements, b.elements),
        span: node.span,
      };
    }
    if (op === "amp" || op === "minus") {
      const a = this.setElements(this.evalNode(node.left, env), node.left.span);
      const b = this.setElements(this.evalNode(node.right, env), node.right.span);
      if (a.kind !== b.kind) throw new DslError(`Cannot combine sets of different kinds`, node.span);
      const elements =
        op === "amp" ? this.intersectElements(a.elements, b.elements) : this.subtractElements(a.elements, b.elements);
      return { kind: "dynamicSet", atomKind: a.kind, elements, span: node.span };
    }
    throw new DslError(`Operator '${op}' not supported here`, node.span);
  }

  private compileEquality(lhs: DslValue, rhs: DslValue, span: Span): BoolLike {
    const pair = orderPair(lhs, rhs);
    const a = pair[0];
    const b = pair[1];
    if (a.kind === "cardinality" && b.kind === "number")
      return this.game.boolSumEquals(a.literals, b.value, this.freshName(`cardinality_${b.value}`));
    if (a.kind === "number" && b.kind === "number")
      return this.game.constantBool(a.value === b.value, this.freshName("number_eq"));
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
    if (isSetAtom(lhs)) {
      const rhsSet = this.setElements(rhs, rhs.span);
      if (rhsSet.kind !== lhs.kind) throw new DslError(`'in' requires matching atom and set types`, span);
      const matches = rhsSet.elements.filter((entry) => sameAtom(entry.atom, lhs)).map((entry) => entry.present);
      return this.game.anyOf(matches, this.freshName("in_set"));
    }
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
    if (node.name === "role_distance") {
      if (node.args.length !== 3) throw new DslError(`role_distance() takes (n, role, role)`, node.span);
      const countArg = node.args[0] as AstCall["args"][number];
      const leftArg = node.args[1] as AstCall["args"][number];
      const rightArg = node.args[2] as AstCall["args"][number];
      if (countArg.name !== undefined || leftArg.name !== undefined || rightArg.name !== undefined)
        throw new DslError(`role_distance arguments are positional`, node.span);
      const distance = this.evalNode(countArg.value, env);
      const left = this.evalNode(leftArg.value, env);
      const right = this.evalNode(rightArg.value, env);
      if (distance.kind !== "number") throw new DslError(`role_distance expects a number first`, countArg.span);
      if (left.kind !== "role") throw new DslError(`role_distance expected a role second`, left.span);
      if (right.kind !== "role") throw new DslError(`role_distance expected a role third`, right.span);
      return {
        kind: "bool",
        value: this.rolesAtDistance(left.name, right.name, distance.value),
        span: node.span,
      };
    }
    if (node.name === "townsfolk_chain_length") {
      if (node.args.length !== 1) throw new DslError(`townsfolk_chain_length() takes (n)`, node.span);
      const lengthArg = node.args[0] as AstCall["args"][number];
      if (lengthArg.name !== undefined)
        throw new DslError(`townsfolk_chain_length's argument is positional`, lengthArg.span);
      const lengthVal = this.evalNode(lengthArg.value, env);
      if (lengthVal.kind !== "number") throw new DslError(`townsfolk_chain_length expects a number`, lengthArg.span);
      return {
        kind: "bool",
        value: this.longestCharacterTypeChainIs(CharacterType.Townsfolk, lengthVal.value),
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
    if (node.name === "role_at") {
      if (node.args.length !== 3) throw new DslError(`role_at() takes (player, role, timing)`, node.span);
      const playerArg = node.args[0] as AstCall["args"][number];
      const roleArg = node.args[1] as AstCall["args"][number];
      const timingArg = node.args[2] as AstCall["args"][number];
      if (playerArg.name !== undefined || roleArg.name !== undefined || timingArg.name !== undefined)
        throw new DslError(`role_at arguments are positional`, node.span);
      const player = this.evalNode(playerArg.value, env);
      const role = this.evalNode(roleArg.value, env);
      const timing = this.expectTimingArg(timingArg);
      if (player.kind !== "player") throw new DslError(`role_at expected a player first`, player.span);
      if (role.kind !== "role") throw new DslError(`role_at expected a role second`, role.span);
      return {
        kind: "bool",
        value: this.game.hasRoleAt(player.name, role.name, timing),
        span: node.span,
      };
    }
    if (node.name === "fortune_teller_red_herring") {
      if (node.args.length !== 2)
        throw new DslError(`fortune_teller_red_herring() takes (fortuneTeller, player)`, node.span);
      const fortuneTellerArg = node.args[0] as AstCall["args"][number];
      const playerArg = node.args[1] as AstCall["args"][number];
      if (fortuneTellerArg.name !== undefined || playerArg.name !== undefined)
        throw new DslError(`fortune_teller_red_herring arguments are positional`, node.span);
      const fortuneTeller = this.evalNode(fortuneTellerArg.value, env);
      const player = this.evalNode(playerArg.value, env);
      if (fortuneTeller.kind !== "player")
        throw new DslError(`fortune_teller_red_herring expected a player first`, fortuneTeller.span);
      if (player.kind !== "player")
        throw new DslError(`fortune_teller_red_herring expected a player second`, player.span);
      return {
        kind: "bool",
        value: this.game.fortuneTellerRedHerring(fortuneTeller.name, player.name),
        span: node.span,
      };
    }
    if (node.name === "globally_drunk") {
      if (node.args.length !== 1) throw new DslError(`globally_drunk() takes (player)`, node.span);
      const playerArg = node.args[0] as AstCall["args"][number];
      if (playerArg.name !== undefined) throw new DslError(`globally_drunk argument is positional`, node.span);
      const player = this.evalNode(playerArg.value, env);
      if (player.kind !== "player") throw new DslError(`globally_drunk expected a player`, player.span);
      return { kind: "bool", value: this.game.globalDrunk(player.name), span: node.span };
    }
    if (node.name === "poisoned") {
      if (node.args.length !== 2) throw new DslError(`poisoned() takes (player, timing)`, node.span);
      const playerArg = node.args[0] as AstCall["args"][number];
      const timingArg = node.args[1] as AstCall["args"][number];
      if (playerArg.name !== undefined || timingArg.name !== undefined)
        throw new DslError(`poisoned arguments are positional`, node.span);
      const player = this.evalNode(playerArg.value, env);
      const timing = this.expectTimingArg(timingArg);
      if (player.kind !== "player") throw new DslError(`poisoned expected a player first`, player.span);
      return { kind: "bool", value: this.game.poisoned(player.name, timing), span: node.span };
    }
    if (node.name === "chef") {
      if (node.args.length !== 1) throw new DslError(`chef() takes (n)`, node.span);
      const countArg = node.args[0] as AstCall["args"][number];
      if (countArg.name !== undefined) throw new DslError(`chef's first argument is positional`, countArg.span);
      const countVal = this.evalNode(countArg.value, env);
      if (countVal.kind !== "number") throw new DslError(`chef expects a number`, countArg.span);
      const name = this.freshName(`chef_${countVal.value}`);
      const bv = Chef.learnsCount(this.game, countVal.value, name);
      return { kind: "bool", value: bv, span: node.span };
    }
    throw new DslError(`Unknown function '${node.name}'`, node.nameSpan);
  }

  private rolesAtDistance(leftRole: string, rightRole: string, distance: number): BoolLike {
    if (!Number.isInteger(distance) || distance < 0)
      throw new DslError(`Distance must be a non-negative integer`, { start: 0, end: 0 });
    return this.game.anyOf(
      this.ctx.players.flatMap((leftPlayer, leftIndex) =>
        this.ctx.players.map((rightPlayer, rightIndex) => {
          const clockwise = (rightIndex - leftIndex + this.ctx.players.length) % this.ctx.players.length;
          const seatingDistance = Math.min(clockwise, this.ctx.players.length - clockwise);
          return this.game.allOf(
            [
              this.game.actualIs(leftPlayer, leftRole),
              this.game.actualIs(rightPlayer, rightRole),
              this.game.constantBool(seatingDistance === distance, this.freshName(`distance_${distance}`)),
            ],
            this.freshName(`role_distance_${distance}`),
          );
        }),
      ),
      this.freshName(`roles_at_distance_${distance}`),
    );
  }

  private longestCharacterTypeChainIs(characterType: CharacterType, length: number): BoolLike {
    if (!Number.isInteger(length) || length < 1)
      throw new DslError(`Chain length must be a positive integer`, { start: 0, end: 0 });
    const atLeastLength = this.hasCharacterTypeChain(characterType, length);
    if (length >= this.ctx.players.length) return atLeastLength;
    return this.game.allOf(
      [
        atLeastLength,
        this.game.not(this.hasCharacterTypeChain(characterType, length + 1), this.freshName("longer_chain_absent")),
      ],
      this.freshName(`${characterType}_chain_length_${length}`),
    );
  }

  private hasCharacterTypeChain(characterType: CharacterType, length: number): BoolLike {
    if (length > this.ctx.players.length) return this.game.constantBool(false, this.freshName("chain_too_long"));
    return this.game.anyOf(
      this.ctx.players.map((_player, startIndex) =>
        this.game.allOf(
          Array.from({ length }, (_ignored, offset) => {
            const player = this.ctx.players[(startIndex + offset) % this.ctx.players.length] as string;
            return this.game.hasCharacterType(player, characterType);
          }),
          this.freshName(`${characterType}_chain_${length}`),
        ),
      ),
      this.freshName(`${characterType}_chain_at_least_${length}`),
    );
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

function sameAtom(a: DslValue, b: DslValue): boolean {
  if (a.kind === "player" && b.kind === "player") return a.name === b.name;
  if (a.kind === "role" && b.kind === "role") return a.name === b.name;
  if (a.kind === "type" && b.kind === "type") return a.value === b.value;
  if (a.kind === "alignment" && b.kind === "alignment") return a.value === b.value;
  return false;
}

function atomKey(atom: SetAtom): string {
  switch (atom.kind) {
    case "player":
    case "role":
      return `${atom.kind}:${atom.name}`;
    case "type":
    case "alignment":
      return `${atom.kind}:${atom.value}`;
  }
}

function isSetAtom(value: DslValue): value is SetAtom {
  return value.kind === "player" || value.kind === "role" || value.kind === "type" || value.kind === "alignment";
}

function orderPair(a: DslValue, b: DslValue): readonly [DslValue, DslValue] {
  if (b.kind === "cardinality") return [b, a];
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
