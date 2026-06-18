import type { AstNode, AstCallArg, BinaryOp, Quantifier } from "./ast";
import { DslError } from "./lex";
import type { Span, Token, TokenKind } from "./tokens";

class Parser {
  private pos = 0;
  constructor(private readonly tokens: readonly Token[]) {}

  private peek(): Token {
    return this.tokens[this.pos] as Token;
  }

  private consume(): Token {
    const tok = this.tokens[this.pos] as Token;
    this.pos += 1;
    return tok;
  }

  private match(kind: TokenKind): boolean {
    if (this.peek().kind === kind) {
      this.pos += 1;
      return true;
    }
    return false;
  }

  private expect(kind: TokenKind, label?: string): Token {
    const tok = this.peek();
    if (tok.kind !== kind) {
      throw new DslError(
        `Expected ${label ?? kind} but got ${tok.kind === "eof" ? "end of input" : tok.text}`,
        tok.span,
      );
    }
    return this.consume();
  }

  parseTop(): AstNode {
    const node = this.parseFormula();
    if (this.peek().kind !== "eof") {
      throw new DslError(`Unexpected ${this.peek().text}`, this.peek().span);
    }
    return node;
  }

  private parseFormula(): AstNode {
    return this.parseImplies();
  }

  private parseImplies(): AstNode {
    const left = this.parseOr();
    if (this.match("implies")) {
      const right = this.parseImplies();
      return { kind: "binop", op: "implies", left, right, span: spanOf(left, right) };
    }
    return left;
  }

  private parseOr(): AstNode {
    let left = this.parseAnd();
    while (this.peek().kind === "or") {
      this.consume();
      const right = this.parseAnd();
      left = { kind: "binop", op: "or", left, right, span: spanOf(left, right) };
    }
    return left;
  }

  private parseAnd(): AstNode {
    let left = this.parseUnary();
    while (this.peek().kind === "and") {
      this.consume();
      const right = this.parseUnary();
      left = { kind: "binop", op: "and", left, right, span: spanOf(left, right) };
    }
    return left;
  }

  private parseUnary(): AstNode {
    const tok = this.peek();
    if (tok.kind === "bang" || tok.kind === "not") {
      this.consume();
      const inner = this.parseUnary();
      return { kind: "not", inner, span: { start: tok.span.start, end: inner.span.end } };
    }
    return this.parseQuantOrCompare();
  }

  private parseQuantOrCompare(): AstNode {
    const tok = this.peek();
    if (tok.kind === "some" || tok.kind === "all" || tok.kind === "no" || tok.kind === "one" || tok.kind === "lone") {
      if (this.tokens[this.pos + 1]?.kind === "ident" && this.tokens[this.pos + 2]?.kind === "colon") {
        return this.parseQuantifier(tok.kind as Quantifier);
      }
      if (tok.kind !== "all") return this.parseMultiplicity(tok.kind);
    }
    return this.parseCompare();
  }

  private parseQuantifier(q: Quantifier): AstNode {
    const start = this.consume();
    const variable = this.expect("ident", "quantifier variable");
    this.expect("colon");
    const set = this.parseSetExpr();
    this.expect("pipe");
    const body = this.parseFormula();
    return {
      kind: "quant",
      quantifier: q,
      variable: variable.text,
      set,
      body,
      span: { start: start.span.start, end: body.span.end },
    };
  }

  private parseMultiplicity(q: Exclude<Quantifier, "all">): AstNode {
    const start = this.consume();
    const set = this.parseUnary();
    return {
      kind: "multiplicity",
      quantifier: q,
      set,
      span: { start: start.span.start, end: set.span.end },
    };
  }

  private parseCompare(): AstNode {
    const left = this.parseSetExpr();
    const tok = this.peek();
    if (tok.kind === "eq" || tok.kind === "neq" || tok.kind === "in") {
      this.consume();
      const right = this.parseSetExpr();
      const op: BinaryOp = tok.kind === "eq" ? "eq" : tok.kind === "neq" ? "neq" : "in";
      return { kind: "binop", op, left, right, span: spanOf(left, right) };
    }
    return left;
  }

  private parseSetExpr(): AstNode {
    return this.parseSetUnion();
  }

  private parseSetUnion(): AstNode {
    let left = this.parseSetIntersect();
    for (;;) {
      const tok = this.peek();
      if (tok.kind === "plus" || tok.kind === "minus") {
        this.consume();
        const right = this.parseSetIntersect();
        const op: BinaryOp = tok.kind === "plus" ? "plus" : "minus";
        left = { kind: "binop", op, left, right, span: spanOf(left, right) };
      } else {
        return left;
      }
    }
  }

  private parseSetIntersect(): AstNode {
    let left = this.parsePrimary();
    while (this.peek().kind === "amp") {
      this.consume();
      const right = this.parsePrimary();
      left = { kind: "binop", op: "amp", left, right, span: spanOf(left, right) };
    }
    return left;
  }

  private parsePrimary(): AstNode {
    const tok = this.peek();

    if (tok.kind === "lparen") {
      this.consume();
      const inner = this.parseFormula();
      this.expect("rparen");
      return inner;
    }

    if (tok.kind === "lbrace") {
      this.consume();
      if (this.peek().kind === "ident" && this.tokens[this.pos + 1]?.kind === "colon") {
        const variable = this.consume();
        this.expect("colon");
        const set = this.parseSetExpr();
        this.expect("pipe");
        const body = this.parseFormula();
        const end = this.expect("rbrace");
        return {
          kind: "comprehension",
          variable: variable.text,
          set,
          body,
          span: { start: tok.span.start, end: end.span.end },
        };
      }
      const elements: AstNode[] = [];
      if (this.peek().kind !== "rbrace") {
        elements.push(this.parseSetExpr());
        while (this.match("comma")) elements.push(this.parseSetExpr());
      }
      const end = this.expect("rbrace");
      return { kind: "setlit", elements, span: { start: tok.span.start, end: end.span.end } };
    }

    if (tok.kind === "hash") {
      this.consume();
      const set = this.parsePrimary();
      return { kind: "cardinality", set, span: { start: tok.span.start, end: set.span.end } };
    }

    if (tok.kind === "number") {
      this.consume();
      return { kind: "number", value: Number(tok.text), span: tok.span };
    }

    if (tok.kind === "true" || tok.kind === "false") {
      this.consume();
      return { kind: "boollit", value: tok.kind === "true", span: tok.span };
    }

    if (tok.kind === "ident") {
      return this.parseIdentOrCall();
    }

    throw new DslError(`Unexpected ${tok.text || tok.kind}`, tok.span);
  }

  private parseIdentOrCall(): AstNode {
    const root = this.consume();
    if (this.peek().kind === "lparen") {
      this.consume();
      const args: AstCallArg[] = [];
      if (this.peek().kind !== "rparen") {
        args.push(this.parseCallArg());
        while (this.match("comma")) args.push(this.parseCallArg());
      }
      const end = this.expect("rparen");
      return {
        kind: "call",
        name: root.text,
        nameSpan: root.span,
        args,
        span: { start: root.span.start, end: end.span.end },
      };
    }
    const fields: { name: string; span: Span }[] = [];
    let end = root.span.end;
    while (this.peek().kind === "dot") {
      this.consume();
      const field = this.expect("ident", "field name");
      fields.push({ name: field.text, span: field.span });
      end = field.span.end;
    }
    return { kind: "path", root: root.text, rootSpan: root.span, fields, span: { start: root.span.start, end } };
  }

  private parseCallArg(): AstCallArg {
    const start = this.peek();
    if (start.kind === "ident" && this.tokens[this.pos + 1]?.kind === "colon") {
      this.consume();
      this.consume();
      const value = this.parseSetExpr();
      return { name: start.text, value, span: { start: start.span.start, end: value.span.end } };
    }
    const value = this.parseSetExpr();
    return { value, span: value.span };
  }
}

function spanOf(left: AstNode, right: AstNode): Span {
  return { start: left.span.start, end: right.span.end };
}

export function parse(tokens: readonly Token[]): AstNode {
  return new Parser(tokens).parseTop();
}
