import type { Span } from "./tokens";

export type Quantifier = "some" | "all" | "no" | "one" | "lone";

export type BinaryOp = "and" | "or" | "implies" | "eq" | "neq" | "in" | "plus" | "minus" | "amp";

export interface AstQuant {
  readonly kind: "quant";
  readonly quantifier: Quantifier;
  readonly variable: string;
  readonly set: AstNode;
  readonly body: AstNode;
  readonly span: Span;
}

export interface AstMultiplicity {
  readonly kind: "multiplicity";
  readonly quantifier: Exclude<Quantifier, "all">;
  readonly set: AstNode;
  readonly span: Span;
}

export interface AstBinOp {
  readonly kind: "binop";
  readonly op: BinaryOp;
  readonly left: AstNode;
  readonly right: AstNode;
  readonly span: Span;
}

export interface AstNot {
  readonly kind: "not";
  readonly inner: AstNode;
  readonly span: Span;
}

export interface AstPath {
  readonly kind: "path";
  readonly root: string;
  readonly rootSpan: Span;
  readonly fields: readonly { readonly name: string; readonly span: Span }[];
  readonly span: Span;
}

export interface AstNumber {
  readonly kind: "number";
  readonly value: number;
  readonly span: Span;
}

export interface AstSetLit {
  readonly kind: "setlit";
  readonly elements: readonly AstNode[];
  readonly span: Span;
}

export interface AstComprehension {
  readonly kind: "comprehension";
  readonly variable: string;
  readonly set: AstNode;
  readonly body: AstNode;
  readonly span: Span;
}

export interface AstCardinality {
  readonly kind: "cardinality";
  readonly set: AstNode;
  readonly span: Span;
}

export interface AstBoolLit {
  readonly kind: "boollit";
  readonly value: boolean;
  readonly span: Span;
}

export interface AstCall {
  readonly kind: "call";
  readonly name: string;
  readonly nameSpan: Span;
  readonly args: readonly AstCallArg[];
  readonly span: Span;
}

export interface AstCallArg {
  readonly name?: string;
  readonly value: AstNode;
  readonly span: Span;
}

export type AstNode =
  | AstQuant
  | AstMultiplicity
  | AstBinOp
  | AstNot
  | AstPath
  | AstNumber
  | AstSetLit
  | AstComprehension
  | AstCardinality
  | AstBoolLit
  | AstCall;
