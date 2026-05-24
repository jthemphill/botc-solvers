export type TokenKind =
  | "ident"
  | "number"
  | "lparen"
  | "rparen"
  | "lbrace"
  | "rbrace"
  | "comma"
  | "colon"
  | "dot"
  | "pipe"
  | "plus"
  | "minus"
  | "amp"
  | "bang"
  | "and"
  | "or"
  | "implies"
  | "eq"
  | "neq"
  | "in"
  | "some"
  | "all"
  | "no"
  | "one"
  | "lone"
  | "not"
  | "true"
  | "false"
  | "eof";

export interface Span {
  readonly start: number;
  readonly end: number;
}

export interface Token {
  readonly kind: TokenKind;
  readonly text: string;
  readonly span: Span;
}

export const KEYWORDS: ReadonlyMap<string, TokenKind> = new Map([
  ["some", "some"],
  ["all", "all"],
  ["no", "no"],
  ["one", "one"],
  ["lone", "lone"],
  ["in", "in"],
  ["and", "and"],
  ["or", "or"],
  ["not", "not"],
  ["implies", "implies"],
  ["true", "true"],
  ["false", "false"],
]);
