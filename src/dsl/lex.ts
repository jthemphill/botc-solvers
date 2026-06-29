import { KEYWORDS, type Token, type TokenKind } from "./tokens";

export class DslError extends Error {
  constructor(
    message: string,
    readonly span: { readonly start: number; readonly end: number },
  ) {
    super(message);
  }
}

const SINGLE: ReadonlyMap<string, TokenKind> = new Map([
  ["(", "lparen"],
  [")", "rparen"],
  ["{", "lbrace"],
  ["}", "rbrace"],
  [",", "comma"],
  [":", "colon"],
  [".", "dot"],
  ["|", "pipe"],
  ["+", "plus"],
  ["-", "minus"],
  ["&", "amp"],
  ["#", "hash"],
]);

function isIdentStart(ch: string): boolean {
  return /[A-Za-z_]/.test(ch);
}

function isIdentRest(ch: string): boolean {
  return /[A-Za-z0-9_]/.test(ch);
}

export function lex(src: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;
  while (i < src.length) {
    const ch = src[i] as string;
    if (/\s/.test(ch)) {
      i += 1;
      continue;
    }
    const start = i;

    if (ch === "/" && src[i + 1] === "/") {
      while (i < src.length && src[i] !== "\n") i += 1;
      continue;
    }

    if (ch === "`") {
      i += 1;
      let text = "";
      while (i < src.length && src[i] !== "`") {
        text += src[i];
        i += 1;
      }
      if (i >= src.length) throw new DslError("Unterminated backtick identifier", { start, end: i });
      i += 1;
      tokens.push({ kind: "ident", text, span: { start, end: i } });
      continue;
    }

    if (ch === "&" && src[i + 1] === "&") {
      i += 2;
      tokens.push({ kind: "and", text: "&&", span: { start, end: i } });
      continue;
    }
    if (ch === "|" && src[i + 1] === "|") {
      i += 2;
      tokens.push({ kind: "or", text: "||", span: { start, end: i } });
      continue;
    }
    if (ch === "=" && src[i + 1] === "=") {
      i += 2;
      tokens.push({ kind: "eq", text: "==", span: { start, end: i } });
      continue;
    }
    if (ch === "!" && src[i + 1] === "=") {
      i += 2;
      tokens.push({ kind: "neq", text: "!=", span: { start, end: i } });
      continue;
    }
    if (ch === "=" && src[i + 1] === ">") {
      i += 2;
      tokens.push({ kind: "implies", text: "=>", span: { start, end: i } });
      continue;
    }
    if (ch === "=") {
      i += 1;
      tokens.push({ kind: "eq", text: "=", span: { start, end: i } });
      continue;
    }
    if (ch === "!") {
      i += 1;
      tokens.push({ kind: "bang", text: "!", span: { start, end: i } });
      continue;
    }

    const singleKind = SINGLE.get(ch);
    if (singleKind !== undefined) {
      i += 1;
      tokens.push({ kind: singleKind, text: ch, span: { start, end: i } });
      continue;
    }

    if (/[0-9]/.test(ch)) {
      while (i < src.length && /[0-9]/.test(src[i] as string)) i += 1;
      tokens.push({ kind: "number", text: src.slice(start, i), span: { start, end: i } });
      continue;
    }

    if (isIdentStart(ch)) {
      while (i < src.length && isIdentRest(src[i] as string)) i += 1;
      const text = src.slice(start, i);
      const keyword = KEYWORDS.get(text);
      tokens.push({ kind: keyword ?? "ident", text, span: { start, end: i } });
      continue;
    }

    throw new DslError(`Unexpected character ${JSON.stringify(ch)}`, { start, end: i + 1 });
  }
  tokens.push({ kind: "eof", text: "", span: { start: src.length, end: src.length } });
  return tokens;
}
