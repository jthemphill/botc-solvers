import { lex } from "../dsl/lex";
import { Alignment } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import type { Claim, PuzzleDoc } from "../schema/puzzleDoc";

export const ALL_ROLE_NAMES = [...ROLE_CLASSES.keys()].sort((left, right) => left.localeCompare(right));

const ROLE_BY_NORMALIZED_NAME = new Map(ALL_ROLE_NAMES.map((role) => [normalizeRoleName(role), role] as const));

export function normalizeRoleName(role: string): string {
  return role.toLowerCase().replace(/[^a-z0-9]+/g, "");
}

export function canonicalRoleName(role: string | undefined): string | undefined {
  if (!role) return undefined;
  return ROLE_CLASSES.has(role) ? role : ROLE_BY_NORMALIZED_NAME.get(normalizeRoleName(role));
}

export function protectedScriptRoles(doc: PuzzleDoc): string[] {
  return mergeRoleNames([
    ...doc.claims.flatMap(claimScriptRoles),
    ...(doc.fixedRoles ?? []).flatMap((fixedRole) => fixedRole.roles),
  ]);
}

export function scriptWithProtectedRoles(script: readonly string[], doc: PuzzleDoc): string[] {
  return mergeRoleNames([...script, ...protectedScriptRoles(doc)]);
}

export function withProtectedScript(doc: PuzzleDoc): PuzzleDoc {
  return { ...doc, script: scriptWithProtectedRoles(doc.script, doc) };
}

export function claimScriptRoles(claim: Claim): string[] {
  const roles = [claimTypeRoleName(claim.type)];

  switch (claim.type) {
    case "Investigator":
      roles.push(claim.minionRole, claim.role);
      break;
    case "Librarian":
    case "Washerwoman":
      roles.push(claim.role);
      break;
    case "FortuneTeller":
      roles.push(...claim.checks.map((check) => check.demonRole));
      break;
    case "Undertaker":
      roles.push(claim.role);
      break;
    case "Juggler":
      roles.push(...Object.values(claim.guesses));
      break;
    case "Dreamer":
      roles.push(...claim.roles);
      break;
    case "Savant":
      roles.push(...claim.statements.flatMap((statement) => statement.options.flatMap(extractDslRoleNames)));
      break;
  }

  return mergeRoleNames(roles);
}

export function jugglerGuessRoleOptions(doc: PuzzleDoc, player: string): string[] {
  const scriptRoles = mergeRoleNames(doc.script);
  const scriptRoleSet = new Set(scriptRoles);
  const claimedRole = claimedRoleForPlayer(doc, player);
  return mergeRoleNames([claimedRole, ...scriptRoles.filter(isJugglerHiddenGuessRole), ...scriptRoles]).filter((role) =>
    scriptRoleSet.has(role),
  );
}

function claimTypeRoleName(type: Claim["type"]): string | undefined {
  return canonicalRoleName(type);
}

function claimedRoleForPlayer(doc: PuzzleDoc, player: string): string | undefined {
  const claim = doc.claims.find((candidate) => candidate.name === player);
  return claim === undefined ? undefined : claimTypeRoleName(claim.type);
}

function isJugglerHiddenGuessRole(role: string): boolean {
  const cls = ROLE_CLASSES.get(role);
  return cls?.alignment === Alignment.Evil || role === "Drunk";
}

function extractDslRoleNames(src: string): string[] {
  try {
    return mergeRoleNames(lex(src).map((token) => (token.kind === "ident" ? token.text : undefined)));
  } catch {
    return [];
  }
}

function mergeRoleNames(roles: readonly (string | undefined)[]): string[] {
  const result: string[] = [];
  for (const role of roles) {
    const canonical = canonicalRoleName(role);
    if (canonical !== undefined && !result.includes(canonical)) result.push(canonical);
  }
  return result;
}
