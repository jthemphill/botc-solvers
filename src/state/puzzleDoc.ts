import { KNIGHT_NO_DEMON_AMONG_MAX, type Claim, type PuzzleDoc } from "../schema/puzzleDoc";
import { scriptWithProtectedRoles, withProtectedScript } from "./scriptRoles";

export type PuzzleAction =
  | { type: "load"; doc: PuzzleDoc }
  | { type: "setTitle"; title: string }
  | { type: "setPlayerCount"; count: number }
  | { type: "addPlayer"; name: string }
  | { type: "removePlayer"; index: number }
  | { type: "renamePlayer"; index: number; name: string }
  | { type: "movePlayer"; index: number; direction: "up" | "down" }
  | { type: "setScript"; script: readonly string[] }
  | { type: "setFixedRoles"; fixedRoles: PuzzleDoc["fixedRoles"] }
  | { type: "addClaim"; claim: Claim }
  | { type: "updateClaim"; index: number; claim: Claim }
  | { type: "removeClaim"; index: number };

export const initialDoc: PuzzleDoc = {
  version: 1,
  title: "Untitled puzzle",
  players: ["Player 1", "Player 2", "Player 3", "Player 4", "Player 5", "Player 6", "Player 7"],
  script: [],
  claims: [],
};

function defaultPlayerName(existing: readonly string[]): string {
  for (let index = existing.length + 1; ; index += 1) {
    const name = `Player ${index}`;
    if (!existing.includes(name)) return name;
  }
}

function rewriteName(claim: Claim, oldName: string, newName: string): Claim {
  const remap = (s: string) => (s === oldName ? newName : s);
  const remapArr = (arr: readonly string[]) => arr.map(remap);
  const name = claim.name === oldName ? newName : claim.name;

  switch (claim.type) {
    case "Investigator":
      return { ...claim, name, among: remapArr(claim.among) };
    case "Librarian":
      return { ...claim, name, among: claim.among ? remapArr(claim.among) : claim.among };
    case "Washerwoman":
      return { ...claim, name, among: remapArr(claim.among) };
    case "Knight":
      return { ...claim, name, noDemonAmong: remapArr(claim.noDemonAmong) };
    case "Noble":
      return {
        ...claim,
        name,
        oneEvilAmong: claim.oneEvilAmong ? remapArr(claim.oneEvilAmong) : claim.oneEvilAmong,
        among: claim.among ? remapArr(claim.among) : claim.among,
      };
    case "Empath":
      return { ...claim, name, player: claim.player ? remap(claim.player) : claim.player };
    case "Undertaker":
      return { ...claim, name, player: remap(claim.player) };
    case "Dreamer":
      return { ...claim, name, player: remap(claim.player) };
    case "Steward":
      return { ...claim, name, goodPlayer: remap(claim.goodPlayer) };
    case "Seamstress":
      return { ...claim, name, among: [remap(claim.among[0]), remap(claim.among[1])] };
    case "Juggler": {
      const guesses: Record<string, string> = {};
      for (const [p, r] of Object.entries(claim.guesses)) guesses[remap(p)] = r;
      return { ...claim, name, guesses };
    }
    case "FortuneTeller":
      return {
        ...claim,
        name,
        checks: claim.checks.map((c) => ({ ...c, left: remap(c.left), right: remap(c.right) })),
      };
    case "VillageIdiot":
      return { ...claim, name, checks: claim.checks.map((c) => ({ ...c, player: remap(c.player) })) };
    case "Balloonist":
      return {
        ...claim,
        name,
        differentCharacterTypePairs: claim.differentCharacterTypePairs.map(
          (p) => [remap(p[0]), remap(p[1])] as readonly [string, string],
        ),
      };
    default:
      return { ...claim, name };
  }
}

function removeNameFromClaim(claim: Claim, name: string): Claim | undefined {
  if (claim.name === name) return undefined;
  // Strip references but leave the claim in place.
  const stripArr = (arr: readonly string[] | undefined) => arr?.filter((n) => n !== name);
  switch (claim.type) {
    case "Investigator":
    case "Librarian":
    case "Washerwoman":
      return { ...claim, among: stripArr(claim.among) ?? [] } as Claim;
    case "Knight":
      return { ...claim, noDemonAmong: stripArr(claim.noDemonAmong) ?? [] };
    case "Noble":
      return {
        ...claim,
        oneEvilAmong: stripArr(claim.oneEvilAmong),
        among: stripArr(claim.among),
      };
    case "Empath":
      return { ...claim, player: claim.player === name ? undefined : claim.player };
    case "Steward":
      return claim.goodPlayer === name ? { ...claim, goodPlayer: "" } : claim;
    case "Juggler": {
      const guesses: Record<string, string> = {};
      for (const [p, r] of Object.entries(claim.guesses)) if (p !== name) guesses[p] = r;
      return { ...claim, guesses };
    }
    case "Seamstress":
      return claim.among.includes(name) ? { ...claim, among: ["", ""] as const } : claim;
    case "FortuneTeller":
      return { ...claim, checks: claim.checks.filter((c) => c.left !== name && c.right !== name) };
    case "VillageIdiot":
      return { ...claim, checks: claim.checks.filter((c) => c.player !== name) };
    case "Dreamer":
    case "Undertaker":
      return claim.player === name ? { ...claim, player: "" } : claim;
    case "Balloonist":
      return {
        ...claim,
        differentCharacterTypePairs: claim.differentCharacterTypePairs.filter(([l, r]) => l !== name && r !== name),
      };
    default:
      return claim;
  }
}

function normalizeClaim(claim: Claim): Claim {
  if (claim.type === "Knight" && claim.noDemonAmong.length > KNIGHT_NO_DEMON_AMONG_MAX) {
    return { ...claim, noDemonAmong: claim.noDemonAmong.slice(0, KNIGHT_NO_DEMON_AMONG_MAX) };
  }
  return claim;
}

export function reducer(state: PuzzleDoc, action: PuzzleAction): PuzzleDoc {
  switch (action.type) {
    case "load":
      return withProtectedScript({ ...action.doc, claims: action.doc.claims.map(normalizeClaim) });
    case "setTitle":
      return { ...state, title: action.title };
    case "setPlayerCount": {
      const target = Math.max(0, Math.floor(action.count));
      if (target === state.players.length) return state;

      if (target > state.players.length) {
        const players = [...state.players];
        while (players.length < target) {
          const name = defaultPlayerName(players);
          players.push(name);
        }
        return { ...state, players };
      }

      const removed = new Set(state.players.slice(target));
      const players = state.players.filter((player) => !removed.has(player));
      const claims = state.claims.flatMap((claim) => {
        let next: Claim | undefined = claim;
        for (const name of removed) {
          if (next === undefined) break;
          next = removeNameFromClaim(next, name);
        }
        return next === undefined ? [] : [next];
      });
      const fixedRoles = state.fixedRoles?.filter((fixedRole) => !removed.has(fixedRole.name));
      return { ...state, players, claims, fixedRoles };
    }
    case "addPlayer":
      if (!action.name || state.players.includes(action.name)) return state;
      return {
        ...state,
        players: [...state.players, action.name],
      };
    case "removePlayer": {
      const name = state.players[action.index];
      if (name === undefined) return state;
      const players = state.players.filter((_, i) => i !== action.index);
      const claims = state.claims.flatMap((c) => {
        const next = removeNameFromClaim(c, name);
        return next === undefined ? [] : [next];
      });
      const fixedRoles = state.fixedRoles?.filter((fixedRole) => fixedRole.name !== name);
      return { ...state, players, claims, fixedRoles };
    }
    case "renamePlayer": {
      const oldName = state.players[action.index];
      if (oldName === undefined || !action.name || state.players.includes(action.name)) return state;
      const players = state.players.map((n, i) => (i === action.index ? action.name : n));
      const claims = state.claims.map((c) => rewriteName(c, oldName, action.name));
      const fixedRoles = state.fixedRoles?.map((fixedRole) =>
        fixedRole.name === oldName ? { ...fixedRole, name: action.name } : fixedRole,
      );
      return { ...state, players, claims, fixedRoles };
    }
    case "movePlayer": {
      const dir = action.direction === "up" ? -1 : 1;
      const j = action.index + dir;
      if (j < 0 || j >= state.players.length) return state;
      const players = [...state.players];
      const tmp = players[action.index] as string;
      players[action.index] = players[j] as string;
      players[j] = tmp;
      return { ...state, players };
    }
    case "setScript": {
      const script = scriptWithProtectedRoles(action.script, state);
      return { ...state, script };
    }
    case "setFixedRoles":
      return withProtectedScript({ ...state, fixedRoles: action.fixedRoles });
    case "addClaim":
      return withProtectedScript({ ...state, claims: [...state.claims, normalizeClaim(action.claim)] });
    case "updateClaim": {
      const claims = state.claims.map((c, i) => (i === action.index ? normalizeClaim(action.claim) : c));
      return withProtectedScript({ ...state, claims });
    }
    case "removeClaim":
      return { ...state, claims: state.claims.filter((_, i) => i !== action.index) };
  }
}
