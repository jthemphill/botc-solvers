import { KNIGHT_NO_DEMON_AMONG_MAX, type Claim, type PuzzleDoc, type TimelineEventDoc } from "../schema/puzzleDoc";
import type { SerializableWorld } from "../worker/protocol";
import { scriptWithProtectedRoles, withProtectedScript } from "./scriptRoles";

export interface PuzzleState {
  readonly doc: PuzzleDoc;
  readonly solveResult?: readonly SerializableWorld[];
  readonly solveError?: string;
}

export type PuzzleDocAction =
  | { type: "load"; doc: PuzzleDoc }
  | { type: "setTitle"; title: string }
  | { type: "setPlayerCount"; count: number }
  | { type: "addPlayer"; name: string }
  | { type: "removePlayer"; index: number }
  | { type: "renamePlayer"; index: number; name: string }
  | { type: "movePlayer"; index: number; direction: "up" | "down" }
  | { type: "movePlayerTo"; fromIndex: number; toIndex: number }
  | { type: "setSetup"; setup: PuzzleDoc["setup"] }
  | { type: "setUniqueCharacters"; uniqueCharacters: PuzzleDoc["uniqueCharacters"] }
  | { type: "setScript"; script: readonly string[] }
  | { type: "setFixedRoles"; fixedRoles: PuzzleDoc["fixedRoles"] }
  | { type: "setForbiddenRoles"; forbiddenRoles: PuzzleDoc["forbiddenRoles"] }
  | { type: "setTimeline"; timeline: PuzzleDoc["timeline"] }
  | { type: "addClaim"; claim: Claim }
  | { type: "updateClaim"; index: number; claim: Claim }
  | { type: "removeClaim"; index: number };

export type SolveAction =
  | { type: "solve"; status: "started"; doc: PuzzleDoc }
  | { type: "solve"; status: "succeeded"; doc: PuzzleDoc; worlds: readonly SerializableWorld[] }
  | { type: "solve"; status: "failed"; doc: PuzzleDoc; message: string }
  | { type: "solve"; status: "cleared"; doc: PuzzleDoc };

export type PuzzleAction = PuzzleDocAction | SolveAction;

export const initialDoc: PuzzleDoc = {
  title: "Untitled puzzle",
  players: ["Player 1", "Player 2", "Player 3", "Player 4", "Player 5", "Player 6", "Player 7"],
  script: [],
  claims: [],
};

export const initialState: PuzzleState = {
  doc: initialDoc,
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
    case "Chambermaid":
      return {
        ...claim,
        name,
        checks: claim.checks?.map((c) => ({ ...c, left: remap(c.left), right: remap(c.right) })),
      };
    case "Knight":
      return { ...claim, name, noDemonAmong: remapArr(claim.noDemonAmong) };
    case "Noble":
      return {
        ...claim,
        name,
        oneEvilAmong: claim.oneEvilAmong ? remapArr(claim.oneEvilAmong) : claim.oneEvilAmong,
        among: claim.among ? remapArr(claim.among) : claim.among,
      };
    case "Oracle":
      return {
        ...claim,
        name,
        deadPlayers: claim.deadPlayers ? remapArr(claim.deadPlayers) : claim.deadPlayers,
      };
    case "Philosopher":
      return {
        ...claim,
        name,
        seamstress:
          claim.seamstress === undefined ? undefined : { ...claim.seamstress, among: remapArr(claim.seamstress.among) },
      };
    case "Empath": {
      return { ...claim, name };
    }
    case "Undertaker":
      return { ...claim, name, player: claim.player ? remap(claim.player) : claim.player };
    case "Dreamer":
      return { ...claim, name, player: claim.player ? remap(claim.player) : claim.player };
    case "Sage":
      return { ...claim, name, demonAmong: claim.demonAmong ? remapArr(claim.demonAmong) : claim.demonAmong };
    case "Slayer":
      return { ...claim, name, target: claim.target ? remap(claim.target) : claim.target };
    case "Snake Charmer":
      return {
        ...claim,
        name,
        checks: claim.checks.map((c) => ({ ...c, player: remap(c.player) })),
        evilTwin:
          claim.evilTwin === undefined ? undefined : { ...claim.evilTwin, player: remap(claim.evilTwin.player) },
      };
    case "Steward":
      return { ...claim, name, goodPlayer: claim.goodPlayer ? remap(claim.goodPlayer) : claim.goodPlayer };
    case "Seamstress":
      return { ...claim, name, among: claim.among.map(remap) };
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
    case "Chambermaid":
      return { ...claim, checks: claim.checks?.filter((c) => c.left !== name && c.right !== name) };
    case "Knight":
      return { ...claim, noDemonAmong: stripArr(claim.noDemonAmong) ?? [] };
    case "Noble":
      return {
        ...claim,
        oneEvilAmong: stripArr(claim.oneEvilAmong),
        among: stripArr(claim.among),
      };
    case "Oracle":
      return { ...claim, deadPlayers: stripArr(claim.deadPlayers) };
    case "Empath":
      return claim;
    case "Philosopher":
      return claim.seamstress?.among.includes(name) ? { ...claim, seamstress: undefined } : claim;
    case "Steward":
      return claim.goodPlayer === name ? { ...claim, goodPlayer: undefined } : claim;
    case "Juggler": {
      const guesses: Record<string, string> = {};
      for (const [p, r] of Object.entries(claim.guesses)) if (p !== name) guesses[p] = r;
      return { ...claim, guesses };
    }
    case "Seamstress":
      return claim.among.includes(name) ? { ...claim, among: [] } : claim;
    case "FortuneTeller":
      return { ...claim, checks: claim.checks.filter((c) => c.left !== name && c.right !== name) };
    case "VillageIdiot":
      return { ...claim, checks: claim.checks.filter((c) => c.player !== name) };
    case "Dreamer":
    case "Undertaker":
      return claim.player === name ? { ...claim, player: undefined } : claim;
    case "Sage":
      return { ...claim, demonAmong: stripArr(claim.demonAmong) };
    case "Slayer":
      return claim.target === name ? { ...claim, target: undefined } : claim;
    case "Snake Charmer":
      return {
        ...claim,
        checks: claim.checks.filter((c) => c.player !== name),
        evilTwin: claim.evilTwin?.player === name ? undefined : claim.evilTwin,
      };
    case "Balloonist":
      return {
        ...claim,
        differentCharacterTypePairs: claim.differentCharacterTypePairs.filter(([l, r]) => l !== name && r !== name),
      };
    default:
      return claim;
  }
}

function rewriteTimelineName(timeline: PuzzleDoc["timeline"], oldName: string, newName: string): PuzzleDoc["timeline"] {
  return timeline?.map((event) => {
    const next = {
      ...event,
      players: event.players.map((player) => (player === oldName ? newName : player)),
    };
    return event.caller === undefined ? next : { ...next, caller: event.caller === oldName ? newName : event.caller };
  });
}

function removeTimelineNames(timeline: PuzzleDoc["timeline"], removed: ReadonlySet<string>): PuzzleDoc["timeline"] {
  return timeline
    ?.map((event) => {
      const next = {
        ...event,
        players: event.players.filter((player) => !removed.has(player)),
      };
      if (event.caller === undefined) return next;
      return removed.has(event.caller) ? { ...next, caller: undefined } : next;
    })
    .filter((event) => event.players.length > 0);
}

export function sortTimelineEvents(timeline: readonly TimelineEventDoc[]): TimelineEventDoc[] {
  return timeline
    .map((event, index) => ({ event, index }))
    .sort(
      (left, right) =>
        timelineTimingOrder(left.event.timing) - timelineTimingOrder(right.event.timing) || left.index - right.index,
    )
    .map(({ event }) => event);
}

function timelineTimingOrder(timing: string): number {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) return Number.MAX_SAFE_INTEGER;
  const phase = match[1] as "night" | "day";
  return Number(match[2]) * 2 + (phase === "day" ? 1 : 0);
}

function normalizeTimeline(timeline: PuzzleDoc["timeline"], players: readonly string[]): PuzzleDoc["timeline"] {
  const knownPlayers = new Set(players);
  const normalized = (timeline ?? [])
    .map<TimelineEventDoc>((event) => {
      const eventPlayers = event.players.filter(
        (player, index) => knownPlayers.has(player) && event.players.indexOf(player) === index,
      );
      return {
        ...event,
        players: event.type === "execution" ? eventPlayers.slice(0, 1) : eventPlayers,
        caller: event.caller === undefined || knownPlayers.has(event.caller) ? event.caller : undefined,
      };
    })
    .filter((event) => event.players.length > 0);
  return normalized.length === 0 ? undefined : sortTimelineEvents(normalized);
}

function slayerShotEventForClaim(claim: Claim): TimelineEventDoc | undefined {
  if (claim.type !== "Slayer" || claim.killed !== true || claim.target === undefined || claim.target === "") {
    return undefined;
  }
  return { timing: claim.timing ?? "day_1", type: "slayerShot", players: [claim.target] };
}

function removeSlayerShotEvent(
  timeline: PuzzleDoc["timeline"],
  claim: Claim | undefined,
  players: readonly string[],
): PuzzleDoc["timeline"] {
  const slayerShot = claim === undefined ? undefined : slayerShotEventForClaim(claim);
  if (slayerShot === undefined) return timeline;

  const next = (timeline ?? []).flatMap((event) => {
    if (
      event.type !== "slayerShot" ||
      event.timing !== slayerShot.timing ||
      !event.players.includes(slayerShot.players[0] as string)
    ) {
      return [event];
    }
    const players = event.players.filter((player) => player !== slayerShot.players[0]);
    return players.length === 0 ? [] : [{ ...event, players }];
  });

  return normalizeTimeline(next, players);
}

function ensureSlayerShotEvent(
  timeline: PuzzleDoc["timeline"],
  claim: Claim | undefined,
  players: readonly string[],
): PuzzleDoc["timeline"] {
  const slayerShot = claim === undefined ? undefined : slayerShotEventForClaim(claim);
  if (slayerShot === undefined) return timeline;

  const existing = timeline?.some(
    (event) =>
      event.type === slayerShot.type &&
      event.timing === slayerShot.timing &&
      event.players.includes(slayerShot.players[0] as string),
  );
  if (existing) return timeline;
  return normalizeTimeline([...(timeline ?? []), slayerShot], players);
}

function syncSlayerShotEvent(
  timeline: PuzzleDoc["timeline"],
  oldClaim: Claim | undefined,
  newClaim: Claim | undefined,
  players: readonly string[],
): PuzzleDoc["timeline"] {
  return ensureSlayerShotEvent(removeSlayerShotEvent(timeline, oldClaim, players), newClaim, players);
}

function normalizeClaim(claim: Claim): Claim {
  const { registers: _registers, ...claimWithoutLegacyRegisters } = claim as Claim & { readonly registers?: boolean };
  if (claimWithoutLegacyRegisters.type === "FortuneTeller") {
    claim = {
      ...claimWithoutLegacyRegisters,
      checks: claimWithoutLegacyRegisters.checks.map((check) => {
        const {
          registers: _checkRegisters,
          demonRole: _demonRole,
          ...checkWithoutLegacyOverrides
        } = check as typeof check & {
          readonly registers?: boolean;
          readonly demonRole?: string;
        };
        return checkWithoutLegacyOverrides;
      }),
    };
  } else {
    claim = claimWithoutLegacyRegisters;
  }
  if (claim.type === "Knight" && claim.noDemonAmong.length > KNIGHT_NO_DEMON_AMONG_MAX) {
    return { ...claim, noDemonAmong: claim.noDemonAmong.slice(0, KNIGHT_NO_DEMON_AMONG_MAX) };
  }
  if (claim.type === "Investigator") {
    const { minionRole, ...investigatorClaim } = claim;
    return {
      ...investigatorClaim,
      role: investigatorClaim.role ?? minionRole,
      among: investigatorClaim.among.slice(0, 2),
    };
  }
  if (claim.type === "Librarian" && claim.among !== undefined && claim.among.length > 2) {
    return { ...claim, among: claim.among.slice(0, 2) };
  }
  if (claim.type === "Washerwoman" && claim.among.length > 2) {
    return { ...claim, among: claim.among.slice(0, 2) };
  }
  if (claim.type === "Slayer") {
    const { gameContinued: _gameContinued, ...slayerClaim } = claim;
    return slayerClaim;
  }
  return claim;
}

function normalizeClaims(claim: Claim): Claim[] {
  const normalized = normalizeClaim(claim);
  if (normalized.type === "FortuneTeller" && normalized.checks.length > 1) {
    const { info: _info, ...claimWithoutInfo } = normalized;
    return normalized.checks.map((check, index) =>
      index === 0 ? { ...normalized, checks: [check] } : { ...claimWithoutInfo, checks: [check] },
    );
  }
  if (normalized.type === "Snake Charmer" && normalized.checks.length > 1) {
    const { info: _info, evilTwin: _evilTwin, ...claimWithoutSharedInfo } = normalized;
    return normalized.checks.map((check, index) =>
      index === 0 ? { ...normalized, checks: [check] } : { ...claimWithoutSharedInfo, checks: [check] },
    );
  }
  return [normalized];
}

export function docReducer(state: PuzzleDoc, action: PuzzleDocAction): PuzzleDoc {
  switch (action.type) {
    case "load":
      return withProtectedScript({
        ...action.doc,
        timeline: normalizeTimeline(action.doc.timeline, action.doc.players),
        claims: action.doc.claims.flatMap(normalizeClaims),
      });
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
      const forbiddenRoles = state.forbiddenRoles?.filter((forbiddenRole) => !removed.has(forbiddenRole.name));
      const timeline = removeTimelineNames(state.timeline, removed);
      return { ...state, players, claims, fixedRoles, forbiddenRoles, timeline };
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
      const forbiddenRoles = state.forbiddenRoles?.filter((forbiddenRole) => forbiddenRole.name !== name);
      const timeline = removeTimelineNames(state.timeline, new Set([name]));
      return { ...state, players, claims, fixedRoles, forbiddenRoles, timeline };
    }
    case "renamePlayer": {
      const oldName = state.players[action.index];
      if (oldName === undefined || !action.name || state.players.includes(action.name)) return state;
      const players = state.players.map((n, i) => (i === action.index ? action.name : n));
      const claims = state.claims.map((c) => rewriteName(c, oldName, action.name));
      const fixedRoles = state.fixedRoles?.map((fixedRole) =>
        fixedRole.name === oldName ? { ...fixedRole, name: action.name } : fixedRole,
      );
      const forbiddenRoles = state.forbiddenRoles?.map((forbiddenRole) =>
        forbiddenRole.name === oldName ? { ...forbiddenRole, name: action.name } : forbiddenRole,
      );
      const timeline = rewriteTimelineName(state.timeline, oldName, action.name);
      return { ...state, players, claims, fixedRoles, forbiddenRoles, timeline };
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
    case "movePlayerTo": {
      const fromIndex = Math.floor(action.fromIndex);
      const toIndex = Math.floor(action.toIndex);
      if (
        fromIndex === toIndex ||
        fromIndex < 0 ||
        toIndex < 0 ||
        fromIndex >= state.players.length ||
        toIndex >= state.players.length
      ) {
        return state;
      }
      const players = [...state.players];
      const [player] = players.splice(fromIndex, 1);
      if (player === undefined) return state;
      players.splice(toIndex, 0, player);
      return { ...state, players };
    }
    case "setSetup":
      return { ...state, setup: action.setup };
    case "setUniqueCharacters":
      return { ...state, uniqueCharacters: action.uniqueCharacters };
    case "setScript": {
      const script = scriptWithProtectedRoles(action.script, state);
      return { ...state, script };
    }
    case "setFixedRoles":
      return withProtectedScript({ ...state, fixedRoles: action.fixedRoles });
    case "setForbiddenRoles":
      return withProtectedScript({ ...state, forbiddenRoles: action.forbiddenRoles });
    case "setTimeline":
      return { ...state, timeline: normalizeTimeline(action.timeline, state.players) };
    case "addClaim":
      return withProtectedScript({
        ...state,
        claims: [...state.claims, ...normalizeClaims(action.claim)],
        timeline: ensureSlayerShotEvent(state.timeline, action.claim, state.players),
      });
    case "updateClaim": {
      const claims = state.claims.flatMap((c, i) => (i === action.index ? normalizeClaims(action.claim) : [c]));
      return withProtectedScript({
        ...state,
        claims,
        timeline: syncSlayerShotEvent(state.timeline, state.claims[action.index], action.claim, state.players),
      });
    }
    case "removeClaim": {
      return {
        ...state,
        claims: state.claims.filter((_, i) => i !== action.index),
        timeline: removeSlayerShotEvent(state.timeline, state.claims[action.index], state.players),
      };
    }
  }
}

export function reducer(state: PuzzleState, action: PuzzleAction): PuzzleState {
  if (action.type === "solve") {
    if (action.doc !== state.doc) return state;
    switch (action.status) {
      case "started":
      case "cleared":
        return { doc: state.doc };
      case "succeeded":
        return { doc: state.doc, solveResult: action.worlds };
      case "failed":
        return { doc: state.doc, solveError: action.message };
    }
  }

  const doc = docReducer(state.doc, action);
  return doc === state.doc ? state : { doc };
}
