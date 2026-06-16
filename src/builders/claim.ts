import {
  Acrobat,
  Balloonist,
  Chambermaid,
  Chef,
  Clockmaker,
  Courtier,
  Dreamer,
  Empath,
  FortuneTeller,
  Gambler,
  Gossip,
  Investigator,
  Juggler,
  Knight,
  Klutz,
  Legionary,
  Librarian,
  Mathematician,
  Noble,
  Nightwatchman,
  Oracle,
  Philosopher,
  Ravenkeeper,
  Sage,
  Savant,
  Seamstress,
  Shugenja,
  Slayer,
  SnakeCharmer,
  Steward,
  Undertaker,
  VillageIdiot,
  Virgin,
  Washerwoman,
  type InfoClaimBuilder,
  type Role,
} from "../model/characters";
import type { Timing } from "../model/model";
import { compile, type CompileCtx } from "../dsl/compile";
import type { Claim } from "../schema/puzzleDoc";
import { resolveRoleRef } from "./roleRef";
import { roleByName } from "../model/roleRegistry";

function timingOf(t: string | undefined): Timing | undefined {
  return t as Timing | undefined;
}

export function buildClaim(claim: Claim, ctx: Omit<CompileCtx, "nameRoot">): Role {
  const timing = timingOf(claim.timing);
  const base = {
    name: claim.name,
    timing,
    extraPossibleActualRoles: claim.extraPossibleActualRoles?.map(resolveRoleRef),
    infoClaims: customInfoClaims(claim, ctx),
  };

  switch (claim.type) {
    case "Acrobat":
      return new Acrobat({
        ...base,
        choices: claim.choices?.map((choice) => ({
          player: choice.player,
          timing: timingOf(choice.timing),
          died: choice.died,
        })),
      });
    case "Investigator":
      return new Investigator({
        ...base,
        minionRole: claim.minionRole ? resolveRoleRef(claim.minionRole) : undefined,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
        among: claim.among,
      });
    case "Librarian":
      return new Librarian({
        ...base,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
        outsiderCount: claim.outsiderCount,
        among: claim.among,
        registers: claim.registers,
      });
    case "Washerwoman":
      return new Washerwoman({
        ...base,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
        among: claim.among,
        registers: claim.registers,
      });
    case "Chef":
      return new Chef({ ...base, count: claim.count, registers: claim.registers });
    case "Chambermaid":
      return new Chambermaid({
        ...base,
        checks: claim.checks?.map((check) => ({
          left: check.left,
          right: check.right,
          count: check.count,
          timing: timingOf(check.timing),
        })),
      });
    case "Empath":
      return new Empath({ ...base, count: claim.count, player: claim.player, neighbors: claim.neighbors });
    case "FortuneTeller":
      return new FortuneTeller({
        ...base,
        checks: claim.checks.map((c) => ({
          left: c.left,
          right: c.right,
          yes: c.yes,
          demonRole: c.demonRole ? resolveRoleRef(c.demonRole) : undefined,
          registers: c.registers,
          timing: timingOf(c.timing),
        })),
      });
    case "Undertaker":
      return new Undertaker({
        ...base,
        player: claim.player,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
      });
    case "Legionary":
      return new Legionary({
        ...base,
        counts: claim.counts?.map((entry) => ({
          count: entry.count,
          timing: timingOf(entry.timing),
          alivePlayers: entry.alivePlayers,
        })),
      });
    case "Noble":
      return new Noble({
        ...base,
        oneEvilAmong: claim.oneEvilAmong,
        among: claim.among,
        evilCount: claim.evilCount,
      });
    case "Oracle":
      return new Oracle({ ...base, count: claim.count, deadPlayers: claim.deadPlayers });
    case "Steward":
      return new Steward({ ...base, goodPlayer: claim.goodPlayer });
    case "Knight":
      return new Knight({ ...base, noDemonAmong: claim.noDemonAmong });
    case "Gambler":
      return new Gambler({
        ...base,
        guesses: claim.guesses?.map((guess) => ({
          player: guess.player,
          role: resolveRoleRef(guess.role),
          timing: timingOf(guess.timing),
          survived: guess.survived,
        })),
      });
    case "Gossip":
      return new Gossip({
        ...base,
        statements: claim.statements?.map((statement, index) => ({
          timing: timingOf(statement.timing),
          killed: statement.killed,
          statement: (game) =>
            compile(statement.expression, game, {
              ...ctx,
              nameRoot: `${slug(claim.name)}_gossip_statement_${index + 1}`,
            }),
        })),
      });
    case "Philosopher":
      return new Philosopher({ ...base, role: claim.role ? resolveRoleRef(claim.role) : undefined });
    case "Klutz":
      return new Klutz({ ...base, chosen: claim.chosen, lost: claim.lost });
    case "Seamstress":
      return new Seamstress({ ...base, among: claim.among, aligned: claim.aligned });
    case "Juggler": {
      const guesses: Record<string, ReturnType<typeof resolveRoleRef>> = {};
      for (const [player, roleName] of Object.entries(claim.guesses)) guesses[player] = resolveRoleRef(roleName);
      return new Juggler({ ...base, guesses, correctCount: claim.correctCount });
    }
    case "Dreamer":
      return new Dreamer({ ...base, player: claim.player, roles: claim.roles.map(resolveRoleRef) });
    case "Shugenja":
      return new Shugenja({ ...base, evilDirection: claim.evilDirection });
    case "Clockmaker":
      return new Clockmaker({ ...base, distance: claim.distance });
    case "Courtier":
      return new Courtier({
        ...base,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
        drunkTimings: claim.drunkTimings?.map((timing) => timingOf(timing) as Timing),
      });
    case "Mathematician":
      return new Mathematician({
        ...base,
        malfunctions: claim.malfunctions?.map((entry) => ({
          timing: timingOf(entry.timing) as Timing,
          count: entry.count,
        })),
      });
    case "Ravenkeeper":
      return new Ravenkeeper({
        ...base,
        player: claim.player,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
      });
    case "Sage":
      return new Sage({ ...base, demonAmong: claim.demonAmong });
    case "Slayer":
      return new Slayer({ ...base, target: claim.target, killed: claim.killed, gameContinued: claim.gameContinued });
    case "Snake Charmer":
      return new SnakeCharmer({ ...base, checked: claim.checked, demon: claim.demon });
    case "VillageIdiot":
      return new VillageIdiot({
        ...base,
        checks: claim.checks.map((c) => ({ player: c.player, good: c.good, timing: timingOf(c.timing) })),
      });
    case "Virgin":
      return new Virgin({ ...base, nominator: claim.nominator, executed: claim.executed });
    case "Balloonist":
      return new Balloonist({
        ...base,
        differentCharacterTypePairs: claim.differentCharacterTypePairs.map((p) => [p[0], p[1]] as [string, string]),
      });
    case "Savant":
      return new Savant({
        ...base,
        statements: claim.statements.map(
          (stmt, stmtIdx) => (game) =>
            stmt.options.map((src, optIdx) =>
              compile(src, game, {
                players: ctx.players,
                script: ctx.script,
                nameRoot: `${slug(claim.name)}_savant_stmt${stmtIdx}_opt${optIdx}`,
              }),
            ),
        ),
      });
    case "Nightwatchman":
      return new Nightwatchman({ ...base, chosen: claim.chosen, learned: claim.learned });
    default: {
      const klass = roleByName(claim.type) as unknown as new (opts: { name: string; timing?: Timing }) => Role;
      return new klass({ ...base });
    }
  }
}

function customInfoClaims(claim: Claim, ctx: Omit<CompileCtx, "nameRoot">): InfoClaimBuilder[] {
  return (claim.info ?? []).flatMap((info, index) => {
    const expression = info.expression?.trim();
    if (!expression) return [];
    return [
      {
        timing: timingOf(info.timing),
        role: info.role ? resolveRoleRef(info.role) : undefined,
        learned: (game) =>
          compile(expression, game, {
            ...ctx,
            nameRoot: `${slug(claim.name)}_custom_info_${index + 1}`,
          }),
      },
    ];
  });
}

function slug(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_+|_+$/g, "");
}
