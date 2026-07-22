import {
  Acrobat,
  Assassin,
  Balloonist,
  Chambermaid,
  Chef,
  Clockmaker,
  Courtier,
  Dreamer,
  Empath,
  Exorcist,
  type EmpathNeighborOption,
  Flowergirl,
  FortuneTeller,
  Gambler,
  Godfather,
  Gossip,
  Grandmother,
  Investigator,
  Innkeeper,
  Juggler,
  Knight,
  Klutz,
  Legionary,
  Librarian,
  Mathematician,
  Noble,
  Nightwatchman,
  Oracle,
  type OracleDeadPlayerOption,
  Philosopher,
  Princess,
  Prodigy,
  Puzzlemaster,
  Ravenkeeper,
  Sage,
  Sailor,
  Savant,
  Seamstress,
  Shugenja,
  Slayer,
  SnakeCharmer,
  Steward,
  TownCrier,
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

export type ClaimWithTimelineContext = Claim & {
  readonly neighbors?: readonly string[];
  readonly neighborOptions?: readonly EmpathNeighborOption[];
  readonly deadPlayers?: readonly string[];
  readonly deadPlayerOptions?: readonly OracleDeadPlayerOption[];
  readonly alivePlayerCount?: number;
};

function timingOf(t: string | undefined): Timing | undefined {
  return t as Timing | undefined;
}

export function buildClaim(claim: ClaimWithTimelineContext, ctx: Omit<CompileCtx, "nameRoot">): Role {
  const timing = timingOf(claim.timing);
  const base = {
    name: claim.name,
    timing,
    possibleActualRoles: claim.possibleActualRoles?.map(resolveRoleRef),
    infoClaims: customInfoClaims(claim, ctx),
  };

  switch (claim.type) {
    case "Assassin":
      return new Assassin({ ...base, target: claim.target });
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
    case "Innkeeper":
      return new Innkeeper({
        ...base,
        choices: claim.choices?.map((choice) => ({
          players: choice.players,
          timing: timingOf(choice.timing),
        })),
      });
    case "Godfather":
      return new Godfather({
        ...base,
        outsiderRoles: claim.outsiderRoles?.map(resolveRoleRef),
      });
    case "Grandmother":
      return new Grandmother({
        ...base,
        grandchild: claim.grandchild,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
      });
    case "Sailor":
      return new Sailor({
        ...base,
        choices: claim.choices?.map((choice) => ({ player: choice.player, timing: timingOf(choice.timing) })),
      });
    case "Librarian":
      return new Librarian({
        ...base,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
        among: claim.among,
      });
    case "Washerwoman":
      return new Washerwoman({
        ...base,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
        among: claim.among,
      });
    case "Chef":
      return new Chef({ ...base, count: claim.count });
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
      return new Empath({
        ...base,
        count: claim.count,
        neighbors:
          claim.neighbors?.length === 2
            ? ([claim.neighbors[0] as string, claim.neighbors[1] as string] as readonly [string, string])
            : undefined,
        neighborOptions: claim.neighborOptions,
      });
    case "Exorcist":
      return new Exorcist({
        ...base,
        choices: claim.choices?.map((choice) => ({
          player: choice.player,
          timing: timingOf(choice.timing),
        })),
      });
    case "Flowergirl":
      return new Flowergirl({
        ...base,
        votes: claim.votes?.map((vote) => ({
          timing: timingOf(vote.timing) as Timing,
          voters: vote.voters,
          demonVoted: vote.demonVoted,
        })),
      });
    case "FortuneTeller":
      return new FortuneTeller({
        ...base,
        checks: claim.checks.map((c) => ({
          left: c.left,
          right: c.right,
          yes: c.yes,
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
      return new Oracle({
        ...base,
        count: claim.count,
        deadPlayers: claim.deadPlayers,
        deadPlayerOptions: claim.deadPlayerOptions,
      });
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
        })),
      });
    case "Gossip":
      return new Gossip({
        ...base,
        statements: claim.statements?.map((statement, index) => ({
          timing: timingOf(statement.timing),
          statement: (game) =>
            compile(statement.expression, game, {
              ...ctx,
              nameRoot: `${slug(claim.name)}_gossip_statement_${index + 1}`,
            }),
        })),
      });
    case "Philosopher":
      return new Philosopher({
        ...base,
        role: claim.role ? resolveRoleRef(claim.role) : undefined,
        infoClaims: [...base.infoClaims, ...philosopherInfoClaims(claim)],
      });
    case "Princess":
      return new Princess({
        ...base,
        nominations: claim.nominations?.map((nomination) => ({
          player: nomination.player,
          timing: timingOf(nomination.timing),
        })),
      });
    case "Prodigy":
      return new Prodigy({
        ...base,
        checks: claim.checks.map((check) => ({
          chosen: check.chosen,
          learned: check.learned,
          timing: timingOf(check.timing),
        })),
      });
    case "Puzzlemaster":
      return new Puzzlemaster({
        ...base,
        guesses: claim.guesses?.map((guess) => ({
          player: guess.player,
          learnedDemon: guess.learnedDemon,
          timing: timingOf(guess.timing),
        })),
      });
    case "Klutz":
      return new Klutz({ ...base, chosen: claim.chosen });
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
    case "Town Crier":
      return new TownCrier({
        ...base,
        checks: claim.checks.map((check) => ({
          timing: timingOf(check.timing) as Timing,
          nominators: check.nominators,
          minionNominated: check.minionNominated,
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
      return new Slayer({
        ...base,
        target: claim.target,
        killed: claim.killed,
        gameContinued: claim.killed === true ? true : claim.gameContinued,
        alivePlayerCount: claim.alivePlayerCount,
      });
    case "Snake Charmer":
      return new SnakeCharmer({
        ...base,
        infoClaims: [...base.infoClaims, ...snakeCharmerInfoClaims(claim)],
      });
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
      return new Nightwatchman({
        ...base,
        chosen: claim.chosen,
        learned: claim.learned,
        confirmedByChosen: claim.confirmedByChosen,
      });
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

function philosopherInfoClaims(claim: Extract<Claim, { readonly type: "Philosopher" }>): InfoClaimBuilder[] {
  const seamstress = claim.seamstress;
  if (seamstress === undefined || seamstress.aligned === undefined) return [];
  const [left, right] = seamstress.among;
  if (left === undefined || right === undefined) return [];

  return [
    {
      timing: timingOf(seamstress.timing ?? claim.timing),
      role: resolveRoleRef("Seamstress"),
      learned: (game) =>
        seamstress.aligned
          ? Seamstress.learnsSameAlignment(game, left, right)
          : Seamstress.learnsDifferentAlignment(game, left, right),
    },
  ];
}

function snakeCharmerInfoClaims(claim: Extract<Claim, { readonly type: "Snake Charmer" }>): InfoClaimBuilder[] {
  const checkClaims = claim.checks.map((check, index): InfoClaimBuilder => {
    const nameRoot = `${slug(claim.name)}_snake_charmer_check_${index + 1}`;
    const timing = timingOf(check.timing) as Timing;
    return {
      timing,
      learned: (game) => {
        const checkedIsDemon = game.isDemonAt(check.player, timing);
        return check.demon ? checkedIsDemon : game.not(checkedIsDemon, `${nameRoot}_not_demon`);
      },
    };
  });

  return checkClaims;
}

function slug(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_+|_+$/g, "");
}
