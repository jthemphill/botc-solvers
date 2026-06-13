import {
  Acrobat,
  Alsaahir,
  Artist,
  Atheist,
  Balloonist,
  Butler,
  Chef,
  Clockmaker,
  Dreamer,
  Drunk,
  Empath,
  FortuneTeller,
  Gambler,
  Gossip,
  Investigator,
  Juggler,
  Klutz,
  Knight,
  Librarian,
  Lunatic,
  Mathematician,
  Mayor,
  Mutant,
  Noble,
  Puzzlemaster,
  Recluse,
  Sage,
  Saint,
  Savant,
  Seamstress,
  Shugenja,
  Shugenja as _Shugenja,
  Slayer,
  Soldier,
  Steward,
  Sweetheart,
  Undertaker,
  VillageIdiot,
  Virgin,
  Washerwoman,
  type Role,
} from "../model/characters";
import type { Timing } from "../model/model";
import { compile, type CompileCtx } from "../dsl/compile";
import type { Claim } from "../schema/puzzleDoc";
import { resolveRoleRef } from "./roleRef";

void _Shugenja; // keep Shugenja import even if not directly used below

function timingOf(t: string | undefined): Timing | undefined {
  return t as Timing | undefined;
}

const BARE_CLASSES: Record<string, new (opts: { name: string; timing?: Timing }) => Role> = {
  Recluse,
  Mayor,
  Soldier,
  Saint,
  Acrobat,
  Slayer,
  Virgin,
  Mathematician,
  Sage,
  Gossip,
  Gambler,
  Atheist,
  Alsaahir,
  Artist,
  Klutz,
  Puzzlemaster,
  Mutant,
  Sweetheart,
  Butler,
  Drunk,
  Lunatic,
};

export function buildClaim(claim: Claim, ctx: Omit<CompileCtx, "nameRoot">): Role {
  const timing = timingOf(claim.timing);
  const base = { name: claim.name, timing };

  switch (claim.type) {
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
        role: resolveRoleRef(claim.role),
        among: claim.among,
        registers: claim.registers,
      });
    case "Chef":
      return new Chef({ ...base, count: claim.count, registers: claim.registers });
    case "Empath":
      return new Empath({ ...base, count: claim.count, player: claim.player });
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
      return new Undertaker({ ...base, player: claim.player, role: resolveRoleRef(claim.role) });
    case "Noble":
      return new Noble({
        ...base,
        oneEvilAmong: claim.oneEvilAmong,
        among: claim.among,
        evilCount: claim.evilCount,
      });
    case "Steward":
      return new Steward({ ...base, goodPlayer: claim.goodPlayer });
    case "Knight":
      return new Knight({ ...base, noDemonAmong: claim.noDemonAmong });
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
      return new Clockmaker({ ...base, demonNextToMinion: claim.demonNextToMinion });
    case "VillageIdiot":
      return new VillageIdiot({
        ...base,
        checks: claim.checks.map((c) => ({ player: c.player, good: c.good })),
      });
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
    default: {
      const klass = BARE_CLASSES[claim.type];
      if (klass === undefined) throw new Error(`Unsupported claim type: ${claim.type}`);
      return new klass({ ...base });
    }
  }
}

function slug(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_+|_+$/g, "");
}
