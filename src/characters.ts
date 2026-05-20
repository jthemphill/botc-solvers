import {
  Alignment,
  CharacterType,
  type RoleClass,
  type RoleRef,
  roleAlignment,
  roleCharacterType,
  roleName,
} from "./core";
import type { BoolLike, BoolVar, BOTCModel } from "./model";
import * as predicates from "./predicates";

export type StatementResult = BoolLike | readonly BoolLike[];
export type StatementFactory = (game: BOTCModel) => StatementResult;
export type StatementBuilder = StatementResult | StatementFactory;
export type ClaimPredicate = (game: BOTCModel, context: unknown) => BoolLike;
export type InfoClaimBuilder = BoolLike | ClaimPredicate | InfoClaim;

export interface InfoClaim {
  readonly role?: RoleRef;
  readonly learned: BoolLike | ClaimPredicate;
  readonly poisonContext?: string;
  readonly falseWhenVortox?: boolean;
}

export interface RoleBaseOptions {
  readonly name: string;
  readonly poisonContext?: string;
  readonly infoClaims?: readonly InfoClaimBuilder[];
}

export interface AppliedInfoClaim {
  readonly player: string;
  readonly role: RoleRef;
  readonly learned: BoolLike;
  readonly poisonContext?: string;
  readonly falseWhenVortox?: boolean;
  readonly context?: unknown;
}

export type ApplyInfoClaim = (game: BOTCModel, claim: AppliedInfoClaim) => void;

export interface ApplyClaimsOptions {
  readonly poisonContext?: string;
  readonly drunkRole?: RoleRef;
  readonly evilRoles?: readonly RoleRef[];
  readonly extraPossibleActualRoles?: readonly RoleRef[];
  readonly drunkThinksOutOfPlayRole?: boolean;
  readonly info?: ApplyInfoClaim;
  readonly context?: unknown;
}

function slug(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_+|_+$/g, "");
}

function claimName(player: string, role: RoleRef, suffix: string): string {
  return `${slug(player)}_${slug(roleName(role))}_${suffix}`;
}

function buildStatement(game: BOTCModel, player: string, index: number, statement: StatementBuilder): BoolVar {
  const resolved = typeof statement === "function" ? statement(game) : statement;
  if (Array.isArray(resolved))
    return Savant.learnsExactlyOne(game, resolved, claimName(player, Savant, `statement_${index}`));
  return resolved instanceof Object && "id" in resolved
    ? (resolved as BoolVar)
    : game.constantBool(Boolean(resolved), claimName(player, Savant, `statement_${index}_constant`));
}

function normalizeInfoClaim(claim: InfoClaimBuilder): InfoClaim {
  return claim instanceof Object && "learned" in claim ? (claim as InfoClaim) : { learned: claim };
}

function resolveInfoClaim(game: BOTCModel, context: unknown, claim: InfoClaim): BoolLike {
  return typeof claim.learned === "function" ? claim.learned(game, context) : claim.learned;
}

function addDefaultInfoClaim(game: BOTCModel, claim: AppliedInfoClaim): void {
  if (!claim.falseWhenVortox) {
    game.addTruthfulInfoClaim(claim.player, claim.role, claim.learned, { poisonContext: claim.poisonContext });
    return;
  }
  const active = game.allOf(
    [game.actualIs(claim.player, claim.role), game.poisoned(claim.player, claim.poisonContext).not()],
    `${claim.player}_${roleName(claim.role)}_sober_healthy_claim`,
  );
  game.addImplication(
    game.allOf([active, game.roleInPlay(Vortox)], `${claim.player}_${roleName(claim.role)}_vortox_claim`),
    game.not(claim.learned, `${claim.player}_${roleName(claim.role)}_vortox_false_claim`),
  );
  game.addImplication(
    game.allOf([active, game.roleInPlay(Vortox).not()], `${claim.player}_${roleName(claim.role)}_normal_claim`),
    claim.learned,
  );
}

function learnsRoleAmong(
  game: BOTCModel,
  players: readonly string[],
  role: RoleRef,
  name: string,
  registers = true,
): BoolVar {
  if (registers) return predicates.registersAsRoleAmong(game, players, role, name);
  const roleRef = roleName(role);
  return game.anyOf(
    players.map((player) => game.actualIs(player, roleRef)),
    `${name}_${players.join("_")}_actual_${roleRef}`,
  );
}

function learnsCharacterTypeCount(
  game: BOTCModel,
  players: readonly string[],
  characterType: CharacterType,
  count: number,
  name: string,
  registers = true,
): BoolVar {
  const options = registers
    ? players.map((player) => game.registersAsCharacterType(player, characterType, name))
    : players.map((player) => game.hasCharacterType(player, characterType));
  return game.boolSumEquals(options, count, `${name}_${characterType}_count_is_${count}`);
}

function directionalPlayers(game: BOTCModel, player: string, direction: "clockwise" | "anticlockwise"): string[] {
  const index = game.seating.indexOf(player);
  if (index === -1) throw new Error(`Unknown player: ${player}`);
  const result: string[] = [];
  for (let offset = 1; offset < game.seating.length; offset += 1) {
    const seat =
      direction === "clockwise"
        ? game.seating[(index + offset) % game.seating.length]
        : game.seating[(index - offset + game.seating.length) % game.seating.length];
    result.push(seat as string);
  }
  return result;
}

export abstract class Role {
  static readonly roleName: string;
  static readonly alignment: Alignment;
  static readonly characterType: CharacterType;

  readonly roleName: string;
  readonly alignment: Alignment;
  readonly characterType: CharacterType;
  readonly name: string;
  readonly poisonContext?: string;
  readonly infoClaims: readonly InfoClaim[];

  constructor(nameOrOptions: string | RoleBaseOptions, options: { readonly poisonContext?: string } = {}) {
    const resolvedName = typeof nameOrOptions === "string" ? nameOrOptions : nameOrOptions.name;
    const resolvedPoisonContext =
      typeof nameOrOptions === "string" ? options.poisonContext : nameOrOptions.poisonContext;
    const cls = this.constructor as unknown as RoleClass;
    this.name = resolvedName;
    this.roleName = cls.roleName;
    this.alignment = cls.alignment;
    this.characterType = cls.characterType;
    this.poisonContext = resolvedPoisonContext;
    this.infoClaims = typeof nameOrOptions === "string" ? [] : (nameOrOptions.infoClaims ?? []).map(normalizeInfoClaim);
  }

  static claim(
    this: RoleClass,
    game: BOTCModel,
    player: string,
    options: { readonly learned?: BoolLike; readonly poisonContext?: string; readonly drunkRole?: RoleRef } = {},
  ): void {
    game.addRoleClaim({ player, apparentRole: this }, { drunkRole: options.drunkRole ?? "Drunk" });
    if (options.learned !== undefined)
      game.addTruthfulInfoClaim(player, this, options.learned, { poisonContext: options.poisonContext });
  }

  learnedInfo(_game: BOTCModel): BoolLike | undefined {
    return undefined;
  }

  protected applyRoleClaim(game: BOTCModel, role: RoleRef, options: ApplyClaimsOptions = {}): void {
    const drunkRole = options.drunkRole ?? "Drunk";
    game.addRoleClaim(
      { player: this.name, apparentRole: role },
      {
        drunkRole,
        evilRoles: options.evilRoles,
        extraPossibleActualRoles: options.extraPossibleActualRoles,
        drunkThinksOutOfPlayRole: options.drunkThinksOutOfPlayRole,
      },
    );
  }

  protected applyInfoClaimBuilders(
    game: BOTCModel,
    role: RoleRef,
    claims: readonly InfoClaimBuilder[],
    options: ApplyClaimsOptions = {},
  ): void {
    const applyInfo = options.info ?? addDefaultInfoClaim;
    for (const claim of claims) {
      const resolvedClaim = normalizeInfoClaim(claim);
      applyInfo(game, {
        player: this.name,
        role: resolvedClaim.role ?? role,
        learned: resolveInfoClaim(game, options.context, resolvedClaim),
        poisonContext: resolvedClaim.poisonContext ?? this.poisonContext ?? options.poisonContext,
        falseWhenVortox: resolvedClaim.falseWhenVortox,
        context: options.context,
      });
    }
  }

  apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    const cls = this.constructor as RoleClass & typeof Role;
    this.applyRoleClaim(game, cls, options);
    const learned = this.learnedInfo(game);
    this.applyInfoClaimBuilders(
      game,
      cls,
      learned === undefined ? this.infoClaims : [{ learned }, ...this.infoClaims],
      options,
    );
  }
}

export class Imp extends Role {
  static readonly roleName = "Imp";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Demon;
}
export class NoDashii extends Role {
  static readonly roleName = "No Dashii";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Demon;
}
export class Leviathan extends Role {
  static readonly roleName = "Leviathan";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Demon;
}
export class LordOfTyphon extends Role {
  static readonly roleName = "Lord of Typhon";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Demon;
}
export class Pukka extends Role {
  static readonly roleName = "Pukka";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Demon;
}
export class Po extends Role {
  static readonly roleName = "Po";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Demon;
}
export class Vortox extends Role {
  static readonly roleName = "Vortox";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Demon;
}
export class Baron extends Role {
  static readonly roleName = "Baron";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class Goblin extends Role {
  static readonly roleName = "Goblin";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class Cerenovus extends Role {
  static readonly roleName = "Cerenovus";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class Marionette extends Role {
  static readonly roleName = "Marionette";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class PitHag extends Role {
  static readonly roleName = "Pit-Hag";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class EvilTwin extends Role {
  static readonly roleName = "Evil Twin";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;

  static pairedWith(game: BOTCModel, evilTwin: string, goodTwin: string, name: string): BoolVar {
    return game.allOf([game.actualIs(evilTwin, EvilTwin), game.isGood(goodTwin)], name);
  }

  static pairIsOneOf(game: BOTCModel, pairs: readonly (readonly [string, string])[], name: string): BoolVar {
    return game.anyOf(
      pairs.flatMap(([left, right]) => [
        EvilTwin.pairedWith(game, left, right, `${name}_${slug(left)}_${slug(right)}`),
        EvilTwin.pairedWith(game, right, left, `${name}_${slug(right)}_${slug(left)}`),
      ]),
      name,
    );
  }
}
export class Poisoner extends Role {
  static readonly roleName = "Poisoner";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class ScarletWoman extends Role {
  static readonly roleName = "Scarlet Woman";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class Spy extends Role {
  static readonly roleName = "Spy";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class Xaan extends Role {
  static readonly roleName = "Xaan";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class Witch extends Role {
  static readonly roleName = "Witch";
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}
export class Lunatic extends Role {
  static readonly roleName = "Lunatic";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}
export class Klutz extends Role {
  static readonly roleName = "Klutz";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}
export class Puzzlemaster extends Role {
  static readonly roleName = "Puzzlemaster";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}
export class Drunk extends Role {
  static readonly roleName = "Drunk";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}
export class Butler extends Role {
  static readonly roleName = "Butler";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}
export class Mutant extends Role {
  static readonly roleName = "Mutant";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}
export class Recluse extends Role {
  static readonly roleName = "Recluse";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}
export class Saint extends Role {
  static readonly roleName = "Saint";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}
export class Sweetheart extends Role {
  static readonly roleName = "Sweetheart";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}
export class Slayer extends Role {
  static readonly roleName = "Slayer";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Alsaahir extends Role {
  static readonly roleName = "Alsaahir";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Artist extends Role {
  static readonly roleName = "Artist";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Atheist extends Role {
  static readonly roleName = "Atheist";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Philosopher extends Role {
  static readonly roleName = "Philosopher";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Acrobat extends Role {
  static readonly roleName = "Acrobat";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Gambler extends Role {
  static readonly roleName = "Gambler";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Mathematician extends Role {
  static readonly roleName = "Mathematician";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Gossip extends Role {
  static readonly roleName = "Gossip";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Ravenkeeper extends Role {
  static readonly roleName = "Ravenkeeper";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Sage extends Role {
  static readonly roleName = "Sage";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class SnakeCharmer extends Role {
  static readonly roleName = "Snake Charmer";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}
export class Soldier extends Role {
  static readonly roleName = "Soldier";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Balloonist extends Role {
  static readonly roleName = "Balloonist";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly differentCharacterTypePairs: readonly [string, string][];
  constructor(
    options: RoleBaseOptions & {
      readonly differentCharacterTypePairs?: readonly [string, string][];
    },
  ) {
    super(options);
    this.differentCharacterTypePairs = options.differentCharacterTypePairs ?? [];
  }
  static learnsDifferentCharacterTypes(game: BOTCModel, pairs: readonly [string, string][], name: string): BoolVar {
    return game.allOf(
      pairs.map(([left, right]) => predicates.differentCharacterTypes(game, left, right)),
      name,
    );
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.differentCharacterTypePairs.length === 0
      ? undefined
      : Balloonist.learnsDifferentCharacterTypes(
          game,
          this.differentCharacterTypePairs,
          claimName(this.name, Balloonist, "different_types"),
        );
  }
}

export class Chef extends Role {
  static readonly roleName = "Chef";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly count?: number;
  readonly registers: boolean;
  constructor(
    options: RoleBaseOptions & {
      readonly count?: number;
      readonly registers?: boolean;
    },
  ) {
    super(options);
    this.count = options.count;
    this.registers = options.registers ?? true;
  }
  static learnsCount(
    game: BOTCModel,
    count: number,
    name: string,
    options: { readonly registers?: boolean } = {},
  ): BoolVar {
    return (options.registers ?? true)
      ? predicates.chefCountRegistersAs(game, count, name)
      : predicates.chefCountIs(game, count);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.count === undefined
      ? undefined
      : Chef.learnsCount(game, this.count, claimName(this.name, Chef, "count"), { registers: this.registers });
  }
}

export class Chambermaid extends Role {
  static readonly roleName = "Chambermaid";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Clockmaker extends Role {
  static readonly roleName = "Clockmaker";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly demonNextToMinion?: boolean;
  constructor(
    options: RoleBaseOptions & {
      readonly demonNextToMinion?: boolean;
    },
  ) {
    super(options);
    this.demonNextToMinion = options.demonNextToMinion;
  }
  static learnsDemonNextToMinion(game: BOTCModel, name: string): BoolVar {
    return game.anyOf(
      [
        ...game
          .adjacentPairs()
          .map(([left, right]) =>
            game.allOf([game.isDemon(left), game.isMinion(right)], `${left}_${right}_demon_minion_neighbors`),
          ),
        ...game
          .adjacentPairs()
          .map(([left, right]) =>
            game.allOf([game.isMinion(left), game.isDemon(right)], `${left}_${right}_minion_demon_neighbors`),
          ),
      ],
      name,
    );
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.demonNextToMinion === undefined) return undefined;
    const claim = Clockmaker.learnsDemonNextToMinion(game, claimName(this.name, Clockmaker, "demon_next_to_minion"));
    return this.demonNextToMinion
      ? claim
      : game.not(claim, claimName(this.name, Clockmaker, "demon_not_next_to_minion"));
  }
}

export class Courtier extends Role {
  static readonly roleName = "Courtier";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Dreamer extends Role {
  static readonly roleName = "Dreamer";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly player?: string;
  readonly roles: readonly RoleRef[];
  constructor(
    options: RoleBaseOptions & {
      readonly player?: string;
      readonly roles?: readonly RoleRef[];
    },
  ) {
    super(options);
    this.player = options.player;
    this.roles = options.roles ?? [];
  }
  static learnsOneOf(game: BOTCModel, player: string, roles: readonly RoleRef[], name: string): BoolVar {
    return game.boolSumEquals(
      roles.map((role) => game.actualIs(player, role)),
      1,
      name,
    );
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.player === undefined || this.roles.length === 0
      ? undefined
      : Dreamer.learnsOneOf(game, this.player, this.roles, claimName(this.name, Dreamer, "one_of"));
  }
}

export class Empath extends Role {
  static readonly roleName = "Empath";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly count?: number;
  readonly player?: string;
  constructor(
    options: RoleBaseOptions & {
      readonly count?: number;
      readonly player?: string;
    },
  ) {
    super(options);
    this.count = options.count;
    this.player = options.player;
  }
  static learnsCount(game: BOTCModel, player: string, count: number, name: string): BoolVar {
    const [left, right] = game.neighbors(player);
    return game.boolSumEquals(
      [game.registersAsEvil(left, name), game.registersAsEvil(right, name)],
      count,
      `${name}_empath_count_is_${count}`,
    );
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.count === undefined
      ? undefined
      : Empath.learnsCount(game, this.player ?? this.name, this.count, claimName(this.name, Empath, "count"));
  }
}

export interface FortuneTellerCheck {
  readonly left: string;
  readonly right: string;
  readonly yes: boolean;
  readonly name?: string;
  readonly demonRole?: RoleRef;
  readonly registers?: boolean;
  readonly poisonContext?: string;
}

export class FortuneTeller extends Role {
  static readonly roleName = "Fortune Teller";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly checks: readonly FortuneTellerCheck[];
  constructor(
    options: RoleBaseOptions & {
      readonly checks?: readonly FortuneTellerCheck[];
    },
  ) {
    super(options);
    this.checks = options.checks ?? [];
  }
  static learnsCheck(
    game: BOTCModel,
    left: string,
    right: string,
    options: {
      readonly yes: boolean;
      readonly name: string;
      readonly demonRole?: RoleRef;
      readonly registers?: boolean;
    },
  ): BoolVar {
    const choices =
      options.demonRole === undefined
        ? [game.isDemon(left), game.isDemon(right)]
        : options.registers
          ? [
              game.registersAsRole(left, options.demonRole, options.name),
              game.registersAsRole(right, options.demonRole, options.name),
            ]
          : [game.actualIs(left, options.demonRole), game.actualIs(right, options.demonRole)];
    const either = game.anyOf(choices, `${options.name}_${left}_${right}_either_demon`);
    return options.yes ? either : game.not(either, `${options.name}_${left}_${right}_neither_demon`);
  }
  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    if (this.checks.length === 0) {
      super.apply(game, options);
      return;
    }
    this.applyRoleClaim(game, FortuneTeller, options);
    this.checks.forEach((check, index) => {
      const name = check.name ?? claimName(this.name, FortuneTeller, `check_${index + 1}`);
      const learned = FortuneTeller.learnsCheck(game, check.left, check.right, {
        yes: check.yes,
        name,
        demonRole: check.demonRole,
        registers: check.registers ?? false,
      });
      this.applyInfoClaimBuilders(game, FortuneTeller, [{ learned, poisonContext: check.poisonContext }], options);
    });
    this.applyInfoClaimBuilders(game, FortuneTeller, this.infoClaims, options);
  }
}

export class Investigator extends Role {
  static readonly roleName = "Investigator";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly among: readonly string[];
  readonly role?: RoleRef;
  readonly minionRole?: RoleRef;
  readonly registers: boolean;
  constructor(
    options: RoleBaseOptions & {
      readonly among?: readonly string[];
      readonly role?: RoleRef;
      readonly minionRole?: RoleRef;
      readonly registers?: boolean;
    },
  ) {
    super(options);
    this.among = options.among ?? [];
    this.role = options.role;
    this.minionRole = options.minionRole;
    this.registers = options.registers ?? true;
  }
  static learnsRoleAmong(
    game: BOTCModel,
    players: readonly string[],
    role: RoleRef,
    name: string,
    options: { readonly registers?: boolean } = {},
  ): BoolVar {
    return learnsRoleAmong(game, players, role, name, options.registers ?? true);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    const role = this.role ?? this.minionRole;
    return role === undefined
      ? undefined
      : Investigator.learnsRoleAmong(game, this.among, role, claimName(this.name, Investigator, "role_among"), {
          registers: this.registers,
        });
  }
}

export class Juggler extends Role {
  static readonly roleName = "Juggler";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly guesses: ReadonlyMap<string, RoleRef>;
  readonly correctCount?: number;
  constructor(
    options: RoleBaseOptions & {
      readonly guesses?: ReadonlyMap<string, RoleRef> | Record<string, RoleRef>;
      readonly correctCount?: number;
    },
  ) {
    super(options);
    this.guesses = options.guesses instanceof Map ? options.guesses : new Map(Object.entries(options.guesses ?? {}));
    this.correctCount = options.correctCount;
  }
  static learnsCorrectCount(
    game: BOTCModel,
    guesses: ReadonlyMap<string, RoleRef> | Record<string, RoleRef>,
    count: number,
    name: string,
  ): BoolVar {
    const items = guesses instanceof Map ? [...guesses.entries()] : Object.entries(guesses);
    return game.boolSumEquals(
      items.map(([player, role]) => game.actualIs(player, role)),
      count,
      name,
    );
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.correctCount === undefined
      ? undefined
      : Juggler.learnsCorrectCount(
          game,
          this.guesses,
          this.correctCount,
          claimName(this.name, Juggler, "correct_count"),
        );
  }
}

export class Shugenja extends Role {
  static readonly roleName = "Shugenja";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly evilDirection?: "clockwise" | "anticlockwise";
  constructor(
    options: RoleBaseOptions & {
      readonly evilDirection?: "clockwise" | "anticlockwise";
    },
  ) {
    super(options);
    this.evilDirection = options.evilDirection;
  }
  static learnsNearestEvilDirection(
    game: BOTCModel,
    player: string,
    direction: "clockwise" | "anticlockwise",
    name: string,
  ): BoolVar {
    const toward = directionalPlayers(game, player, direction);
    const away = directionalPlayers(game, player, direction === "clockwise" ? "anticlockwise" : "clockwise");
    const possibilities = toward.map((towardPlayer, index) => {
      const noCloserToward = toward.slice(0, index).map((closer) => game.isEvil(closer).not());
      const noCloserAway = away.slice(0, index).map((closer) => game.isEvil(closer).not());
      return game.allOf(
        [game.isEvil(towardPlayer), ...noCloserToward, ...noCloserAway],
        `${name}_${towardPlayer}_nearest_${direction}`,
      );
    });
    return game.anyOf(possibilities, name);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.evilDirection === undefined
      ? undefined
      : Shugenja.learnsNearestEvilDirection(
          game,
          this.name,
          this.evilDirection,
          claimName(this.name, Shugenja, "nearest_evil_direction"),
        );
  }
}

export class Knight extends Role {
  static readonly roleName = "Knight";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly noDemonAmong: readonly string[];
  constructor(
    options: RoleBaseOptions & {
      readonly noDemonAmong?: readonly string[];
    },
  ) {
    super(options);
    this.noDemonAmong = options.noDemonAmong ?? [];
  }
  static learnsNoDemonAmong(game: BOTCModel, players: readonly string[], name: string): BoolVar {
    return game.not(
      game.anyOf(
        players.map((player) => game.isDemon(player)),
        `${name}_${players.join("_")}_any_demon`,
      ),
      `${name}_${players.join("_")}_no_demon`,
    );
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.noDemonAmong.length === 0
      ? undefined
      : Knight.learnsNoDemonAmong(game, this.noDemonAmong, claimName(this.name, Knight, "no_demon"));
  }
}

export interface VillageIdiotCheck {
  readonly player: string;
  readonly good: boolean;
  readonly name?: string;
}

export class VillageIdiot extends Role {
  static readonly roleName = "Village Idiot";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly checks: readonly VillageIdiotCheck[];
  constructor(
    options: RoleBaseOptions & {
      readonly checks?: readonly VillageIdiotCheck[];
    },
  ) {
    super(options);
    this.checks = options.checks ?? [];
  }
  static learnsCheck(game: BOTCModel, player: string, good: boolean, name: string): BoolVar {
    return good ? game.registersAsGood(player, name) : game.registersAsEvil(player, name);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.checks.length === 0
      ? undefined
      : game.allOf(
          this.checks.map((check, index) =>
            VillageIdiot.learnsCheck(
              game,
              check.player,
              check.good,
              check.name ?? claimName(this.name, VillageIdiot, `check_${index + 1}`),
            ),
          ),
          claimName(this.name, VillageIdiot, "checks"),
        );
  }
}

export class Virgin extends Role {
  static readonly roleName = "Virgin";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Librarian extends Role {
  static readonly roleName = "Librarian";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly among: readonly string[];
  readonly role?: RoleRef;
  readonly outsiderCount?: number;
  readonly registers: boolean;
  constructor(
    options: RoleBaseOptions & {
      readonly among?: readonly string[];
      readonly role?: RoleRef;
      readonly outsiderCount?: number;
      readonly registers?: boolean;
    },
  ) {
    super(options);
    this.among = options.among ?? [];
    this.role = options.role;
    this.outsiderCount = options.outsiderCount;
    this.registers = options.registers ?? true;
  }
  static learnsRoleAmong(
    game: BOTCModel,
    players: readonly string[],
    role: RoleRef,
    name: string,
    options: { readonly registers?: boolean } = {},
  ): BoolVar {
    return learnsRoleAmong(game, players, role, name, options.registers ?? true);
  }
  static learnsCharacterTypeCount(
    game: BOTCModel,
    players: readonly string[],
    characterType: CharacterType,
    count: number,
    name: string,
    options: { readonly registers?: boolean } = {},
  ): BoolVar {
    return learnsCharacterTypeCount(game, players, characterType, count, name, options.registers ?? true);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.role !== undefined)
      return Librarian.learnsRoleAmong(game, this.among, this.role, claimName(this.name, Librarian, "role_among"), {
        registers: this.registers,
      });
    if (this.outsiderCount !== undefined)
      return Librarian.learnsCharacterTypeCount(
        game,
        game.players,
        CharacterType.Outsider,
        this.outsiderCount,
        claimName(this.name, Librarian, "outsider_count"),
        { registers: this.registers },
      );
    return undefined;
  }
}

export class Legionary extends Role {
  static readonly roleName = "Legionary";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Mayor extends Role {
  static readonly roleName = "Mayor";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Noble extends Role {
  static readonly roleName = "Noble";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly oneEvilAmong: readonly string[];
  readonly among: readonly string[];
  readonly evilCount?: number;
  constructor(
    options: RoleBaseOptions & {
      readonly oneEvilAmong?: readonly string[];
      readonly among?: readonly string[];
      readonly evilCount?: number;
    },
  ) {
    super(options);
    this.oneEvilAmong = options.oneEvilAmong ?? [];
    this.among = options.among ?? [];
    this.evilCount = options.evilCount;
  }
  static learnsEvilCount(game: BOTCModel, players: readonly string[], count: number): BoolVar {
    return predicates.exactlyNEvil(game, players, count);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.oneEvilAmong.length > 0) return Noble.learnsEvilCount(game, this.oneEvilAmong, 1);
    return this.evilCount === undefined ? undefined : Noble.learnsEvilCount(game, this.among, this.evilCount);
  }
}

export class Oracle extends Role {
  static readonly roleName = "Oracle";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Nightwatchman extends Role {
  static readonly roleName = "Nightwatchman";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Savant extends Role {
  static readonly roleName = "Savant";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly statements: readonly StatementBuilder[];
  constructor(
    options: RoleBaseOptions & {
      readonly statements?: readonly StatementBuilder[];
    },
  ) {
    super(options);
    this.statements = options.statements ?? [];
  }
  static learnsExactlyOne(game: BOTCModel, statements: readonly BoolLike[], name: string): BoolVar {
    return game.boolSumEquals(statements, 1, name);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.statements.length === 0
      ? undefined
      : game.allOf(
          this.statements.map((statement, index) => buildStatement(game, this.name, index + 1, statement)),
          claimName(this.name, Savant, "all_statements"),
        );
  }
}

export class Seamstress extends Role {
  static readonly roleName = "Seamstress";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly among: readonly string[];
  readonly aligned?: boolean;
  constructor(
    options: RoleBaseOptions & {
      readonly among?: readonly string[];
      readonly aligned?: boolean;
    },
  ) {
    super(options);
    this.among = options.among ?? [];
    this.aligned = options.aligned;
  }
  static learnsSameAlignment(game: BOTCModel, left: string, right: string): BoolVar {
    return predicates.sameAlignment(game, left, right);
  }
  static learnsDifferentAlignment(game: BOTCModel, left: string, right: string): BoolVar {
    return predicates.differentAlignments(game, left, right);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.aligned === undefined) return undefined;
    const [left, right] = this.among;
    if (left === undefined || right === undefined) throw new Error("Seamstress needs two players.");
    return this.aligned
      ? Seamstress.learnsSameAlignment(game, left, right)
      : Seamstress.learnsDifferentAlignment(game, left, right);
  }
}

export class Steward extends Role {
  static readonly roleName = "Steward";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly goodPlayer?: string;
  constructor(options: RoleBaseOptions & { readonly goodPlayer?: string }) {
    super(options);
    this.goodPlayer = options.goodPlayer;
  }
  static learnsGoodPlayer(game: BOTCModel, player: string): BoolVar {
    return game.isGood(player);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.goodPlayer === undefined ? undefined : Steward.learnsGoodPlayer(game, this.goodPlayer);
  }
}

export class Undertaker extends Role {
  static readonly roleName = "Undertaker";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly player?: string;
  readonly role?: RoleRef;
  constructor(
    options: RoleBaseOptions & {
      readonly player?: string;
      readonly role?: RoleRef;
    },
  ) {
    super(options);
    this.player = options.player;
    this.role = options.role;
  }
  static learnsRole(game: BOTCModel, player: string, role: RoleRef): BoolVar {
    return game.actualIs(player, role);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.player === undefined || this.role === undefined
      ? undefined
      : Undertaker.learnsRole(game, this.player, this.role);
  }
}

export class Washerwoman extends Role {
  static readonly roleName = "Washerwoman";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly among: readonly string[];
  readonly role?: RoleRef;
  readonly registers: boolean;
  constructor(
    options: RoleBaseOptions & {
      readonly among?: readonly string[];
      readonly role?: RoleRef;
      readonly registers?: boolean;
    },
  ) {
    super(options);
    this.among = options.among ?? [];
    this.role = options.role;
    this.registers = options.registers ?? true;
  }
  static learnsRoleAmong(
    game: BOTCModel,
    players: readonly string[],
    role: RoleRef,
    name: string,
    options: { readonly registers?: boolean } = {},
  ): BoolVar {
    return learnsRoleAmong(game, players, role, name, options.registers ?? true);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.role === undefined
      ? undefined
      : Washerwoman.learnsRoleAmong(game, this.among, this.role, claimName(this.name, Washerwoman, "role_among"), {
          registers: this.registers,
        });
  }
}

export type ClaimRef = string | Role;

export function playerName(player: ClaimRef): string {
  return player instanceof Role ? player.name : player;
}

export function playerNames(players: readonly ClaimRef[]): string[] {
  const names: string[] = [];
  for (const player of players) {
    const name = playerName(player);
    if (!names.includes(name)) names.push(name);
  }
  return names;
}

export function applyClaims(game: BOTCModel, claims: readonly Role[], options: ApplyClaimsOptions = {}): void {
  for (const claim of claims) claim.apply(game, options);
}

export function script(...characters: RoleRef[]): RoleRef[] {
  return characters;
}

export function roleNames(
  characters: readonly RoleRef[],
  options: { readonly alignment?: Alignment; readonly characterType?: CharacterType } = {},
): string[] {
  return characters
    .filter(
      (character) =>
        (options.alignment === undefined || roleAlignment(character) === options.alignment) &&
        (options.characterType === undefined || roleCharacterType(character) === options.characterType),
    )
    .map(roleName);
}
