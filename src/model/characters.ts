import { slug } from "./keys";
import {
  Alignment,
  CharacterType,
  type RoleClass,
  type RoleRef,
  type WakeRule,
  roleAlignment,
  roleCharacterType,
  roleName,
  roleWakeRule,
} from "./core";
import { day, night, type BoolLike, type BoolVar, type BOTCModel, type Timing } from "./model";
import * as predicates from "./predicates";

export type StatementResult = BoolLike | readonly BoolLike[];
export type StatementFactory = (game: BOTCModel) => StatementResult;
export type StatementBuilder = StatementResult | StatementFactory;
export type ClaimPredicate = (game: BOTCModel, context: unknown) => BoolLike;
export type InfoClaimBuilder = BoolLike | ClaimPredicate | InfoClaim;

interface TimedOptions {
  readonly timing?: Timing;
}

export interface InfoClaim {
  readonly role?: RoleRef;
  readonly learned: BoolLike | ClaimPredicate;
  readonly malfunctionLearned?: BoolLike | ClaimPredicate;
  readonly timing?: Timing;
  readonly vortoxAffected?: boolean;
}

export interface RoleBaseOptions {
  readonly roleTiming?: Timing;
  readonly name: string;
  readonly timing?: Timing;
  readonly claimAlignment?: Alignment;
  readonly possibleActualRoles?: readonly RoleRef[];
  readonly infoClaims?: readonly InfoClaimBuilder[];
}

export interface AppliedInfoClaim {
  readonly player: string;
  readonly role: RoleRef;
  readonly learned: BoolLike;
  readonly malfunctionLearned?: BoolLike;
  readonly timing: Timing;
  readonly vortoxAffected?: boolean;
  readonly context?: unknown;
}

export type ApplyInfoClaim = (game: BOTCModel, claim: AppliedInfoClaim) => void;

export interface ApplyClaimsOptions extends TimedOptions {
  readonly drunkRole?: RoleRef;
  readonly evilRoles?: readonly RoleRef[];
  readonly possibleActualRoles?: readonly RoleRef[];
  readonly info?: ApplyInfoClaim;
  readonly context?: unknown;
}

function claimName(player: string, role: RoleRef, suffix: string): string {
  return `${slug(player)}_${slug(roleName(role))}_${suffix}`;
}

function buildStatement(
  game: BOTCModel,
  player: string,
  index: number,
  statement: StatementBuilder,
  timing?: Timing,
): BoolVar {
  const resolved = typeof statement === "function" ? statement(game) : statement;
  if (Array.isArray(resolved)) {
    const exactlyOne = Savant.learnsExactlyOne(game, resolved, claimName(player, Savant, `statement_${index}`));
    if (timing === undefined || !game.characters.has("Vortox")) return exactlyOne;

    const activeVortox = game.anyOf(
      game.players.map((candidate) =>
        game.allOf(
          [game.hasAbilityAt(candidate, "Vortox", timing), game.soberAndHealthy(candidate, timing)],
          claimName(player, Savant, `statement_${index}_vortox_${candidate}`),
        ),
      ),
      claimName(player, Savant, `statement_${index}_active_vortox`),
    );
    const anyOptionTrue = game.anyOf(resolved, claimName(player, Savant, `statement_${index}_any_option_true`));
    return game.anyOf(
      [
        game.allOf([activeVortox.not(), exactlyOne], claimName(player, Savant, `statement_${index}_normal`)),
        game.allOf([activeVortox, anyOptionTrue], claimName(player, Savant, `statement_${index}_vortox`)),
      ],
      claimName(player, Savant, `statement_${index}_reported`),
    );
  }
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

function explicitTiming(options: TimedOptions): Timing | undefined {
  return options.timing;
}

function healthTimingForAbility(timing: Timing): Timing {
  const match = /^day_(\d+)$/.exec(timing);
  return match === null ? timing : (`night_${match[1]}` as Timing);
}

function addDefaultInfoClaim(game: BOTCModel, claim: AppliedInfoClaim): void {
  game.addInfoClaim({
    player: claim.player,
    role: claim.role,
    learned: claim.learned,
    malfunctionLearned: claim.malfunctionLearned,
    timing: claim.timing,
    vortoxAffected: claim.vortoxAffected,
  });
}

function learnsRoleAmong(game: BOTCModel, players: readonly string[], role: RoleRef, name: string): BoolVar {
  return predicates.registersAsRoleAmong(game, players, role, name);
}

function learnsCharacterTypeCount(
  game: BOTCModel,
  players: readonly string[],
  characterType: CharacterType,
  count: number,
  name: string,
): BoolVar {
  const options = players.map((player) => game.registersAsCharacterType(player, characterType, name));
  return game.boolSumEquals(options, count, `${name}_${characterType}_count_is_${count}`);
}

function directionalPlayers(game: BOTCModel, player: string, direction: "clockwise" | "anticlockwise"): string[] {
  const index = game.players.indexOf(player);
  if (index === -1) throw new Error(`Unknown player: ${player}`);
  const result: string[] = [];
  for (let offset = 1; offset < game.players.length; offset += 1) {
    const seat =
      direction === "clockwise"
        ? game.players[(index + offset) % game.players.length]
        : game.players[(index - offset + game.players.length) % game.players.length];
    result.push(seat as string);
  }
  return result;
}

function nightNumber(timing: Timing): number | undefined {
  const match = /^night_(\d+)$/.exec(timing);
  return match === null ? undefined : Number(match[1]);
}

function wakeRule(wakes: WakeRule["wakes"]): WakeRule {
  return { wakes };
}

export const Wakes = {
  never: wakeRule((game, _player, _timing, name) => game.constantBool(false, `${name}_never_wakes`)),
  firstNight: wakeRule((game, _player, timing, name) =>
    game.constantBool(nightNumber(timing) === 1, `${name}_wakes_first_night`),
  ),
  everyNight: wakeRule((game, _player, timing, name) =>
    game.constantBool(nightNumber(timing) !== undefined, `${name}_wakes_every_night`),
  ),
  everyNightExceptFirst: wakeRule((game, _player, timing, name) => {
    const number = nightNumber(timing);
    return game.constantBool(number !== undefined && number >= 2, `${name}_wakes_after_first_night`);
  }),
  secondNight: wakeRule((game, _player, timing, name) =>
    game.constantBool(nightNumber(timing) === 2, `${name}_wakes_second_night`),
  ),
  firstNightOrConditional(role: RoleRef): WakeRule {
    return wakeRule((game, player, timing, name) =>
      game.anyOf(
        [
          game.constantBool(nightNumber(timing) === 1, `${name}_wakes_first_night`),
          game.conditionalWakeAt(player, role, timing, `${name}_${slug(roleName(role))}_conditional_wake`),
        ],
        `${name}_${slug(roleName(role))}_first_night_or_conditional_wake`,
      ),
    );
  },
  untilAbilityUsed(role: RoleRef, schedule: WakeRule): WakeRule {
    return wakeRule((game, player, timing, name) =>
      game.allOf(
        [
          schedule.wakes(game, player, timing, name),
          game.abilityUsedBefore(player, role, timing, `${name}_${slug(roleName(role))}_not_yet_used`).not(),
        ],
        `${name}_${slug(roleName(role))}_wakes_until_used`,
      ),
    );
  },
  unlessPrevented(schedule: WakeRule): WakeRule {
    return wakeRule((game, player, timing, name) =>
      game.allOf(
        [
          schedule.wakes(game, player, timing, name),
          game.wakePreventedAt(player, timing, `${name}_wake_prevented`).not(),
        ],
        `${name}_wakes_unless_prevented`,
      ),
    );
  },
} as const;

export abstract class Role {
  readonly roleTiming?: Timing;
  static readonly roleName: string;
  static readonly alignment: Alignment;
  static readonly characterType: CharacterType;

  readonly roleName: string;
  readonly alignment: Alignment;
  readonly characterType: CharacterType;
  readonly maxCopies?: number;
  readonly name: string;
  readonly timing?: Timing;
  readonly claimAlignment?: Alignment;
  readonly possibleActualRoles?: readonly RoleRef[];
  readonly infoClaims: readonly InfoClaim[];

  constructor(nameOrOptions: string | RoleBaseOptions, options: TimedOptions = {}) {
    const resolvedName = typeof nameOrOptions === "string" ? nameOrOptions : nameOrOptions.name;
    const resolvedTiming = typeof nameOrOptions === "string" ? explicitTiming(options) : explicitTiming(nameOrOptions);
    const cls = this.constructor as unknown as RoleClass;
    this.name = resolvedName;
    this.roleName = cls.roleName;
    this.alignment = cls.alignment;
    this.characterType = cls.characterType;
    this.maxCopies = cls.maxCopies;
    this.timing = resolvedTiming;
    this.roleTiming = typeof nameOrOptions === "string" ? undefined : nameOrOptions.roleTiming;
    this.claimAlignment = typeof nameOrOptions === "string" ? undefined : nameOrOptions.claimAlignment;
    this.possibleActualRoles = typeof nameOrOptions === "string" ? undefined : nameOrOptions.possibleActualRoles;
    this.infoClaims = typeof nameOrOptions === "string" ? [] : (nameOrOptions.infoClaims ?? []).map(normalizeInfoClaim);
  }

  static claim(
    this: RoleClass,
    game: BOTCModel,
    player: string,
    options: { readonly learned?: BoolLike; readonly drunkRole?: RoleRef } & TimedOptions = {},
  ): void {
    game.addRoleClaim({ player, apparentRole: this }, { drunkRole: options.drunkRole ?? "Drunk" });
    if (options.learned !== undefined) {
      const timing = explicitTiming(options);
      if (timing === undefined)
        throw new Error(`${player}'s ${roleName(this)} info claim needs an explicit night or day.`);
      game.addTruthfulInfoClaim(player, this, options.learned, { timing });
    }
  }

  learnedInfo(_game: BOTCModel): BoolLike | undefined {
    return undefined;
  }

  protected applyRoleClaim(game: BOTCModel, role: RoleRef, options: ApplyClaimsOptions = {}): void {
    const drunkRole = options.drunkRole ?? "Drunk";
    game.addRoleClaim(
      { player: this.name, apparentRole: role, alignment: this.claimAlignment },
      {
        drunkRole,
        evilRoles: options.evilRoles,
        possibleActualRoles: this.possibleActualRoles ?? options.possibleActualRoles,
        timing: this.roleTiming ?? night(1),
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
    for (const [index, claim] of claims.entries()) {
      const resolvedClaim = normalizeInfoClaim(claim);
      const timing = this.claimTiming(explicitTiming(resolvedClaim) ?? explicitTiming(options), index);
      applyInfo(game, {
        player: this.name,
        role: resolvedClaim.role ?? role,
        learned: game.withTiming(timing, () => resolveInfoClaim(game, options.context, resolvedClaim)),
        malfunctionLearned:
          resolvedClaim.malfunctionLearned === undefined
            ? undefined
            : resolveInfoClaim(game, options.context, {
                learned: resolvedClaim.malfunctionLearned,
              }),
        timing,
        vortoxAffected: resolvedClaim.vortoxAffected,
        context: options.context,
      });
    }
  }

  protected defaultInfoTiming(_claimIndex: number): Timing | undefined {
    if (this.timing !== undefined) return this.timing;
    if (this.roleName === "Juggler") return night(2);
    if (
      [
        Balloonist.roleName,
        Chef.roleName,
        Clockmaker.roleName,
        Godfather.roleName,
        Grandmother.roleName,
        Investigator.roleName,
        Knight.roleName,
        Librarian.roleName,
        Noble.roleName,
        Shugenja.roleName,
        Steward.roleName,
        Washerwoman.roleName,
      ].includes(this.roleName)
    ) {
      return night(1);
    }
    if (
      [
        Chambermaid.roleName,
        Dreamer.roleName,
        Empath.roleName,
        FortuneTeller.roleName,
        Legionary.roleName,
        Mathematician.roleName,
        SnakeCharmer.roleName,
        VillageIdiot.roleName,
      ].includes(this.roleName)
    ) {
      return night(_claimIndex + 1);
    }
    return undefined;
  }

  protected claimTiming(timing: Timing | undefined, claimIndex = 0): Timing {
    const resolved = timing ?? this.defaultInfoTiming(claimIndex);
    if (resolved === undefined) {
      throw new Error(`${this.name}'s ${this.roleName} info claim needs an explicit night or day.`);
    }
    return resolved;
  }

  apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    const cls = this.constructor as RoleClass & typeof Role;
    this.applyRoleClaim(game, cls, options);
    const learned = game.withTiming(this.defaultInfoTiming(0), () => this.learnedInfo(game));
    this.applyInfoClaimBuilders(
      game,
      cls,
      learned === undefined ? this.infoClaims : [{ learned }, ...this.infoClaims],
      options,
    );
  }
}

abstract class DemonRole extends Role {
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Demon;
}

abstract class MinionRole extends Role {
  static readonly alignment = Alignment.Evil;
  static readonly characterType = CharacterType.Minion;
}

abstract class OutsiderRole extends Role {
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Outsider;
}

abstract class TownsfolkRole extends Role {
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
}

export class Imp extends DemonRole {
  static readonly roleName = "Imp";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNightExceptFirst);
}
export class FangGu extends DemonRole {
  static readonly roleName = "Fang Gu";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNightExceptFirst);
}
export class NoDashii extends DemonRole {
  static readonly roleName = "No Dashii";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNightExceptFirst);
}
export class Kazali extends DemonRole {
  static readonly roleName = "Kazali";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNight);
}
export class Leviathan extends DemonRole {
  static readonly roleName = "Leviathan";
  static readonly wake = Wakes.never;
}
export class Lleech extends DemonRole {
  static readonly roleName = "Lleech";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNight);
}
export class Legion extends DemonRole {
  static readonly roleName = "Legion";
  static readonly wake = Wakes.never;
  static readonly maxCopies = 6;
}
export class Riot extends DemonRole {
  static readonly roleName = "Riot";
  static readonly wake = Wakes.never;
}
export class LordOfTyphon extends DemonRole {
  static readonly roleName = "Lord of Typhon";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNightExceptFirst);
}
export class Pukka extends DemonRole {
  static readonly roleName = "Pukka";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNight);
}
export class Shabaloth extends DemonRole {
  static readonly roleName = "Shabaloth";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNightExceptFirst);
}
export class Zombuul extends DemonRole {
  static readonly roleName = "Zombuul";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNightExceptFirst);
}
export class Po extends DemonRole {
  static readonly roleName = "Po";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNightExceptFirst);
}
export class Vortox extends DemonRole {
  static readonly roleName = "Vortox";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNightExceptFirst);
}
export class Vigormortis extends DemonRole {
  static readonly roleName = "Vigormortis";
  static readonly wake = Wakes.unlessPrevented(Wakes.everyNightExceptFirst);
}
export class Baron extends MinionRole {
  static readonly roleName = "Baron";
  static readonly wake = Wakes.never;
}
export class Boffin extends MinionRole {
  static readonly roleName = "Boffin";
  static readonly wake = Wakes.firstNight;
}
export class Goblin extends MinionRole {
  static readonly roleName = "Goblin";
  static readonly wake = Wakes.never;
}
export class Godfather extends MinionRole {
  static readonly roleName = "Godfather";
  static readonly wake = Wakes.firstNightOrConditional("Godfather");
  readonly outsiderRoles: readonly RoleRef[];

  constructor(options: RoleBaseOptions & { readonly outsiderRoles?: readonly RoleRef[] }) {
    super(options);
    this.outsiderRoles = options.outsiderRoles ?? [];
  }

  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.outsiderRoles.length === 0) return undefined;
    const claimed = new Set(this.outsiderRoles.map(roleName));
    const outsiderRoles = [...game.characters.entries()]
      .filter(([, role]) => roleCharacterType(role) === CharacterType.Outsider)
      .map(([role]) => role);
    return game.allOf(
      outsiderRoles.map((role) =>
        claimed.has(role)
          ? game.roleInPlay(role)
          : game.not(game.roleInPlay(role), claimName(this.name, Godfather, `${role}_not_in_play`)),
      ),
      claimName(this.name, Godfather, "outsider_knowledge"),
    );
  }
}
export class Assassin extends MinionRole {
  static readonly roleName = "Assassin";
  static readonly wake = Wakes.untilAbilityUsed("Assassin", Wakes.everyNightExceptFirst);
  readonly target?: string;

  constructor(options: RoleBaseOptions & { readonly target?: string }) {
    super(options);
    this.target = options.target;
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Assassin, options);
    if (this.target !== undefined) {
      const timing = this.claimTiming(explicitTiming(options));
      game.registerAbilityUse(this.name, Assassin, timing, game.hasAbilityAt(this.name, Assassin, timing));
    }
    this.applyInfoClaimBuilders(game, Assassin, this.infoClaims, options);
  }
}
export class Mastermind extends MinionRole {
  static readonly roleName = "Mastermind";
  static readonly wake = Wakes.never;
}
export class Cerenovus extends MinionRole {
  static readonly roleName = "Cerenovus";
  static readonly wake = Wakes.everyNightExceptFirst;
}
export class DevilsAdvocate extends MinionRole {
  static readonly roleName = "Devil's Advocate";
  static readonly wake = Wakes.everyNight;
}
export class Marionette extends MinionRole {
  static readonly roleName = "Marionette";
  static readonly wake = Wakes.never;
}
export class PitHag extends MinionRole {
  static readonly roleName = "Pit-Hag";
  static readonly wake = Wakes.everyNightExceptFirst;
}
export class EvilTwin extends MinionRole {
  static readonly roleName = "Evil Twin";
  static readonly wake = Wakes.firstNight;

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
export class Poisoner extends MinionRole {
  static readonly roleName = "Poisoner";
  static readonly wake = Wakes.everyNight;
}
export class Widow extends MinionRole {
  static readonly roleName = "Widow";
  static readonly wake = Wakes.firstNight;
}
export class ScarletWoman extends MinionRole {
  static readonly roleName = "Scarlet Woman";
  static readonly wake = Wakes.never;
}
export class Spy extends MinionRole {
  static readonly roleName = "Spy";
  static readonly wake = Wakes.everyNight;
}
export class Xaan extends MinionRole {
  static readonly roleName = "Xaan";
  static readonly wake = Wakes.never;
}
export class Witch extends MinionRole {
  static readonly roleName = "Witch";
  static readonly wake = Wakes.everyNight;
}
export class Lunatic extends OutsiderRole {
  static readonly roleName = "Lunatic";
  static readonly wake = Wakes.everyNightExceptFirst;
}
export class Goon extends OutsiderRole {
  static readonly roleName = "Goon";
  static readonly wake = Wakes.never;
}
export class Moonchild extends OutsiderRole {
  static readonly roleName = "Moonchild";
  static readonly wake = Wakes.never;
}
export class Tinker extends OutsiderRole {
  static readonly roleName = "Tinker";
  static readonly wake = Wakes.never;
}
export class Klutz extends OutsiderRole {
  static readonly roleName = "Klutz";
  static readonly wake = Wakes.never;
  readonly chosen?: string;

  constructor(options: RoleBaseOptions & { readonly chosen?: string }) {
    super(options);
    this.chosen = options.chosen;
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Klutz, options);
    if (this.chosen === undefined) {
      this.applyInfoClaimBuilders(game, Klutz, this.infoClaims, options);
      return;
    }

    const timing = this.claimTiming(explicitTiming(options));
    const activeHealthy = game.allOf(
      [game.hasAbilityAt(this.name, Klutz, timing), game.soberAndHealthy(this.name, timing)],
      claimName(this.name, Klutz, "choice_active"),
    );
    game.addImplication(activeHealthy, game.isGood(this.chosen));
    this.applyInfoClaimBuilders(game, Klutz, this.infoClaims, options);
  }
}
export class Politician extends OutsiderRole {
  static readonly roleName = "Politician";
  static readonly wake = Wakes.never;
}
export class Puzzlemaster extends OutsiderRole {
  static readonly roleName = "Puzzlemaster";
  static readonly wake = Wakes.never;
  readonly guesses: readonly {
    readonly player: string;
    readonly learnedDemon: string;
    readonly timing?: Timing;
  }[];

  constructor(
    options: RoleBaseOptions & {
      readonly guesses?: readonly {
        readonly player: string;
        readonly learnedDemon: string;
        readonly timing?: Timing;
      }[];
    },
  ) {
    super(options);
    this.guesses = options.guesses ?? [];
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Puzzlemaster, options);
    for (const [index, guess] of this.guesses.entries()) {
      const timing = this.claimTiming(guess.timing ?? explicitTiming(options), index);
      const activeHealthy = game.allOf(
        [
          game.hasAbilityAt(this.name, Puzzlemaster, timing),
          game.soberAndHealthy(this.name, healthTimingForAbility(timing)),
        ],
        claimName(this.name, Puzzlemaster, `guess_${index + 1}_active`),
      );
      const guessedCorrect = game.puzzlemasterDrunk(
        guess.player,
        claimName(this.name, Puzzlemaster, `guess_${index + 1}_correct`),
      );
      const learnedDemon = game.isDemon(guess.learnedDemon);
      game.addImplication(
        game.allOf([activeHealthy, guessedCorrect], claimName(this.name, Puzzlemaster, `guess_${index + 1}_true`)),
        learnedDemon,
      );
      game.addImplication(
        game.allOf(
          [activeHealthy, guessedCorrect.not()],
          claimName(this.name, Puzzlemaster, `guess_${index + 1}_false`),
        ),
        learnedDemon.not(),
      );
    }
    this.applyInfoClaimBuilders(game, Puzzlemaster, this.infoClaims, options);
  }
}
export class Drunk extends OutsiderRole {
  static readonly roleName = "Drunk";
  static readonly wake = Wakes.never;
}
export class Hermit extends OutsiderRole {
  static readonly roleName = "Hermit";
  static readonly wake = Wakes.never;
}
export class Golem extends OutsiderRole {
  static readonly roleName = "Golem";
  static readonly wake = Wakes.never;
}
export class Butler extends OutsiderRole {
  static readonly roleName = "Butler";
  static readonly wake = Wakes.everyNight;
}
export class Damsel extends OutsiderRole {
  static readonly roleName = "Damsel";
  static readonly wake = Wakes.never;
}
export class Mutant extends OutsiderRole {
  static readonly roleName = "Mutant";
  static readonly wake = Wakes.never;
}
export class Recluse extends OutsiderRole {
  static readonly roleName = "Recluse";
  static readonly wake = Wakes.never;
}
export class Saint extends OutsiderRole {
  static readonly roleName = "Saint";
  static readonly wake = Wakes.never;
}
export class Sweetheart extends OutsiderRole {
  static readonly roleName = "Sweetheart";
  static readonly wake = Wakes.never;
}
export class Slayer extends TownsfolkRole {
  static readonly roleName = "Slayer";
  static readonly wake = Wakes.never;
  readonly target?: string;
  readonly killed?: boolean;
  readonly gameContinued: boolean;
  readonly alivePlayerCount?: number;

  constructor(
    options: RoleBaseOptions & {
      readonly target?: string;
      readonly killed?: boolean;
      readonly gameContinued?: boolean;
      readonly alivePlayerCount?: number;
    },
  ) {
    super(options);
    this.target = options.target;
    this.killed = options.killed;
    this.gameContinued = options.gameContinued ?? options.killed === true;
    this.alivePlayerCount = options.alivePlayerCount;
  }

  static shotResult(game: BOTCModel, target: string, killed: boolean, timing: Timing, name: string): BoolVar {
    const registersAsDemon = game.registersAsCharacterTypeAt(target, CharacterType.Demon, timing, name);
    return killed ? registersAsDemon : game.not(registersAsDemon, `${name}_${target}_did_not_die`);
  }

  static actualDemonTarget(game: BOTCModel, target: string, name: string): BoolVar {
    const demonRoles = [...game.characters.entries()]
      .filter(([, character]) => roleCharacterType(character) === CharacterType.Demon)
      .map(([role]) => role);
    return game.anyOf(
      demonRoles.map((role) => game.actualIs(target, role)),
      `${name}_${target}_actual_demon`,
    );
  }

  static scarletWomanCanCatch(game: BOTCModel, name: string, alivePlayerCount = game.players.length): BoolVar {
    return alivePlayerCount >= 5 && game.characters.has("Scarlet Woman")
      ? game.roleInPlay("Scarlet Woman")
      : game.constantBool(false, `${name}_no_scarlet_woman_to_catch`);
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Slayer, options);
    if (this.target === undefined || this.killed === undefined) {
      this.applyInfoClaimBuilders(game, Slayer, this.infoClaims, options);
      return;
    }

    const timing = this.claimTiming(explicitTiming(options));
    const activeHealthy = game.allOf(
      [game.hasAbilityAt(this.name, Slayer, timing), game.soberAndHealthy(this.name, healthTimingForAbility(timing))],
      claimName(this.name, Slayer, "shot_active"),
    );
    if (this.killed) game.addTruth(activeHealthy);
    game.addImplication(
      activeHealthy,
      Slayer.shotResult(game, this.target, this.killed, timing, claimName(this.name, Slayer, "shot")),
    );
    if (this.killed && this.gameContinued) {
      game.addImplication(
        Slayer.actualDemonTarget(game, this.target, claimName(this.name, Slayer, "shot")),
        Slayer.scarletWomanCanCatch(game, claimName(this.name, Slayer, "shot_continued"), this.alivePlayerCount),
      );
    }
    this.applyInfoClaimBuilders(game, Slayer, this.infoClaims, options);
  }
}

export class Alsaahir extends TownsfolkRole {
  static readonly roleName = "Alsaahir";
  static readonly wake = Wakes.never;
}

export class Artist extends TownsfolkRole {
  static readonly roleName = "Artist";
  static readonly wake = Wakes.never;
}

export class Atheist extends TownsfolkRole {
  static readonly roleName = "Atheist";
  static readonly wake = Wakes.never;
}

export class Philosopher extends TownsfolkRole {
  static readonly roleName = "Philosopher";
  static readonly wake = Wakes.untilAbilityUsed("Philosopher", Wakes.everyNight);
  readonly role?: RoleRef;

  constructor(options: RoleBaseOptions & { readonly role?: RoleRef }) {
    super(options);
    this.role = options.role;
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Philosopher, options);
    if (this.role !== undefined) {
      const timing = this.claimTiming(explicitTiming(options));
      game.registerAbilityUse(this.name, Philosopher, timing, game.hasAbilityAt(this.name, Philosopher, timing));
      const activeHealthy = game.allOf(
        [game.actualIs(this.name, Philosopher), game.soberAndHealthy(this.name, timing)],
        claimName(this.name, Philosopher, "choice_active"),
      );
      game.gainAbility(this.name, this.role, timing, activeHealthy, "Philosopher");
    }
    this.applyInfoClaimBuilders(game, Philosopher, this.infoClaims, options);
  }
}

export class PoppyGrower extends TownsfolkRole {
  static readonly roleName = "Poppy Grower";
  static readonly wake = Wakes.never;
}

export class SolarProdigy extends TownsfolkRole {
  static readonly roleName = "Solar Prodigy";
  static readonly wake = Wakes.everyNight;
}

export class LunarProdigy extends TownsfolkRole {
  static readonly roleName = "Lunar Prodigy";
  static readonly wake = Wakes.everyNight;
}

export interface ProdigyCheck {
  readonly chosen: string;
  readonly learned: string;
  readonly timing?: Timing;
  readonly name?: string;
}

export class Prodigy extends TownsfolkRole {
  static readonly roleName = "Solar Prodigy";
  static readonly wake = Wakes.everyNight;
  readonly checks: readonly ProdigyCheck[];

  constructor(
    options: RoleBaseOptions & {
      readonly checks?: readonly ProdigyCheck[];
    },
  ) {
    super(options);
    this.checks = options.checks ?? [];
  }

  static learnsCheck(game: BOTCModel, check: ProdigyCheck, solar: boolean): BoolVar {
    return solar
      ? predicates.sameAlignment(game, check.chosen, check.learned)
      : predicates.differentAlignments(game, check.chosen, check.learned);
  }

  protected override defaultInfoTiming(claimIndex: number): Timing | undefined {
    return this.timing ?? night(claimIndex + 1);
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    const evilRoles =
      options.evilRoles ??
      [...game.characters.values()].filter((role) => roleAlignment(role) === Alignment.Evil).map(roleName);
    const possibleRoles: readonly RoleRef[] = this.possibleActualRoles ??
      options.possibleActualRoles ?? [
        SolarProdigy,
        LunarProdigy,
        ...evilRoles,
        ...(game.characters.has(Drunk.roleName) ? [Drunk] : []),
      ];
    game.setPossibleActualRoles(this.name, possibleRoles);
    this.checks.forEach((check, index) => {
      const timing = this.claimTiming(check.timing ?? explicitTiming(options), index);
      game.addInfoClaim({
        player: this.name,
        role: SolarProdigy,
        learned: Prodigy.learnsCheck(game, check, true),
        timing,
      });
      game.addInfoClaim({
        player: this.name,
        role: LunarProdigy,
        learned: Prodigy.learnsCheck(game, check, false),
        timing,
      });
    });
    this.applyInfoClaimBuilders(game, SolarProdigy, this.infoClaims, options);
  }
}

export class Acrobat extends TownsfolkRole {
  static readonly roleName = "Acrobat";
  static readonly wake = Wakes.everyNightExceptFirst;
  readonly choices: readonly AcrobatChoice[];

  constructor(
    options: RoleBaseOptions & {
      readonly choices?: readonly AcrobatChoice[];
    },
  ) {
    super(options);
    this.choices = options.choices ?? [];
  }

  static targetIsDrunkOrPoisoned(game: BOTCModel, player: string, timing: Timing, name: string): BoolVar {
    return game.anyOf([game.isDroisonedAt(player, timing), game.noDashiiPoisonedAt(player, timing)], name);
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Acrobat, options);
    this.choices.forEach((choice, index) => {
      const timing = this.claimTiming(choice.timing, index);
      const activeHealthy = game.allOf(
        [game.hasAbilityAt(this.name, Acrobat, timing), game.soberAndHealthy(this.name, timing)],
        claimName(this.name, Acrobat, `choice_${index + 1}_active`),
      );
      const targetDrunkOrPoisoned = Acrobat.targetIsDrunkOrPoisoned(
        game,
        choice.player,
        timing,
        claimName(this.name, Acrobat, `choice_${index + 1}_${choice.player}_drunk_or_poisoned`),
      );
      if (choice.died) game.addTruth(activeHealthy);
      game.addImplication(
        activeHealthy,
        choice.died
          ? targetDrunkOrPoisoned
          : game.not(targetDrunkOrPoisoned, claimName(this.name, Acrobat, `choice_${index + 1}_survived`)),
      );
    });
    this.applyInfoClaimBuilders(game, Acrobat, this.infoClaims, options);
  }
}

export class Grandmother extends TownsfolkRole {
  static readonly roleName = "Grandmother";
  static readonly wake = Wakes.firstNight;
  readonly grandchild?: string;
  readonly role?: RoleRef;

  constructor(options: RoleBaseOptions & { readonly grandchild?: string; readonly role?: RoleRef }) {
    super(options);
    this.grandchild = options.grandchild;
    this.role = options.role;
  }

  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.grandchild === undefined || this.role === undefined) return undefined;
    return game.allOf(
      [
        game.isGood(this.grandchild),
        game.registersAsRole(
          this.grandchild,
          this.role,
          claimName(this.name, Grandmother, `${this.grandchild}_${roleName(this.role)}`),
        ),
      ],
      claimName(this.name, Grandmother, "grandchild_info"),
    );
  }
}

export interface SailorChoice {
  readonly player: string;
  readonly timing?: Timing;
}

export class Sailor extends TownsfolkRole {
  static readonly roleName = "Sailor";
  static readonly wake = Wakes.everyNight;
  readonly choices: readonly SailorChoice[];

  constructor(options: RoleBaseOptions & { readonly choices?: readonly SailorChoice[] }) {
    super(options);
    this.choices = options.choices ?? [];
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Sailor, options);
    this.choices.forEach((choice, index) => {
      const timing = this.claimTiming(choice.timing, index);
      const match = /^night_(\d+)$/.exec(timing);
      const affectedTimings: Timing[] = [timing];
      if (match !== null) affectedTimings.push(`day_${match[1]}` as Timing);
      game.addNightlyChoiceDrunking(
        this.name,
        Sailor,
        timing,
        [this.name, choice.player],
        affectedTimings,
        claimName(this.name, Sailor, `choice_${index + 1}`),
      );
    });
    this.applyInfoClaimBuilders(game, Sailor, this.infoClaims, options);
  }
}

export interface InnkeeperChoice {
  readonly players: readonly string[];
  readonly timing?: Timing;
}

export class Innkeeper extends TownsfolkRole {
  static readonly roleName = "Innkeeper";
  static readonly wake = Wakes.everyNightExceptFirst;
  readonly choices: readonly InnkeeperChoice[];

  constructor(
    options: RoleBaseOptions & {
      readonly choices?: readonly InnkeeperChoice[];
    },
  ) {
    super(options);
    this.choices = options.choices ?? [];
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Innkeeper, options);
    this.choices.forEach((choice, index) => {
      if (choice.players.length !== 2 || new Set(choice.players).size !== 2 || choice.players.includes(this.name))
        return;
      const timing = this.claimTiming(choice.timing, index);
      const activeHealthy = game.allOf(
        [game.hasAbilityAt(this.name, Innkeeper, timing), game.soberAndHealthy(this.name, timing)],
        claimName(this.name, Innkeeper, `choice_${index + 1}_active`),
      );
      const match = /^night_(\d+)$/.exec(timing);
      const affectedTimings: Timing[] = [timing];
      if (match !== null) affectedTimings.push(`day_${match[1]}` as Timing);
      game.addPersistentDrunking(affectedTimings, {
        activeIf: activeHealthy,
        excludedPlayers: game.players.filter((player) => !choice.players.includes(player)),
        sourceName: claimName(this.name, Innkeeper, `choice_${index + 1}`),
      });
    });
    this.applyInfoClaimBuilders(game, Innkeeper, this.infoClaims, options);
  }
}

export class Professor extends TownsfolkRole {
  static readonly roleName = "Professor";
  static readonly wake = Wakes.untilAbilityUsed("Professor", Wakes.everyNightExceptFirst);
}

export class Minstrel extends TownsfolkRole {
  static readonly roleName = "Minstrel";
  static readonly wake = Wakes.never;
}

export class Pacifist extends TownsfolkRole {
  static readonly roleName = "Pacifist";
  static readonly wake = Wakes.never;
}

export class Fool extends TownsfolkRole {
  static readonly roleName = "Fool";
  static readonly wake = Wakes.never;
}

export interface AcrobatChoice {
  readonly player: string;
  readonly timing?: Timing;
  readonly died: boolean;
}

export class Gambler extends TownsfolkRole {
  static readonly roleName = "Gambler";
  static readonly wake = Wakes.everyNightExceptFirst;
  readonly guesses: readonly GamblerGuess[];

  constructor(
    options: RoleBaseOptions & {
      readonly guesses?: readonly GamblerGuess[];
    },
  ) {
    super(options);
    this.guesses = options.guesses ?? [];
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Gambler, options);
    this.applyInfoClaimBuilders(game, Gambler, this.infoClaims, options);
  }
}

export interface ExorcistChoice {
  readonly player: string;
  readonly timing?: Timing;
}

export class Exorcist extends TownsfolkRole {
  static readonly roleName = "Exorcist";
  static readonly wake = Wakes.everyNightExceptFirst;
  readonly choices: readonly ExorcistChoice[];

  constructor(
    options: RoleBaseOptions & {
      readonly choices?: readonly ExorcistChoice[];
    },
  ) {
    super(options);
    this.choices = options.choices ?? [];
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Exorcist, options);
    this.choices.forEach((choice, index) => {
      const timing = this.claimTiming(choice.timing ?? explicitTiming(options), index);
      game.preventWakeAt(
        choice.player,
        timing,
        game.allOf(
          [game.hasAbilityAt(this.name, Exorcist, timing), game.soberAndHealthy(this.name, timing)],
          claimName(this.name, Exorcist, `choice_${index + 1}_active`),
        ),
      );
    });
    this.applyInfoClaimBuilders(game, Exorcist, this.infoClaims, options);
  }
}

export interface GamblerGuess {
  readonly player: string;
  readonly role: RoleRef;
  readonly timing?: Timing;
}

export interface GossipStatement {
  readonly timing?: Timing;
  readonly statement: ClaimPredicate;
}

export class Gossip extends TownsfolkRole {
  static readonly roleName = "Gossip";
  static readonly wake = Wakes.never;
  readonly statements: readonly GossipStatement[];

  constructor(
    options: RoleBaseOptions & {
      readonly statements?: readonly GossipStatement[];
    },
  ) {
    super(options);
    this.statements = options.statements ?? [];
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Gossip, options);
    this.applyInfoClaimBuilders(game, Gossip, this.infoClaims, options);
  }
}

export class Mathematician extends TownsfolkRole {
  static readonly roleName = "Mathematician";
  static readonly wake = Wakes.everyNight;
  readonly malfunctions: readonly { readonly timing: Timing; readonly count: number }[];
  constructor(
    options: RoleBaseOptions & {
      readonly malfunctions?: readonly { readonly timing: Timing; readonly count: number }[];
    },
  ) {
    super(options);
    this.malfunctions = options.malfunctions ?? [];
  }
  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Mathematician, options);
    this.applyInfoClaimBuilders(
      game,
      Mathematician,
      this.malfunctions.map((entry) => ({
        timing: entry.timing,
        learned: (model: BOTCModel) =>
          model.malfunctionCountAt(
            entry.timing,
            entry.count,
            claimName(this.name, Mathematician, `${entry.timing}_${entry.count}_malfunctions`),
            this.name,
          ),
      })),
      options,
    );
    this.applyInfoClaimBuilders(game, Mathematician, this.infoClaims, options);
  }
}

export interface TownCrierCheck {
  readonly timing: Timing;
  readonly nominators: readonly string[];
  readonly minionNominated: boolean;
}

export class TownCrier extends TownsfolkRole {
  static readonly roleName = "Town Crier";
  static readonly wake = Wakes.everyNightExceptFirst;
  readonly checks: readonly TownCrierCheck[];

  constructor(options: RoleBaseOptions & { readonly checks?: readonly TownCrierCheck[] }) {
    super(options);
    this.checks = options.checks ?? [];
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, TownCrier, options);
    this.applyInfoClaimBuilders(
      game,
      TownCrier,
      this.checks.map((check) => ({
        timing: check.timing,
        learned: (model: BOTCModel) => {
          const aMinionNominated = model.anyOf(
            check.nominators.map((player) => model.hasCharacterType(player, CharacterType.Minion)),
            claimName(this.name, TownCrier, `${check.timing}_minion_nominated`),
          );
          return check.minionNominated ? aMinionNominated : aMinionNominated.not();
        },
      })),
      options,
    );
    this.applyInfoClaimBuilders(game, TownCrier, this.infoClaims, options);
  }
}

export interface PrincessNomination {
  readonly player: string;
  readonly timing?: Timing;
}

export class Princess extends TownsfolkRole {
  static readonly roleName = "Princess";
  static readonly wake = Wakes.never;
  readonly nominations: readonly PrincessNomination[];

  constructor(
    options: RoleBaseOptions & {
      readonly nominations?: readonly PrincessNomination[];
    },
  ) {
    super(options);
    this.nominations = options.nominations ?? [];
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Princess, options);
    this.applyInfoClaimBuilders(game, Princess, this.infoClaims, options);
  }
}

export class Ravenkeeper extends TownsfolkRole {
  static readonly roleName = "Ravenkeeper";
  static readonly wake = Wakes.never;
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

  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.player === undefined || this.role === undefined
      ? undefined
      : game.registersAsRole(this.player, this.role, claimName(this.name, Ravenkeeper, "role"));
  }
}

export class Sage extends TownsfolkRole {
  static readonly roleName = "Sage";
  static readonly wake = Wakes.never;
  readonly demonAmong: readonly string[];
  constructor(options: RoleBaseOptions & { readonly demonAmong?: readonly string[] }) {
    super(options);
    this.demonAmong = options.demonAmong ?? [];
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.demonAmong.length === 0
      ? undefined
      : game.anyOf(
          this.demonAmong.map((player) =>
            game.registersAsCharacterType(player, CharacterType.Demon, claimName(this.name, Sage, player)),
          ),
          claimName(this.name, Sage, "demon_among"),
        );
  }
}

export class SnakeCharmer extends TownsfolkRole {
  static readonly roleName = "Snake Charmer";
  static readonly wake = Wakes.everyNight;
  readonly checked?: string;
  readonly demon?: boolean;
  constructor(options: RoleBaseOptions & { readonly checked?: string; readonly demon?: boolean }) {
    super(options);
    this.checked = options.checked;
    this.demon = options.demon;
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.checked === undefined || this.demon === undefined) return undefined;
    const checkedIsDemon = game.isDemon(this.checked);
    return this.demon ? checkedIsDemon : game.not(checkedIsDemon, claimName(this.name, SnakeCharmer, "not_demon"));
  }
}
export class Soldier extends TownsfolkRole {
  static readonly roleName = "Soldier";
  static readonly wake = Wakes.never;
}

export class Balloonist extends TownsfolkRole {
  static readonly roleName = "Balloonist";
  static readonly wake = Wakes.everyNight;
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

export class Chef extends TownsfolkRole {
  static readonly roleName = "Chef";
  static readonly wake = Wakes.firstNight;
  readonly count?: number;
  constructor(
    options: RoleBaseOptions & {
      readonly count?: number;
    },
  ) {
    super(options);
    this.count = options.count;
  }
  static learnsCount(game: BOTCModel, count: number, name: string): BoolVar {
    return predicates.chefCountRegistersAs(game, count, name);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.count === undefined
      ? undefined
      : Chef.learnsCount(game, this.count, claimName(this.name, Chef, "count"));
  }
}

export interface ChambermaidCheck {
  readonly left: string;
  readonly right: string;
  readonly count: number;
  readonly timing?: Timing;
}

export class Chambermaid extends TownsfolkRole {
  static readonly roleName = "Chambermaid";
  static readonly wake = Wakes.everyNight;
  readonly checks: readonly ChambermaidCheck[];

  constructor(
    options: RoleBaseOptions & {
      readonly checks?: readonly ChambermaidCheck[];
    },
  ) {
    super(options);
    this.checks = options.checks ?? [];
  }

  static wakesDueToAbility(game: BOTCModel, player: string, timing: Timing, name: string): BoolVar {
    return game.anyOf(
      [...game.characters.entries()].map(([role, character]) =>
        game.allOf(
          [game.hasAbilityAt(player, role, timing), roleWakeRule(character).wakes(game, player, timing, name)],
          `${name}_${player}_${slug(role)}_woke_due_to_ability`,
        ),
      ),
      `${name}_${player}_woke_due_to_ability`,
    );
  }

  static learnsWakeCount(
    game: BOTCModel,
    players: readonly [string, string],
    count: number,
    timing: Timing,
    name: string,
  ): BoolVar {
    return game.boolSumEquals(
      players.map((player) => Chambermaid.wakesDueToAbility(game, player, timing, name)),
      count,
      `${name}_chambermaid_count_is_${count}`,
    );
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    if (this.checks.length === 0) {
      super.apply(game, options);
      return;
    }
    this.applyRoleClaim(game, Chambermaid, options);
    this.checks.forEach((check, index) => {
      const timing = this.claimTiming(check.timing ?? explicitTiming(options), index);
      this.applyInfoClaimBuilders(
        game,
        Chambermaid,
        [
          {
            learned: Chambermaid.learnsWakeCount(
              game,
              [check.left, check.right],
              check.count,
              timing,
              claimName(this.name, Chambermaid, `check_${index + 1}`),
            ),
            timing,
          },
        ],
        options,
      );
    });
    this.applyInfoClaimBuilders(game, Chambermaid, this.infoClaims, options);
  }
}

export class Clockmaker extends TownsfolkRole {
  static readonly roleName = "Clockmaker";
  static readonly wake = Wakes.firstNight;
  readonly distance?: number;
  constructor(
    options: RoleBaseOptions & {
      readonly distance?: number;
    },
  ) {
    super(options);
    this.distance = options.distance;
  }
  static learnsDemonNextToMinion(game: BOTCModel, name: string): BoolVar {
    return Clockmaker.learnsDemonMinionDistance(game, 1, name);
  }
  static learnsDemonMinionDistance(game: BOTCModel, distance: number, name: string): BoolVar {
    return game.anyOf(
      game.players.map((demon, demonIndex) => {
        const minionsAtDistance = game.players.flatMap((minion, minionIndex) =>
          Clockmaker.seatingDistance(game.players.length, demonIndex, minionIndex) === distance
            ? [game.isMinion(minion)]
            : [],
        );
        const closerSeatsAreNotMinions = game.players.flatMap((minion, minionIndex) =>
          Clockmaker.seatingDistance(game.players.length, demonIndex, minionIndex) < distance
            ? [game.isMinion(minion).not()]
            : [],
        );
        return game.allOf(
          [
            game.isDemon(demon),
            game.anyOf(minionsAtDistance, `${demon}_minion_${distance}_steps_away`),
            ...closerSeatsAreNotMinions,
          ],
          `${demon}_nearest_minion_${distance}_steps_away`,
        );
      }),
      name,
    );
  }
  private static seatingDistance(playerCount: number, leftIndex: number, rightIndex: number): number {
    const clockwise = (rightIndex - leftIndex + playerCount) % playerCount;
    return Math.min(clockwise, playerCount - clockwise);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.distance !== undefined)
      return Clockmaker.learnsDemonMinionDistance(
        game,
        this.distance,
        claimName(this.name, Clockmaker, `demon_${this.distance}_from_minion`),
      );
    return undefined;
  }
}

export class Courtier extends TownsfolkRole {
  static readonly roleName = "Courtier";
  static readonly wake = Wakes.untilAbilityUsed("Courtier", Wakes.everyNight);
  readonly role?: RoleRef;
  readonly drunkTimings: readonly Timing[];

  constructor(
    options: RoleBaseOptions & {
      readonly role?: RoleRef;
      readonly drunkTimings?: readonly Timing[];
    },
  ) {
    super(options);
    this.role = options.role;
    this.drunkTimings = options.drunkTimings ?? [];
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Courtier, options);
    if (this.role !== undefined && this.drunkTimings.length > 0) {
      const timing = this.claimTiming(explicitTiming(options));
      game.registerAbilityUse(this.name, Courtier, timing, game.hasAbilityAt(this.name, Courtier, timing));
      const activeHealthy = game.allOf(
        [game.hasAbilityAt(this.name, Courtier, timing), game.soberAndHealthy(this.name, timing)],
        claimName(this.name, Courtier, "choice_active"),
      );
      game.addRoleDrunking(this.role, this.drunkTimings, { activeIf: activeHealthy });
    }
    this.applyInfoClaimBuilders(game, Courtier, this.infoClaims, options);
  }
}

export class Dreamer extends TownsfolkRole {
  static readonly roleName = "Dreamer";
  static readonly wake = Wakes.everyNight;
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
      roles.map((role) => game.registersAsRole(player, role, name)),
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

export class Empath extends TownsfolkRole {
  static readonly roleName = "Empath";
  static readonly wake = Wakes.everyNight;
  readonly count?: number;
  readonly neighbors?: readonly [string, string];
  readonly neighborOptions?: readonly EmpathNeighborOption[];
  constructor(
    options: RoleBaseOptions & {
      readonly count?: number;
      readonly neighbors?: readonly [string, string];
      readonly neighborOptions?: readonly EmpathNeighborOption[];
    },
  ) {
    super(options);
    this.count = options.count;
    this.neighbors = options.neighbors;
    this.neighborOptions = options.neighborOptions;
  }
  static learnsCount(
    game: BOTCModel,
    player: string,
    count: number,
    name: string,
    neighbors?: readonly [string, string],
  ): BoolVar {
    const [left, right] = neighbors ?? game.neighbors(player);
    return game.boolSumEquals(
      [game.registersAsEvil(left, name), game.registersAsEvil(right, name)],
      count,
      `${name}_empath_count_is_${count}`,
    );
  }
  static learnsConditionalCount(
    game: BOTCModel,
    player: string,
    count: number,
    name: string,
    neighborOptions: readonly EmpathNeighborOption[],
  ): BoolVar {
    return game.anyOf(
      neighborOptions.map((option, index) =>
        game.allOf(
          [option.activeIf, Empath.learnsCount(game, player, count, `${name}_option_${index + 1}`, option.neighbors)],
          `${name}_option_${index + 1}_active`,
        ),
      ),
      `${name}_conditional`,
    );
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.count === undefined) return undefined;
    const name = claimName(this.name, Empath, "count");
    if (this.neighborOptions !== undefined && this.neighbors === undefined) {
      return Empath.learnsConditionalCount(game, this.name, this.count, name, this.neighborOptions);
    }
    return Empath.learnsCount(game, this.name, this.count, name, this.neighbors);
  }
}

export interface EmpathNeighborOption {
  readonly neighbors: readonly [string, string];
  readonly activeIf: BoolLike;
}

export interface FlowergirlVote {
  readonly timing: Timing;
  readonly voters: readonly string[];
  readonly demonVoted: boolean;
}

export class Flowergirl extends TownsfolkRole {
  static readonly roleName = "Flowergirl";
  static readonly wake = Wakes.everyNightExceptFirst;
  readonly votes: readonly FlowergirlVote[];

  constructor(
    options: RoleBaseOptions & {
      readonly votes?: readonly FlowergirlVote[];
    },
  ) {
    super(options);
    this.votes = options.votes ?? [];
  }

  static learnsDemonVoted(
    game: BOTCModel,
    voters: readonly string[],
    demonVoted: boolean,
    timing: Timing,
    name: string,
  ): BoolVar {
    const voteTiming = Flowergirl.voteTiming(timing);
    const anyDemonVoted = game.anyOf(
      voters.map((player) =>
        game.registersAsCharacterTypeAt(player, CharacterType.Demon, voteTiming, `${name}_${player}`),
      ),
      `${name}_any_demon_voted`,
    );
    return demonVoted ? anyDemonVoted : game.not(anyDemonVoted, `${name}_no_demon_voted`);
  }

  private static voteTiming(timing: Timing): Timing {
    const match = /^night_(\d+)$/.exec(timing);
    if (match === null) return timing;
    return `day_${Math.max(1, Number(match[1]) - 1)}` as Timing;
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    if (this.votes.length === 0) {
      super.apply(game, options);
      return;
    }
    this.applyRoleClaim(game, Flowergirl, options);
    this.votes.forEach((vote, index) => {
      this.applyInfoClaimBuilders(
        game,
        Flowergirl,
        [
          {
            learned: Flowergirl.learnsDemonVoted(
              game,
              vote.voters,
              vote.demonVoted,
              vote.timing,
              claimName(this.name, Flowergirl, `vote_${index + 1}`),
            ),
            timing: vote.timing,
          },
        ],
        options,
      );
    });
    this.applyInfoClaimBuilders(game, Flowergirl, this.infoClaims, options);
  }
}

export class TeaLady extends TownsfolkRole {
  static readonly roleName = "Tea Lady";
  static readonly wake = Wakes.never;
}

export interface FortuneTellerCheck {
  readonly left: string;
  readonly right: string;
  readonly yes: boolean;
  readonly name?: string;
  readonly timing?: Timing;
}

export class FortuneTeller extends TownsfolkRole {
  static readonly roleName = "Fortune Teller";
  static readonly wake = Wakes.everyNight;
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
      readonly timing: Timing;
      readonly redHerrings?: ReturnType<BOTCModel["addFortuneTellerRedHerring"]>;
    },
  ): BoolVar {
    const isDemon = (player: string, name: string) =>
      game.registersAsCharacterTypeAt(player, CharacterType.Demon, options.timing, name);
    if (options.redHerrings !== undefined) {
      return options.yes
        ? game.fortuneTellerYes(options.redHerrings, [left, right], options.name, isDemon)
        : game.fortuneTellerNo(options.redHerrings, [left, right], options.name, isDemon);
    }

    const either = game.anyOf(
      [isDemon(left, `${options.name}_${left}`), isDemon(right, `${options.name}_${right}`)],
      `${options.name}_${left}_${right}_either_demon`,
    );
    return options.yes ? either : game.not(either, `${options.name}_${left}_${right}_neither_demon`);
  }
  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    if (this.checks.length === 0) {
      super.apply(game, options);
      return;
    }
    this.applyRoleClaim(game, FortuneTeller, options);
    const redHerrings = game.addFortuneTellerRedHerring(this.name);
    this.checks.forEach((check, index) => {
      const name = check.name ?? claimName(this.name, FortuneTeller, `check_${index + 1}`);
      const learned = FortuneTeller.learnsCheck(game, check.left, check.right, {
        yes: check.yes,
        name,
        timing: check.timing ?? night(index + 1),
        redHerrings,
      });
      this.applyInfoClaimBuilders(
        game,
        FortuneTeller,
        [{ learned, timing: check.timing ?? night(index + 1) }],
        options,
      );
    });
    this.applyInfoClaimBuilders(game, FortuneTeller, this.infoClaims, options);
  }
}

export class Investigator extends TownsfolkRole {
  static readonly roleName = "Investigator";
  static readonly wake = Wakes.firstNight;
  readonly among: readonly string[];
  readonly role?: RoleRef;
  readonly minionRole?: RoleRef;
  constructor(
    options: RoleBaseOptions & {
      readonly among?: readonly string[];
      readonly role?: RoleRef;
      readonly minionRole?: RoleRef;
    },
  ) {
    super(options);
    this.among = options.among ?? [];
    this.role = options.role;
    this.minionRole = options.minionRole;
  }
  static learnsRoleAmong(game: BOTCModel, players: readonly string[], role: RoleRef, name: string): BoolVar {
    return learnsRoleAmong(game, players, role, name);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    const role = this.role ?? this.minionRole;
    return role === undefined
      ? undefined
      : Investigator.learnsRoleAmong(game, this.among, role, claimName(this.name, Investigator, "role_among"));
  }
}

export class Juggler extends TownsfolkRole {
  static readonly roleName = "Juggler";
  static readonly wake = Wakes.secondNight;
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
      items.map(([player, role]) => game.registersAsRole(player, role, name)),
      count,
      name,
    );
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    const round = Number((this.timing ?? night(2)).split("_")[1]);
    return this.correctCount === undefined
      ? undefined
      : game.withTiming(day(Math.max(1, round - 1)), () =>
          Juggler.learnsCorrectCount(
            game,
            this.guesses,
            this.correctCount!,
            claimName(this.name, Juggler, "correct_count"),
          ),
        );
  }
}

export class Shugenja extends TownsfolkRole {
  static readonly roleName = "Shugenja";
  static readonly wake = Wakes.firstNight;
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

export class Knight extends TownsfolkRole {
  static readonly roleName = "Knight";
  static readonly wake = Wakes.firstNight;
  static readonly maxNoDemonAmong = 2;
  readonly noDemonAmong: readonly string[];
  constructor(
    options: RoleBaseOptions & {
      readonly noDemonAmong?: readonly string[];
    },
  ) {
    super(options);
    const noDemonAmong = options.noDemonAmong ?? [];
    Knight.assertNoDemonAmongLimit(noDemonAmong);
    this.noDemonAmong = noDemonAmong;
  }
  static learnsNoDemonAmong(game: BOTCModel, players: readonly string[], name: string): BoolVar {
    Knight.assertNoDemonAmongLimit(players);
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
  private static assertNoDemonAmongLimit(players: readonly string[]): void {
    if (players.length > Knight.maxNoDemonAmong) {
      throw new Error(`Knight claims can include at most ${Knight.maxNoDemonAmong} non-Demon players.`);
    }
  }
}

export interface VillageIdiotCheck {
  readonly player: string;
  readonly good: boolean;
  readonly timing?: Timing;
  readonly name?: string;
}

export class VillageIdiot extends TownsfolkRole {
  static readonly roleName = "Village Idiot";
  static readonly wake = Wakes.everyNight;
  static readonly maxCopies = 3;
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
  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, VillageIdiot, options);
    this.applyInfoClaimBuilders(
      game,
      VillageIdiot,
      [
        ...this.checks.map((check, index): InfoClaim => {
          const name = check.name ?? claimName(this.name, VillageIdiot, `check_${index + 1}`);
          return {
            timing: check.timing ?? this.claimTiming(undefined, index),
            learned: (model: BOTCModel) => VillageIdiot.learnsCheck(model, check.player, check.good, name),
          };
        }),
        ...this.infoClaims,
      ],
      options,
    );
  }
}

export class Virgin extends TownsfolkRole {
  static readonly roleName = "Virgin";
  static readonly wake = Wakes.never;
  readonly nominator?: string;
  readonly executed?: boolean;

  constructor(
    options: RoleBaseOptions & {
      readonly nominator?: string;
      readonly executed?: boolean;
    },
  ) {
    super(options);
    this.nominator = options.nominator;
    this.executed = options.executed;
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Virgin, options);
    if (this.nominator === undefined || this.executed === undefined) {
      this.applyInfoClaimBuilders(game, Virgin, this.infoClaims, options);
      return;
    }

    const timing = this.claimTiming(explicitTiming(options));
    const activeHealthy = game.allOf(
      [game.hasAbilityAt(this.name, Virgin, timing), game.soberAndHealthy(this.name, healthTimingForAbility(timing))],
      claimName(this.name, Virgin, "nomination_active"),
    );
    if (this.executed) game.addTruth(activeHealthy);
    game.addImplication(
      activeHealthy,
      this.executed
        ? game.registersAsCharacterType(
            this.nominator,
            CharacterType.Townsfolk,
            claimName(this.name, Virgin, "nominator_townsfolk"),
          )
        : game.not(
            game.registersAsCharacterType(
              this.nominator,
              CharacterType.Townsfolk,
              claimName(this.name, Virgin, "nominator_townsfolk"),
            ),
            claimName(this.name, Virgin, "nominator_not_townsfolk"),
          ),
    );
    this.applyInfoClaimBuilders(game, Virgin, this.infoClaims, options);
  }
}

export class Librarian extends TownsfolkRole {
  static readonly roleName = "Librarian";
  static readonly wake = Wakes.firstNight;
  readonly among: readonly string[];
  readonly role?: RoleRef;
  constructor(
    options: RoleBaseOptions & {
      readonly among?: readonly string[];
      readonly role?: RoleRef;
    },
  ) {
    super(options);
    this.among = options.among ?? [];
    this.role = options.role;
  }
  static learnsRoleAmong(game: BOTCModel, players: readonly string[], role: RoleRef, name: string): BoolVar {
    return learnsRoleAmong(game, players, role, name);
  }
  static learnsCharacterTypeCount(
    game: BOTCModel,
    players: readonly string[],
    characterType: CharacterType,
    count: number,
    name: string,
  ): BoolVar {
    return learnsCharacterTypeCount(game, players, characterType, count, name);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.role !== undefined)
      return Librarian.learnsRoleAmong(game, this.among, this.role, claimName(this.name, Librarian, "role_among"));
    return Librarian.learnsCharacterTypeCount(
      game,
      game.players,
      CharacterType.Outsider,
      0,
      claimName(this.name, Librarian, "outsider_count"),
    );
  }
}

export class Legionary extends TownsfolkRole {
  static readonly roleName = "Legionary";
  static readonly wake = Wakes.everyNight;
  static readonly maxCopies = 3;
  readonly counts: readonly LegionaryCount[];

  constructor(
    options: RoleBaseOptions & {
      readonly counts?: readonly LegionaryCount[];
    },
  ) {
    super(options);
    this.counts = options.counts ?? [];
  }

  static learnsCount(
    game: BOTCModel,
    player: string,
    count: number,
    alivePlayers: readonly string[],
    name: string,
  ): BoolVar {
    const playerIndex = alivePlayers.indexOf(player);
    if (playerIndex === -1) return game.constantBool(false, `${name}_dead_player`);

    const nextLegionaryOptions: BoolVar[] = [];
    for (let offset = 1; offset < alivePlayers.length; offset += 1) {
      const candidate = alivePlayers[(playerIndex + offset) % alivePlayers.length] as string;
      const between = Array.from(
        { length: offset - 1 },
        (_ignored, betweenOffset) => alivePlayers[(playerIndex + betweenOffset + 1) % alivePlayers.length] as string,
      );
      const candidateIsNext = game.allOf(
        [
          game.actualIs(candidate, Legionary),
          ...between.map((betweenPlayer) => game.actualIs(betweenPlayer, Legionary).not()),
        ],
        `${name}_${candidate}_next_legionary`,
      );
      const countMatches = game.boolSumEquals(
        between.map((betweenPlayer) => game.isEvil(betweenPlayer)),
        count,
        `${name}_${candidate}_evil_count_${count}`,
      );
      nextLegionaryOptions.push(
        game.allOf([candidateIsNext, countMatches], `${name}_${candidate}_next_legionary_count_matches`),
      );
    }
    return game.anyOf(nextLegionaryOptions, name);
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Legionary, options);
    this.applyInfoClaimBuilders(
      game,
      Legionary,
      [
        ...this.counts.map((entry, index): InfoClaim => {
          const timing = this.claimTiming(entry.timing, index);
          return {
            timing,
            learned: (model: BOTCModel) =>
              Legionary.learnsCount(
                model,
                this.name,
                entry.count,
                entry.alivePlayers ?? model.players,
                claimName(this.name, Legionary, `count_${index + 1}`),
              ),
          };
        }),
        ...this.infoClaims,
      ],
      options,
    );
  }
}

export interface LegionaryCount {
  readonly count: number;
  readonly timing?: Timing;
  readonly alivePlayers?: readonly string[];
}

export class Mayor extends TownsfolkRole {
  static readonly roleName = "Mayor";
  static readonly wake = Wakes.never;
}

export class Monk extends TownsfolkRole {
  static readonly roleName = "Monk";
  static readonly wake = Wakes.everyNightExceptFirst;
}

export class Noble extends TownsfolkRole {
  static readonly roleName = "Noble";
  static readonly wake = Wakes.firstNight;
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
    return predicates.exactlyNRegisteredEvil(game, players, count);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    if (this.oneEvilAmong.length > 0) return Noble.learnsEvilCount(game, this.oneEvilAmong, 1);
    return this.evilCount === undefined ? undefined : Noble.learnsEvilCount(game, this.among, this.evilCount);
  }
}

export class Oracle extends TownsfolkRole {
  static readonly roleName = "Oracle";
  static readonly wake = Wakes.everyNightExceptFirst;
  readonly count?: number;
  readonly deadPlayers: readonly string[];
  readonly deadPlayerOptions?: readonly OracleDeadPlayerOption[];

  constructor(
    options: RoleBaseOptions & {
      readonly count?: number;
      readonly deadPlayers?: readonly string[];
      readonly deadPlayerOptions?: readonly OracleDeadPlayerOption[];
    },
  ) {
    super(options);
    this.count = options.count;
    this.deadPlayers = options.deadPlayers ?? [];
    this.deadPlayerOptions = options.deadPlayerOptions;
  }

  static learnsDeadEvilCount(game: BOTCModel, deadPlayers: readonly string[], count: number): BoolVar {
    return game.registeredEvilCount(deadPlayers, count, `oracle_dead_evil_count_is_${count}`);
  }

  static actualDeadEvilCount(game: BOTCModel, deadPlayers: readonly string[], count: number, name: string): BoolVar {
    return game.boolSumEquals(
      deadPlayers.map((player) => game.isEvil(player)),
      count,
      name,
    );
  }

  static learnsConditionalDeadEvilCount(
    game: BOTCModel,
    count: number,
    name: string,
    deadPlayerOptions: readonly OracleDeadPlayerOption[],
  ): BoolVar {
    return game.anyOf(
      deadPlayerOptions.map((option, index) =>
        game.allOf(
          [
            option.activeIf,
            game.registeredEvilCount(option.deadPlayers, count, `${name}_option_${index + 1}_dead_evil_count`),
          ],
          `${name}_option_${index + 1}_active`,
        ),
      ),
      `${name}_conditional`,
    );
  }

  static actualConditionalDeadEvilCount(
    game: BOTCModel,
    count: number,
    name: string,
    deadPlayerOptions: readonly OracleDeadPlayerOption[],
  ): BoolVar {
    return game.anyOf(
      deadPlayerOptions.map((option, index) =>
        game.allOf(
          [
            option.activeIf,
            Oracle.actualDeadEvilCount(
              game,
              option.deadPlayers,
              count,
              `${name}_option_${index + 1}_actual_dead_evil_count`,
            ),
          ],
          `${name}_option_${index + 1}_actual_active`,
        ),
      ),
      `${name}_actual_conditional`,
    );
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Oracle, options);
    if (this.count === undefined) {
      this.applyInfoClaimBuilders(game, Oracle, this.infoClaims, options);
      return;
    }
    const name = claimName(this.name, Oracle, "count");
    const learned =
      this.deadPlayerOptions === undefined
        ? Oracle.learnsDeadEvilCount(game, this.deadPlayers, this.count)
        : Oracle.learnsConditionalDeadEvilCount(game, this.count, name, this.deadPlayerOptions);
    const malfunctionLearned =
      this.deadPlayerOptions === undefined
        ? Oracle.actualDeadEvilCount(game, this.deadPlayers, this.count, `${name}_actual`)
        : Oracle.actualConditionalDeadEvilCount(game, this.count, name, this.deadPlayerOptions);
    this.applyInfoClaimBuilders(game, Oracle, [{ learned, malfunctionLearned }, ...this.infoClaims], options);
  }
}

export interface OracleDeadPlayerOption {
  readonly deadPlayers: readonly string[];
  readonly activeIf: BoolLike;
}

export class Nightwatchman extends TownsfolkRole {
  static readonly roleName = "Nightwatchman";
  static readonly wake = Wakes.untilAbilityUsed("Nightwatchman", Wakes.everyNight);
  readonly chosen?: string;
  readonly learned?: boolean;
  readonly confirmedByChosen: boolean;

  constructor(
    options: RoleBaseOptions & {
      readonly chosen?: string;
      readonly learned?: boolean;
      readonly confirmedByChosen?: boolean;
    },
  ) {
    super(options);
    this.chosen = options.chosen;
    this.learned = options.learned;
    this.confirmedByChosen = options.confirmedByChosen ?? false;
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Nightwatchman, options);
    if (this.chosen === undefined || this.learned === undefined) {
      this.applyInfoClaimBuilders(game, Nightwatchman, this.infoClaims, options);
      return;
    }

    const timing = this.claimTiming(explicitTiming(options));
    game.registerAbilityUse(this.name, Nightwatchman, timing, game.hasAbilityAt(this.name, Nightwatchman, timing));
    const activeHealthy = game.allOf(
      [game.hasAbilityAt(this.name, Nightwatchman, timing), game.soberAndHealthy(this.name, timing)],
      claimName(this.name, Nightwatchman, "chosen_player_learns"),
    );
    game.addImplication(
      activeHealthy,
      game.constantBool(this.learned, claimName(this.chosen, Nightwatchman, "learned")),
    );
    if (this.learned && this.confirmedByChosen) {
      game.addImplication(game.isGood(this.chosen), activeHealthy);
    }
    this.applyInfoClaimBuilders(game, Nightwatchman, this.infoClaims, options);
  }
}

export class Savant extends TownsfolkRole {
  static readonly roleName = "Savant";
  static readonly wake = Wakes.never;
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
          this.statements.map((statement, index) => buildStatement(game, this.name, index + 1, statement, this.timing)),
          claimName(this.name, Savant, "all_statements"),
        );
  }
}

export class Seamstress extends TownsfolkRole {
  static readonly roleName = "Seamstress";
  static readonly wake = Wakes.untilAbilityUsed("Seamstress", Wakes.everyNight);
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

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Seamstress, options);
    if (this.aligned === undefined) {
      this.applyInfoClaimBuilders(game, Seamstress, this.infoClaims, options);
      return;
    }
    const timing = this.claimTiming(explicitTiming(options));
    const [left, right] = this.among;
    if (left === undefined || right === undefined) throw new Error("Seamstress needs two players.");
    const learned = this.aligned
      ? predicates.sameAlignmentAt(game, left, right, timing)
      : predicates.differentAlignmentsAt(game, left, right, timing);
    this.applyInfoClaimBuilders(game, Seamstress, [{ learned, timing }, ...this.infoClaims], options);
    game.registerAbilityUse(this.name, Seamstress, timing, game.hasAbilityAt(this.name, Seamstress, timing));
  }
}

export class Steward extends TownsfolkRole {
  static readonly roleName = "Steward";
  static readonly wake = Wakes.firstNight;
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

export class Undertaker extends TownsfolkRole {
  static readonly roleName = "Undertaker";
  static readonly wake = Wakes.everyNightExceptFirst;
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
    return game.registersAsRole(player, role, claimName(player, Undertaker, `registers_as_${roleName(role)}`));
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.player === undefined || this.role === undefined
      ? undefined
      : Undertaker.learnsRole(game, this.player, this.role);
  }
}

export class Washerwoman extends TownsfolkRole {
  static readonly roleName = "Washerwoman";
  static readonly wake = Wakes.firstNight;
  readonly among: readonly string[];
  readonly role?: RoleRef;
  constructor(
    options: RoleBaseOptions & {
      readonly among?: readonly string[];
      readonly role?: RoleRef;
    },
  ) {
    super(options);
    this.among = options.among ?? [];
    this.role = options.role;
  }
  static learnsRoleAmong(game: BOTCModel, players: readonly string[], role: RoleRef, name: string): BoolVar {
    return learnsRoleAmong(game, players, role, name);
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.role === undefined
      ? undefined
      : Washerwoman.learnsRoleAmong(game, this.among, this.role, claimName(this.name, Washerwoman, "role_among"));
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
