import {
  Alignment,
  CharacterType,
  type RoleClass,
  type RoleRef,
  roleAlignment,
  roleCharacterType,
  roleName,
} from "./core";
import { night, type BoolLike, type BoolVar, type BOTCModel, type Timing } from "./model";
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
  readonly timing?: Timing;
  readonly vortoxAffected?: boolean;
}

export interface RoleBaseOptions {
  readonly name: string;
  readonly timing?: Timing;
  readonly extraPossibleActualRoles?: readonly RoleRef[];
  readonly infoClaims?: readonly InfoClaimBuilder[];
}

export interface AppliedInfoClaim {
  readonly player: string;
  readonly role: RoleRef;
  readonly learned: BoolLike;
  readonly timing: Timing;
  readonly vortoxAffected?: boolean;
  readonly context?: unknown;
}

export type ApplyInfoClaim = (game: BOTCModel, claim: AppliedInfoClaim) => void;

export interface ApplyClaimsOptions extends TimedOptions {
  readonly drunkRole?: RoleRef;
  readonly evilRoles?: readonly RoleRef[];
  readonly extraPossibleActualRoles?: readonly RoleRef[];
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

export abstract class Role {
  static readonly roleName: string;
  static readonly alignment: Alignment;
  static readonly characterType: CharacterType;

  readonly roleName: string;
  readonly alignment: Alignment;
  readonly characterType: CharacterType;
  readonly maxCopies?: number;
  readonly name: string;
  readonly timing?: Timing;
  readonly extraPossibleActualRoles: readonly RoleRef[];
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
    this.extraPossibleActualRoles =
      typeof nameOrOptions === "string" ? [] : (nameOrOptions.extraPossibleActualRoles ?? []);
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
      { player: this.name, apparentRole: role },
      {
        drunkRole,
        evilRoles: options.evilRoles,
        extraPossibleActualRoles: [...this.extraPossibleActualRoles, ...(options.extraPossibleActualRoles ?? [])],
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
        learned: resolveInfoClaim(game, options.context, resolvedClaim),
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
  readonly chosen?: string;
  readonly lost?: boolean;

  constructor(
    options: RoleBaseOptions & {
      readonly chosen?: string;
      readonly lost?: boolean;
    },
  ) {
    super(options);
    this.chosen = options.chosen;
    this.lost = options.lost;
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Klutz, options);
    if (this.chosen === undefined || this.lost === undefined) {
      this.applyInfoClaimBuilders(game, Klutz, this.infoClaims, options);
      return;
    }

    const timing = this.claimTiming(explicitTiming(options));
    const activeHealthy = game.allOf(
      [game.hasRoleAt(this.name, Klutz, timing), game.soberAndHealthy(this.name, timing)],
      claimName(this.name, Klutz, "choice_active"),
    );
    game.addImplication(activeHealthy, this.lost ? game.isEvil(this.chosen) : game.isGood(this.chosen));
    this.applyInfoClaimBuilders(game, Klutz, this.infoClaims, options);
  }
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
export class Damsel extends Role {
  static readonly roleName = "Damsel";
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
  readonly target?: string;
  readonly killed?: boolean;
  readonly gameContinued: boolean;

  constructor(
    options: RoleBaseOptions & {
      readonly target?: string;
      readonly killed?: boolean;
      readonly gameContinued?: boolean;
    },
  ) {
    super(options);
    this.target = options.target;
    this.killed = options.killed;
    this.gameContinued = options.gameContinued ?? false;
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

  static scarletWomanCanCatch(game: BOTCModel, name: string): BoolVar {
    return game.characters.has("Scarlet Woman")
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
      [game.hasRoleAt(this.name, Slayer, timing), game.soberAndHealthy(this.name, healthTimingForAbility(timing))],
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
        Slayer.scarletWomanCanCatch(game, claimName(this.name, Slayer, "shot_continued")),
      );
    }
    this.applyInfoClaimBuilders(game, Slayer, this.infoClaims, options);
  }
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
  readonly role?: RoleRef;

  constructor(options: RoleBaseOptions & { readonly role?: RoleRef }) {
    super(options);
    this.role = options.role;
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Philosopher, options);
    if (this.role !== undefined) {
      const timing = this.claimTiming(explicitTiming(options));
      const activeHealthy = game.allOf(
        [game.actualIs(this.name, Philosopher), game.soberAndHealthy(this.name, timing)],
        claimName(this.name, Philosopher, "choice_active"),
      );
      game.addRoleAt(this.name, this.role, timing, activeHealthy);
    }
    this.applyInfoClaimBuilders(game, Philosopher, this.infoClaims, options);
  }
}

export class Acrobat extends Role {
  static readonly roleName = "Acrobat";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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
    return game.anyOf(
      [game.isDrunkAt(player, timing), game.isPoisonedAt(player, timing), game.noDashiiPoisonedAt(player, timing)],
      name,
    );
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Acrobat, options);
    this.choices.forEach((choice, index) => {
      const timing = this.claimTiming(choice.timing, index);
      const activeHealthy = game.allOf(
        [game.hasRoleAt(this.name, Acrobat, timing), game.soberAndHealthy(this.name, timing)],
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

export interface AcrobatChoice {
  readonly player: string;
  readonly timing?: Timing;
  readonly died: boolean;
}

export class Gambler extends Role {
  static readonly roleName = "Gambler";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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
    this.guesses.forEach((guess, index) => {
      if (guess.survived === undefined) return;
      const timing = this.claimTiming(guess.timing, index);
      const activeHealthy = game.allOf(
        [game.hasRoleAt(this.name, Gambler, timing), game.soberAndHealthy(this.name, timing)],
        claimName(this.name, Gambler, `guess_${index + 1}_active`),
      );
      const correct = game.registersAsRole(
        guess.player,
        guess.role,
        claimName(this.name, Gambler, `guess_${index + 1}_correct`),
      );
      if (!guess.survived) game.addTruth(activeHealthy);
      game.addImplication(
        activeHealthy,
        guess.survived ? correct : game.not(correct, claimName(this.name, Gambler, `guess_${index + 1}_wrong`)),
      );
    });
    this.applyInfoClaimBuilders(game, Gambler, this.infoClaims, options);
  }
}

export interface GamblerGuess {
  readonly player: string;
  readonly role: RoleRef;
  readonly timing?: Timing;
  readonly survived?: boolean;
}

export interface GossipStatement {
  readonly timing?: Timing;
  readonly statement: ClaimPredicate;
}

export class Gossip extends Role {
  static readonly roleName = "Gossip";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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

export class Mathematician extends Role {
  static readonly roleName = "Mathematician";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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
          ),
      })),
      options,
    );
    this.applyInfoClaimBuilders(game, Mathematician, this.infoClaims, options);
  }
}

export class Ravenkeeper extends Role {
  static readonly roleName = "Ravenkeeper";
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

  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.player === undefined || this.role === undefined
      ? undefined
      : game.registersAsRole(this.player, this.role, claimName(this.name, Ravenkeeper, "role"));
  }
}

export class Sage extends Role {
  static readonly roleName = "Sage";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly demonAmong: readonly string[];
  constructor(options: RoleBaseOptions & { readonly demonAmong?: readonly string[] }) {
    super(options);
    this.demonAmong = options.demonAmong ?? [];
  }
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.demonAmong.length === 0
      ? undefined
      : game.anyOf(
          this.demonAmong.map((player) => game.isDemon(player)),
          claimName(this.name, Sage, "demon_among"),
        );
  }
}

export class SnakeCharmer extends Role {
  static readonly roleName = "Snake Charmer";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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

const FIRST_NIGHT_WAKE_ROLES = new Set([
  "Chef",
  "Clockmaker",
  "Investigator",
  "Librarian",
  "Noble",
  "Shugenja",
  "Steward",
  "Washerwoman",
]);
const EVERY_NIGHT_WAKE_ROLES = new Set([
  "Balloonist",
  "Chambermaid",
  "Dreamer",
  "Empath",
  "Fortune Teller",
  "Mathematician",
  "Pukka",
  "Snake Charmer",
  "Village Idiot",
]);
const SECOND_NIGHT_PLUS_WAKE_ROLES = new Set(["Oracle", "Undertaker"]);
const SECOND_NIGHT_WAKE_ROLES = new Set(["Juggler"]);

function nightNumber(timing: Timing): number | undefined {
  const match = /^night_(\d+)$/.exec(timing);
  return match === null ? undefined : Number(match[1]);
}

export class Chambermaid extends Role {
  static readonly roleName = "Chambermaid";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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
    const nightIndex = nightNumber(timing);
    if (nightIndex === undefined) return game.constantBool(false, `${name}_not_a_night`);
    const wakingRoles = [...game.characters.keys()].filter((role) => {
      if (EVERY_NIGHT_WAKE_ROLES.has(role)) return true;
      if (FIRST_NIGHT_WAKE_ROLES.has(role)) return nightIndex === 1;
      if (SECOND_NIGHT_PLUS_WAKE_ROLES.has(role)) return nightIndex >= 2;
      if (SECOND_NIGHT_WAKE_ROLES.has(role)) return nightIndex === 2;
      return false;
    });
    return game.anyOf(
      wakingRoles.map((role) => game.hasRoleAt(player, role, timing)),
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

export class Clockmaker extends Role {
  static readonly roleName = "Clockmaker";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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

export class Courtier extends Role {
  static readonly roleName = "Courtier";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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
      const activeHealthy = game.allOf(
        [game.hasRoleAt(this.name, Courtier, timing), game.soberAndHealthy(this.name, timing)],
        claimName(this.name, Courtier, "choice_active"),
      );
      game.addRoleDrunking(this.role, this.drunkTimings, { activeIf: activeHealthy });
    }
    this.applyInfoClaimBuilders(game, Courtier, this.infoClaims, options);
  }
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
  readonly neighbors?: readonly [string, string];
  constructor(
    options: RoleBaseOptions & {
      readonly count?: number;
      readonly player?: string;
      readonly neighbors?: readonly [string, string];
    },
  ) {
    super(options);
    this.count = options.count;
    this.player = options.player;
    this.neighbors = options.neighbors;
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
  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.count === undefined
      ? undefined
      : Empath.learnsCount(
          game,
          this.player ?? this.name,
          this.count,
          claimName(this.name, Empath, "count"),
          this.neighbors,
        );
  }
}

export interface FortuneTellerCheck {
  readonly left: string;
  readonly right: string;
  readonly yes: boolean;
  readonly name?: string;
  readonly demonRole?: RoleRef;
  readonly timing?: Timing;
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
      readonly timing: Timing;
      readonly demonRole?: RoleRef;
      readonly redHerrings?: ReturnType<BOTCModel["addFortuneTellerRedHerring"]>;
    },
  ): BoolVar {
    const isDemon =
      options.demonRole === undefined
        ? (player: string, name: string) =>
            game.registersAsCharacterTypeAt(player, CharacterType.Demon, options.timing, name)
        : (player: string, name: string) =>
            game.registersAsRoleAt(player, options.demonRole as RoleRef, options.timing, name);
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
        demonRole: check.demonRole,
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

export class Investigator extends Role {
  static readonly roleName = "Investigator";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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

export class VillageIdiot extends Role {
  static readonly roleName = "Village Idiot";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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

export class Virgin extends Role {
  static readonly roleName = "Virgin";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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
      [game.hasRoleAt(this.name, Virgin, timing), game.soberAndHealthy(this.name, healthTimingForAbility(timing))],
      claimName(this.name, Virgin, "nomination_active"),
    );
    game.addImplication(
      activeHealthy,
      this.executed
        ? game.isTownsfolk(this.nominator)
        : game.not(game.isTownsfolk(this.nominator), claimName(this.name, Virgin, "nominator_not_townsfolk")),
    );
    this.applyInfoClaimBuilders(game, Virgin, this.infoClaims, options);
  }
}

export class Librarian extends Role {
  static readonly roleName = "Librarian";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly among: readonly string[];
  readonly role?: RoleRef;
  readonly outsiderCount?: number;
  constructor(
    options: RoleBaseOptions & {
      readonly among?: readonly string[];
      readonly role?: RoleRef;
      readonly outsiderCount?: number;
    },
  ) {
    super(options);
    this.among = options.among ?? [];
    this.role = options.role;
    this.outsiderCount = options.outsiderCount;
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
    if (this.outsiderCount !== undefined)
      return Librarian.learnsCharacterTypeCount(
        game,
        game.players,
        CharacterType.Outsider,
        this.outsiderCount,
        claimName(this.name, Librarian, "outsider_count"),
      );
    return undefined;
  }
}

export class Legionary extends Role {
  static readonly roleName = "Legionary";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
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
  readonly count?: number;
  readonly deadPlayers: readonly string[];

  constructor(
    options: RoleBaseOptions & {
      readonly count?: number;
      readonly deadPlayers?: readonly string[];
    },
  ) {
    super(options);
    this.count = options.count;
    this.deadPlayers = options.deadPlayers ?? [];
  }

  static learnsDeadEvilCount(game: BOTCModel, deadPlayers: readonly string[], count: number): BoolVar {
    return game.registeredEvilCount(deadPlayers, count, `oracle_dead_evil_count_is_${count}`);
  }

  override learnedInfo(game: BOTCModel): BoolLike | undefined {
    return this.count === undefined || this.deadPlayers.length === 0
      ? undefined
      : Oracle.learnsDeadEvilCount(game, this.deadPlayers, this.count);
  }
}

export class Nightwatchman extends Role {
  static readonly roleName = "Nightwatchman";
  static readonly alignment = Alignment.Good;
  static readonly characterType = CharacterType.Townsfolk;
  readonly chosen?: string;
  readonly learned?: boolean;

  constructor(
    options: RoleBaseOptions & {
      readonly chosen?: string;
      readonly learned?: boolean;
    },
  ) {
    super(options);
    this.chosen = options.chosen;
    this.learned = options.learned;
  }

  override apply(game: BOTCModel, options: ApplyClaimsOptions = {}): void {
    this.applyRoleClaim(game, Nightwatchman, options);
    if (this.chosen === undefined || this.learned === undefined) {
      this.applyInfoClaimBuilders(game, Nightwatchman, this.infoClaims, options);
      return;
    }

    const timing = this.claimTiming(explicitTiming(options));
    const activeHealthy = game.allOf(
      [game.hasRoleAt(this.name, Nightwatchman, timing), game.soberAndHealthy(this.name, timing)],
      claimName(this.name, Nightwatchman, "chosen_player_learns"),
    );
    game.addImplication(
      activeHealthy,
      game.constantBool(this.learned, claimName(this.chosen, Nightwatchman, "learned")),
    );
    this.applyInfoClaimBuilders(game, Nightwatchman, this.infoClaims, options);
  }
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
