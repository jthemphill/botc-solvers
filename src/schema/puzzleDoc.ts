export interface PuzzleDoc {
  readonly version: 1;
  readonly title?: string;
  readonly players: readonly string[];
  readonly script: readonly string[];
  readonly setup?: "standard" | "none";
  readonly uniqueCharacters?: boolean;
  readonly fixedRoles?: readonly FixedRoleConstraint[];
  readonly forbiddenRoles?: readonly ForbiddenRoleConstraint[];
  readonly claims: readonly Claim[];
}

export const KNIGHT_NO_DEMON_AMONG_MAX = 2;

export interface FixedRoleConstraint {
  readonly name: string;
  readonly roles: readonly string[];
}

export interface ForbiddenRoleConstraint {
  readonly name: string;
  readonly roles: readonly string[];
}

export type Claim =
  | InvestigatorClaim
  | LibrarianClaim
  | WasherwomanClaim
  | ChefClaim
  | EmpathClaim
  | FortuneTellerClaim
  | UndertakerClaim
  | NobleClaim
  | StewardClaim
  | KnightClaim
  | SeamstressClaim
  | JugglerClaim
  | DreamerClaim
  | ShugenjaClaim
  | ClockmakerClaim
  | VillageIdiotClaim
  | BalloonistClaim
  | SavantClaim
  | BareClaim;

interface BaseClaim {
  readonly name: string;
  readonly timing?: string;
  readonly info?: readonly CustomInfoStatementDoc[];
}

export interface CustomInfoStatementDoc {
  readonly timing?: string;
  readonly text?: string;
  readonly expression?: string;
  readonly vortoxAffected?: boolean;
}

export interface InvestigatorClaim extends BaseClaim {
  readonly type: "Investigator";
  readonly minionRole?: string;
  readonly role?: string;
  readonly among: readonly string[];
}

export interface LibrarianClaim extends BaseClaim {
  readonly type: "Librarian";
  readonly role?: string;
  readonly outsiderCount?: number;
  readonly among?: readonly string[];
  readonly registers?: boolean;
}

export interface WasherwomanClaim extends BaseClaim {
  readonly type: "Washerwoman";
  readonly role?: string;
  readonly among: readonly string[];
  readonly registers?: boolean;
}

export interface ChefClaim extends BaseClaim {
  readonly type: "Chef";
  readonly count?: number;
  readonly registers?: boolean;
}

export interface EmpathClaim extends BaseClaim {
  readonly type: "Empath";
  readonly count?: number;
  readonly player?: string;
}

export interface FortuneTellerCheckDoc {
  readonly left: string;
  readonly right: string;
  readonly yes: boolean;
  readonly demonRole?: string;
  readonly registers?: boolean;
  readonly timing?: string;
}

export interface FortuneTellerClaim extends BaseClaim {
  readonly type: "FortuneTeller";
  readonly checks: readonly FortuneTellerCheckDoc[];
}

export interface UndertakerClaim extends BaseClaim {
  readonly type: "Undertaker";
  readonly player?: string;
  readonly role?: string;
}

export interface NobleClaim extends BaseClaim {
  readonly type: "Noble";
  readonly oneEvilAmong?: readonly string[];
  readonly among?: readonly string[];
  readonly evilCount?: number;
}

export interface StewardClaim extends BaseClaim {
  readonly type: "Steward";
  readonly goodPlayer?: string;
}

export interface KnightClaim extends BaseClaim {
  readonly type: "Knight";
  readonly noDemonAmong: readonly string[];
}

export interface SeamstressClaim extends BaseClaim {
  readonly type: "Seamstress";
  readonly among: readonly string[];
  readonly aligned?: boolean;
}

export interface JugglerClaim extends BaseClaim {
  readonly type: "Juggler";
  readonly guesses: Readonly<Record<string, string>>;
  readonly correctCount?: number;
}

export interface DreamerClaim extends BaseClaim {
  readonly type: "Dreamer";
  readonly player?: string;
  readonly roles: readonly string[];
}

export interface ShugenjaClaim extends BaseClaim {
  readonly type: "Shugenja";
  readonly evilDirection?: "clockwise" | "anticlockwise";
}

export interface ClockmakerClaim extends BaseClaim {
  readonly type: "Clockmaker";
  readonly demonNextToMinion?: boolean;
}

export interface VillageIdiotCheckDoc {
  readonly player: string;
  readonly good: boolean;
}

export interface VillageIdiotClaim extends BaseClaim {
  readonly type: "VillageIdiot";
  readonly checks: readonly VillageIdiotCheckDoc[];
}

export interface BalloonistClaim extends BaseClaim {
  readonly type: "Balloonist";
  readonly differentCharacterTypePairs: readonly (readonly [string, string])[];
}

export interface SavantStatementDoc {
  readonly options: readonly string[];
}

export interface SavantClaim extends BaseClaim {
  readonly type: "Savant";
  readonly statements: readonly SavantStatementDoc[];
}

export const BARE_CLAIM_TYPES = [
  "Acrobat",
  "Alsaahir",
  "Artist",
  "Atheist",
  "Baron",
  "Butler",
  "Cerenovus",
  "Chambermaid",
  "Courtier",
  "Damsel",
  "Drunk",
  "Evil Twin",
  "Gambler",
  "Goblin",
  "Gossip",
  "Imp",
  "Klutz",
  "Legionary",
  "Leviathan",
  "Lord of Typhon",
  "Lunatic",
  "Marionette",
  "Mathematician",
  "Mayor",
  "Mutant",
  "Nightwatchman",
  "No Dashii",
  "Oracle",
  "Philosopher",
  "Pit-Hag",
  "Po",
  "Poisoner",
  "Pukka",
  "Puzzlemaster",
  "Ravenkeeper",
  "Recluse",
  "Sage",
  "Saint",
  "Scarlet Woman",
  "Slayer",
  "Snake Charmer",
  "Soldier",
  "Spy",
  "Sweetheart",
  "Virgin",
  "Vortox",
  "Witch",
  "Xaan",
] as const;

export type BareClaimType = (typeof BARE_CLAIM_TYPES)[number];

export interface BareClaim extends BaseClaim {
  readonly type: BareClaimType;
}

export const STRUCTURED_CLAIM_TYPES = [
  "Investigator",
  "Librarian",
  "Washerwoman",
  "Chef",
  "Empath",
  "FortuneTeller",
  "Undertaker",
  "Noble",
  "Steward",
  "Knight",
  "Seamstress",
  "Juggler",
  "Dreamer",
  "Shugenja",
  "Clockmaker",
  "VillageIdiot",
  "Balloonist",
  "Savant",
] as const satisfies readonly Claim["type"][];

export const SUPPORTED_CLAIM_TYPES = new Set<Claim["type"]>([...STRUCTURED_CLAIM_TYPES, ...BARE_CLAIM_TYPES]);
