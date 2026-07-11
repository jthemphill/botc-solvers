export interface PuzzleDoc {
  readonly title?: string;
  readonly players: readonly string[];
  readonly script: readonly string[];
  readonly setup?: "standard" | "none" | "atheist";
  readonly uniqueCharacters?: boolean;
  readonly constraints?: readonly PuzzleConstraintDoc[];
  readonly timeline?: readonly TimelineEventDoc[];
  readonly claims: readonly Claim[];
}

export const KNIGHT_NO_DEMON_AMONG_MAX = 2;

export interface PuzzleConstraintDoc {
  readonly expression: string;
}

export type TimelineEventType =
  "nominationDeath" | "witchCurse" | "slayerShot" | "execution" | "survivedExecution" | "nightDeath" | "doomsayerDeath";

export interface TimelineEventDoc {
  readonly timing: string;
  readonly type: TimelineEventType;
  readonly players: readonly string[];
  readonly caller?: string;
  readonly sourceActedBeforeDeath?: boolean;
}

export const TIMELINE_DEATH_EVENT_TYPES = [
  "nominationDeath",
  "witchCurse",
  "slayerShot",
  "execution",
  "nightDeath",
  "doomsayerDeath",
] as const satisfies readonly TimelineEventType[];

export const TIMELINE_EVENT_TYPES = [
  ...TIMELINE_DEATH_EVENT_TYPES,
  "survivedExecution",
] as const satisfies readonly TimelineEventType[];

export function isTimelineDeathEvent(event: TimelineEventDoc): boolean {
  return (TIMELINE_DEATH_EVENT_TYPES as readonly string[]).includes(event.type);
}

export type Claim =
  | AcrobatClaim
  | InvestigatorClaim
  | LibrarianClaim
  | WasherwomanClaim
  | ChefClaim
  | ChambermaidClaim
  | EmpathClaim
  | ExorcistClaim
  | FlowergirlClaim
  | FortuneTellerClaim
  | UndertakerClaim
  | LegionaryClaim
  | NobleClaim
  | OracleClaim
  | StewardClaim
  | KnightClaim
  | GamblerClaim
  | GossipClaim
  | PhilosopherClaim
  | PrincessClaim
  | ProdigyClaim
  | PuzzlemasterClaim
  | SeamstressClaim
  | JugglerClaim
  | DreamerClaim
  | ShugenjaClaim
  | ClockmakerClaim
  | CourtierClaim
  | MathematicianClaim
  | TownCrierClaim
  | RavenkeeperClaim
  | SageClaim
  | SlayerClaim
  | SnakeCharmerClaim
  | VillageIdiotClaim
  | KlutzClaim
  | VirginClaim
  | BalloonistClaim
  | SavantClaim
  | NightwatchmanClaim
  | BareClaim;

interface BaseClaim {
  readonly name: string;
  readonly timing?: string;
  readonly possibleActualRoles?: readonly string[];
  readonly heardWidowCall?: boolean;
  readonly knownEvilTwin?: string;
  readonly info?: readonly CustomInfoStatementDoc[];
}

export interface CustomInfoStatementDoc {
  readonly timing?: string;
  readonly role?: string;
  readonly expression?: string;
}

export interface AcrobatChoiceDoc {
  readonly player: string;
  readonly timing?: string;
  readonly died: boolean;
}

export interface AcrobatClaim extends BaseClaim {
  readonly type: "Acrobat";
  readonly choices?: readonly AcrobatChoiceDoc[];
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
  readonly among?: readonly string[];
}

export interface WasherwomanClaim extends BaseClaim {
  readonly type: "Washerwoman";
  readonly role?: string;
  readonly among: readonly string[];
}

export interface ChefClaim extends BaseClaim {
  readonly type: "Chef";
  readonly count?: number;
}

export interface ChambermaidCheckDoc {
  readonly left: string;
  readonly right: string;
  readonly count: number;
  readonly timing?: string;
}

export interface ChambermaidClaim extends BaseClaim {
  readonly type: "Chambermaid";
  readonly checks?: readonly ChambermaidCheckDoc[];
}

export interface EmpathClaim extends BaseClaim {
  readonly type: "Empath";
  readonly count?: number;
}

export interface ExorcistChoiceDoc {
  readonly player: string;
  readonly timing?: string;
}

export interface ExorcistClaim extends BaseClaim {
  readonly type: "Exorcist";
  readonly choices?: readonly ExorcistChoiceDoc[];
}

export interface FortuneTellerCheckDoc {
  readonly left: string;
  readonly right: string;
  readonly yes: boolean;
  readonly timing?: string;
}

export interface FlowergirlVoteDoc {
  readonly timing: string;
  readonly voters: readonly string[];
  readonly demonVoted: boolean;
}

export interface FlowergirlClaim extends BaseClaim {
  readonly type: "Flowergirl";
  readonly votes?: readonly FlowergirlVoteDoc[];
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

export interface LegionaryCountDoc {
  readonly count: number;
  readonly timing?: string;
  readonly alivePlayers?: readonly string[];
}

export interface LegionaryClaim extends BaseClaim {
  readonly type: "Legionary";
  readonly counts?: readonly LegionaryCountDoc[];
}

export interface NobleClaim extends BaseClaim {
  readonly type: "Noble";
  readonly oneEvilAmong?: readonly string[];
  readonly among?: readonly string[];
  readonly evilCount?: number;
}

export interface OracleClaim extends BaseClaim {
  readonly type: "Oracle";
  readonly count?: number;
}

export interface StewardClaim extends BaseClaim {
  readonly type: "Steward";
  readonly goodPlayer?: string;
}

export interface KnightClaim extends BaseClaim {
  readonly type: "Knight";
  readonly noDemonAmong: readonly string[];
}

export interface GamblerGuessDoc {
  readonly player: string;
  readonly role: string;
  readonly timing?: string;
  readonly survived?: boolean;
}

export interface GamblerClaim extends BaseClaim {
  readonly type: "Gambler";
  readonly guesses?: readonly GamblerGuessDoc[];
}

export interface GossipStatementDoc {
  readonly expression: string;
  readonly timing?: string;
}

export interface GossipClaim extends BaseClaim {
  readonly type: "Gossip";
  readonly statements?: readonly GossipStatementDoc[];
}

export interface PhilosopherClaim extends BaseClaim {
  readonly type: "Philosopher";
  readonly role?: string;
  readonly seamstress?: PhilosopherSeamstressInfoDoc;
}

export interface PrincessNominationDoc {
  readonly player: string;
  readonly timing?: string;
}

export interface PrincessClaim extends BaseClaim {
  readonly type: "Princess";
  readonly nominations?: readonly PrincessNominationDoc[];
}

export interface PhilosopherSeamstressInfoDoc {
  readonly among: readonly string[];
  readonly aligned?: boolean;
  readonly timing?: string;
}

export interface ProdigyCheckDoc {
  readonly chosen: string;
  readonly learned: string;
  readonly timing?: string;
}

export interface ProdigyClaim extends BaseClaim {
  readonly type: "Prodigy";
  readonly checks: readonly ProdigyCheckDoc[];
}

export interface PuzzlemasterGuessDoc {
  readonly player: string;
  readonly learnedDemon: string;
  readonly timing?: string;
}

export interface PuzzlemasterClaim extends BaseClaim {
  readonly type: "Puzzlemaster";
  readonly guesses?: readonly PuzzlemasterGuessDoc[];
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
  readonly distance?: number;
}

export interface CourtierClaim extends BaseClaim {
  readonly type: "Courtier";
  readonly role?: string;
  readonly drunkTimings?: readonly string[];
}

export interface MathematicianCountDoc {
  readonly timing: string;
  readonly count: number;
}

export interface MathematicianClaim extends BaseClaim {
  readonly type: "Mathematician";
  readonly malfunctions?: readonly MathematicianCountDoc[];
  readonly countsDrunkInfo?: boolean;
}

export interface TownCrierCheckDoc {
  readonly timing: string;
  readonly nominators: readonly string[];
  readonly minionNominated: boolean;
}

export interface TownCrierClaim extends BaseClaim {
  readonly type: "Town Crier";
  readonly checks: readonly TownCrierCheckDoc[];
}

export interface RavenkeeperClaim extends BaseClaim {
  readonly type: "Ravenkeeper";
  readonly player?: string;
  readonly role?: string;
}

export interface SageClaim extends BaseClaim {
  readonly type: "Sage";
  readonly demonAmong?: readonly string[];
}

export interface SlayerClaim extends BaseClaim {
  readonly type: "Slayer";
  readonly target?: string;
  readonly killed?: boolean;
  readonly gameContinued?: boolean;
}

export interface SnakeCharmerCheckDoc {
  readonly player: string;
  readonly demon: boolean;
  readonly timing: string;
}

export interface SnakeCharmerClaim extends BaseClaim {
  readonly type: "Snake Charmer";
  readonly checks: readonly SnakeCharmerCheckDoc[];
}

export interface VillageIdiotCheckDoc {
  readonly player: string;
  readonly good: boolean;
  readonly timing?: string;
}

export interface VillageIdiotClaim extends BaseClaim {
  readonly type: "VillageIdiot";
  readonly checks: readonly VillageIdiotCheckDoc[];
}

export interface KlutzClaim extends BaseClaim {
  readonly type: "Klutz";
  readonly chosen?: string;
}

export interface VirginClaim extends BaseClaim {
  readonly type: "Virgin";
  readonly nominator?: string;
  readonly executed?: boolean;
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

export interface NightwatchmanClaim extends BaseClaim {
  readonly type: "Nightwatchman";
  readonly chosen?: string;
  readonly learned?: boolean;
  readonly confirmedByChosen?: boolean;
}

export const BARE_CLAIM_TYPES = [
  "Alsaahir",
  "Artist",
  "Atheist",
  "Baron",
  "Boffin",
  "Butler",
  "Cerenovus",
  "Damsel",
  "Devil's Advocate",
  "Drunk",
  "Evil Twin",
  "Golem",
  "Goblin",
  "Hermit",
  "Imp",
  "Kazali",
  "Legion",
  "Leviathan",
  "Lord of Typhon",
  "Lunar Prodigy",
  "Lunatic",
  "Marionette",
  "Mayor",
  "Mutant",
  "No Dashii",
  "Pit-Hag",
  "Po",
  "Poisoner",
  "Politician",
  "Poppy Grower",
  "Pukka",
  "Recluse",
  "Riot",
  "Saint",
  "Scarlet Woman",
  "Soldier",
  "Solar Prodigy",
  "Spy",
  "Sweetheart",
  "Tea Lady",
  "Vortox",
  "Widow",
  "Witch",
  "Xaan",
] as const;

export type BareClaimType = (typeof BARE_CLAIM_TYPES)[number];

export interface BareClaim extends BaseClaim {
  readonly type: BareClaimType;
}

export const STRUCTURED_CLAIM_TYPES = [
  "Acrobat",
  "Investigator",
  "Librarian",
  "Washerwoman",
  "Chef",
  "Chambermaid",
  "Empath",
  "Exorcist",
  "Flowergirl",
  "FortuneTeller",
  "Undertaker",
  "Legionary",
  "Noble",
  "Oracle",
  "Steward",
  "Knight",
  "Gambler",
  "Gossip",
  "Philosopher",
  "Princess",
  "Prodigy",
  "Puzzlemaster",
  "Seamstress",
  "Juggler",
  "Dreamer",
  "Shugenja",
  "Clockmaker",
  "Courtier",
  "Mathematician",
  "Town Crier",
  "Ravenkeeper",
  "Sage",
  "Slayer",
  "Snake Charmer",
  "VillageIdiot",
  "Klutz",
  "Virgin",
  "Balloonist",
  "Savant",
  "Nightwatchman",
] as const satisfies readonly Claim["type"][];

export const SUPPORTED_CLAIM_TYPES = new Set<Claim["type"]>([...STRUCTURED_CLAIM_TYPES, ...BARE_CLAIM_TYPES]);
