import { ROLE_CLASSES } from "./roleRegistry";

const ROLE_EMOJI_ENTRIES = [
  ["Acrobat", "🤸"],
  ["Alsaahir", "🧞"],
  ["Artist", "🎨"],
  ["Atheist", "🚫"],
  ["Balloonist", "🎈"],
  ["Baron", "🎩"],
  ["Boffin", "🧪"],
  ["Butler", "🛎️"],
  ["Cerenovus", "🧠"],
  ["Chambermaid", "🧹"],
  ["Chef", "🧑‍🍳"],
  ["Clockmaker", "🕰️"],
  ["Courtier", "🍷"],
  ["Damsel", "🕯️"],
  ["Devil's Advocate", "⚖️"],
  ["Dreamer", "💭"],
  ["Drunk", "🍺"],
  ["Empath", "💗"],
  ["Exorcist", "🧳"],
  ["Evil Twin", "🪞"],
  ["Fang Gu", "🐉"],
  ["Flowergirl", "🌸"],
  ["Fortune Teller", "🔮"],
  ["Gambler", "🎲"],
  ["Golem", "🗿"],
  ["Goblin", "👺"],
  ["Godfather", "🫒"],
  ["Gossip", "🗣️"],
  ["Hermit", "🛟"],
  ["Imp", "👹"],
  ["Investigator", "🔎"],
  ["Juggler", "🤹"],
  ["Kazali", "🌀"],
  ["Klutz", "🫨"],
  ["Knight", "⚔️"],
  ["Legionary", "🪖"],
  ["Legion", "✋"],
  ["Leviathan", "🐋"],
  ["Librarian", "📖"],
  ["Lord of Typhon", "🌋"],
  ["Lunar Prodigy", "🌙"],
  ["Lunatic", "🌙"],
  ["Marionette", "🪆"],
  ["Mathematician", "🧮"],
  ["Mayor", "🏛️"],
  ["Monk", "🙏"],
  ["Mutant", "🧬"],
  ["Nightwatchman", "🏮"],
  ["No Dashii", "☣️"],
  ["Noble", "👑"],
  ["Oracle", "👁️"],
  ["Philosopher", "📜"],
  ["Pit-Hag", "🧙"],
  ["Po", "💥"],
  ["Poisoner", "☠️"],
  ["Politician", "🏳️"],
  ["Poppy Grower", "🌺"],
  ["Princess", "👸"],
  ["Pukka", "🩸"],
  ["Puzzlemaster", "🧩"],
  ["Ravenkeeper", "🪶"],
  ["Recluse", "🕸️"],
  ["Riot", "🚩"],
  ["Sage", "📚"],
  ["Saint", "😇"],
  ["Savant", "🧠"],
  ["Scarlet Woman", "💋"],
  ["Seamstress", "🧵"],
  ["Shugenja", "🏯"],
  ["Slayer", "🏹"],
  ["Snake Charmer", "🐍"],
  ["Soldier", "🛡️"],
  ["Solar Prodigy", "☀️"],
  ["Spy", "🕵️"],
  ["Steward", "🗝️"],
  ["Sweetheart", "💔"],
  ["Tea Lady", "🍵"],
  ["Undertaker", "⚰️"],
  ["Village Idiot", "🃏"],
  ["Virgin", "💍"],
  ["Vigormortis", "🧟"],
  ["Vortox", "🌀"],
  ["Washerwoman", "🧺"],
  ["Widow", "🕷️"],
  ["Witch", "🪄"],
  ["Xaan", "⚡"],
] as const;

const ROLE_EMOJIS = new Map<string, string>(ROLE_EMOJI_ENTRIES);
const ROLE_NAMES_BY_NORMALIZED_NAME = new Map(
  ROLE_EMOJI_ENTRIES.map(([role]) => [normalizeRoleName(role), role] as const),
);

const missingRoles = [...ROLE_CLASSES.keys()].filter((role) => !ROLE_EMOJIS.has(role));
if (missingRoles.length > 0) {
  throw new Error(`Missing role emoji for: ${missingRoles.join(", ")}`);
}

export const ROLE_EMOJI_BY_NAME: ReadonlyMap<string, string> = ROLE_EMOJIS;

export function canonicalEmojiRoleName(role: string | undefined): string | undefined {
  if (!role) return undefined;
  if (ROLE_EMOJIS.has(role)) return role;
  return ROLE_NAMES_BY_NORMALIZED_NAME.get(normalizeRoleName(role));
}

export function roleEmoji(role: string | undefined): string | undefined {
  const canonical = canonicalEmojiRoleName(role);
  return canonical === undefined ? undefined : ROLE_EMOJIS.get(canonical);
}

export function roleEmojiLabel(role: string | undefined): string {
  if (!role) return "";
  const canonical = canonicalEmojiRoleName(role);
  const emoji = roleEmoji(role);
  return canonical === undefined || emoji === undefined ? role : `${emoji} ${canonical}`;
}

function normalizeRoleName(role: string): string {
  return role.toLowerCase().replace(/[^a-z0-9]+/g, "");
}
