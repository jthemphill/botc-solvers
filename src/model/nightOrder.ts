import type { Timing } from "./timing";

/**
 * The order of night actions on nights after the first night.
 * The list includes each supported character that chooses players or causes deaths at night.
 * It follows the official night sheet.
 */
const OTHER_NIGHTS: readonly string[] = [
  "Sailor",
  "Poisoner",
  "Widow",
  "Courtier",
  "Innkeeper",
  "Gambler",
  "Acrobat",
  "Snake Charmer",
  "Monk",
  "Devil's Advocate",
  "Witch",
  "Cerenovus",
  "Pit-Hag",
  "Exorcist",
  "Legion",
  "Riot",
  "Imp",
  "Zombuul",
  "Pukka",
  "Shabaloth",
  "Po",
  "Fang Gu",
  "No Dashii",
  "Vortox",
  "Lord of Typhon",
  "Vigormortis",
  "Lleech",
  "Kazali",
  "Leviathan",
  "Assassin",
  "Godfather",
  "Gossip",
  "Professor",
  "Tinker",
  "Moonchild",
  "Ravenkeeper",
  "Fortune Teller",
  "Dreamer",
  "Seamstress",
  "Village Idiot",
  "Nightwatchman",
  "Butler",
  "Chambermaid",
];

/** On the first night, the Lleech acts before the Poisoner and the Butler acts before the Dreamer. */
const FIRST_NIGHT: readonly string[] = moveBefore(moveBefore(OTHER_NIGHTS, "Lleech", "Poisoner"), "Butler", "Dreamer");

function moveBefore(order: readonly string[], role: string, successor: string): readonly string[] {
  const rest = order.filter((entry) => entry !== role);
  const index = rest.indexOf(successor);
  return [...rest.slice(0, index), role, ...rest.slice(index)];
}

/**
 * Returns the position of a character in the night order. A smaller number acts earlier.
 * Positions are 10 apart, so a caller can put an effect between two characters.
 */
export function nightActionOrder(role: string, timing?: Timing): number {
  const index = (timing === "night_1" ? FIRST_NIGHT : OTHER_NIGHTS).indexOf(role);
  if (index === -1) throw new Error(`${role} has no night order.`);
  return index * 10;
}
