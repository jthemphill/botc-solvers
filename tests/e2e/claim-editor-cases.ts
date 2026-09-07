import type { Claim } from "../../src/schema/puzzleDoc";

export const CLAIM_EDITOR_CASES: readonly {
  name: string;
  script: readonly string[];
  claims: readonly Claim[];
}[] = [
  {
    name: "counts, directions, and repeated counts",
    script: ["Chef", "Empath", "Oracle", "Clockmaker", "Shugenja", "Legionary", "Mathematician"],
    claims: [
      { type: "Chef", name: "Ada", count: 2, timing: "night_1" },
      { type: "Empath", name: "Ada", count: 0, timing: "night_2" },
      { type: "Oracle", name: "Ada", count: 1, timing: "night_3" },
      { type: "Clockmaker", name: "Ada", distance: 3, timing: "night_1" },
      { type: "Shugenja", name: "Ada", evilDirection: "anticlockwise", timing: "night_1" },
      {
        type: "Legionary",
        name: "Ada",
        counts: [
          { count: 2, timing: "night_1" },
          { count: 1, timing: "night_2" },
        ],
      },
      {
        type: "Mathematician",
        name: "Ada",
        malfunctions: [
          { count: 1, timing: "night_1" },
          { count: 0, timing: "night_2" },
        ],
      },
    ],
  },
  {
    name: "learned roles and player selections",
    script: [
      "Investigator",
      "Washerwoman",
      "Librarian",
      "Undertaker",
      "Ravenkeeper",
      "Grandmother",
      "Poisoner",
      "Chef",
      "Drunk",
    ],
    claims: [
      { type: "Investigator", name: "Ada", role: "Poisoner", among: ["Ben", "Cara"], timing: "night_1" },
      { type: "Washerwoman", name: "Ada", role: "Chef", among: ["Ada", "Cara"], timing: "night_1" },
      { type: "Librarian", name: "Ada", role: "Drunk", among: ["Ben", "Cara"], timing: "night_1" },
      { type: "Undertaker", name: "Ada", player: "Cara", role: "Chef", timing: "night_2" },
      { type: "Ravenkeeper", name: "Ada", player: "Ben", role: "Poisoner", timing: "night_3" },
      { type: "Grandmother", name: "Ada", grandchild: "Cara", role: "Chef", timing: "night_1" },
    ],
  },
  {
    name: "player groups and alignment information",
    script: ["Noble", "Knight", "Sage", "Steward", "Seamstress"],
    claims: [
      { type: "Noble", name: "Ada", oneEvilAmong: ["Ada", "Ben", "Cara"] },
      { type: "Knight", name: "Ada", noDemonAmong: ["Ben", "Cara"] },
      { type: "Sage", name: "Ada", demonAmong: ["Ada", "Ben"], timing: "night_2" },
      { type: "Steward", name: "Ada", goodPlayer: "Cara" },
      { type: "Seamstress", name: "Ada", among: ["Cara", "Ben"], aligned: false, timing: "night_2" },
    ],
  },
  {
    name: "single-night reports, repeated checks, and radio choices",
    script: ["Fortune Teller", "Snake Charmer", "Village Idiot", "Chambermaid", "Balloonist"],
    claims: [
      { type: "FortuneTeller", name: "Ada", checks: [{ left: "Ben", right: "Cara", yes: true, timing: "night_1" }] },
      { type: "FortuneTeller", name: "Ada", checks: [{ left: "Cara", right: "Ada", yes: false, timing: "night_2" }] },
      { type: "Snake Charmer", name: "Ada", checks: [{ player: "Ben", demon: false, timing: "night_1" }] },
      { type: "Snake Charmer", name: "Ada", checks: [{ player: "Cara", demon: true, timing: "night_2" }] },
      {
        type: "VillageIdiot",
        name: "Ada",
        checks: [
          { player: "Ben", good: false, timing: "night_1" },
          { player: "Cara", good: true, timing: "night_2" },
        ],
      },
      {
        type: "Chambermaid",
        name: "Ada",
        checks: [
          { left: "Ben", right: "Cara", count: 2, timing: "night_2" },
          { left: "Cara", right: "Ben", count: 1, timing: "night_3" },
        ],
      },
      {
        type: "Balloonist",
        name: "Ada",
        differentCharacterTypePairs: [
          ["Ben", "Cara"],
          ["Cara", "Ada"],
        ],
        timing: "night_2",
      },
    ],
  },
  {
    name: "role lists, per-player guesses, and repeated guesses",
    script: ["Dreamer", "Juggler", "Gambler", "Chef", "Imp"],
    claims: [
      { type: "Dreamer", name: "Ada", player: "Ben", roles: ["Chef", "Imp"], timing: "night_2" },
      { type: "Juggler", name: "Ada", guesses: { Ben: "Chef", Cara: "Imp" }, correctCount: 1, timing: "night_2" },
      {
        type: "Gambler",
        name: "Ada",
        guesses: [
          { player: "Ben", role: "Chef", timing: "night_2" },
          { player: "Cara", role: "Imp", timing: "night_3" },
        ],
      },
    ],
  },
  {
    name: "nightly targets, protected pairs, and known Outsiders",
    script: ["Acrobat", "Exorcist", "Innkeeper", "Sailor", "Devil's Advocate", "Godfather", "Moonchild", "Tinker"],
    claims: [
      {
        type: "Acrobat",
        name: "Ada",
        choices: [
          { player: "Ben", died: false, timing: "night_2" },
          { player: "Cara", died: true, timing: "night_3" },
        ],
      },
      { type: "Exorcist", name: "Ada", choices: [{ player: "Cara", timing: "night_2" }] },
      {
        type: "Innkeeper",
        name: "Ada",
        choices: [
          { players: ["Ben", "Cara"], timing: "night_2" },
          { players: ["Ben", "Cara"], timing: "night_3" },
        ],
      },
      { type: "Sailor", name: "Ada", choices: [{ player: "Ben", timing: "night_2" }] },
      { type: "Devil's Advocate", name: "Ada", choices: [{ player: "Cara", timing: "night_2" }] },
      {
        type: "Godfather",
        name: "Ada",
        outsiderRoles: ["Moonchild", "Tinker"],
        choices: [{ player: "Ben", timing: "night_3" }],
      },
    ],
  },
  {
    name: "votes and nominations with positive and negative reports",
    script: ["Flowergirl", "Town Crier", "Princess", "Virgin"],
    claims: [
      {
        type: "Flowergirl",
        name: "Ada",
        votes: [
          { timing: "day_1", voters: ["Ben", "Cara"], demonVoted: true },
          { timing: "day_2", voters: [], demonVoted: false },
        ],
      },
      {
        type: "Town Crier",
        name: "Ada",
        checks: [
          { timing: "night_2", nominators: ["Cara"], minionNominated: true },
          { timing: "night_3", nominators: [], minionNominated: false },
        ],
      },
      {
        type: "Princess",
        name: "Ada",
        nominations: [
          { player: "Ben", timing: "day_1" },
          { player: "Cara", timing: "day_2" },
        ],
      },
      { type: "Virgin", name: "Ada", nominator: "Cara", executed: false, timing: "day_1" },
    ],
  },
  {
    name: "action targets, death choices, and confirmation",
    script: ["Assassin", "Professor", "Slayer", "Moonchild", "Klutz", "Nightwatchman"],
    claims: [
      { type: "Assassin", name: "Ada", target: "Cara", timing: "night_2" },
      { type: "Professor", name: "Ada", target: "Ben", timing: "night_3" },
      { type: "Slayer", name: "Ada", target: "Cara", killed: false, timing: "day_2" },
      { type: "Moonchild", name: "Ada", chosen: "Ben", timing: "day_2" },
      { type: "Klutz", name: "Ada", chosen: "Cara", timing: "day_3" },
      { type: "Nightwatchman", name: "Ada", chosen: "Cara", learned: true, confirmedByChosen: true, timing: "night_1" },
    ],
  },
  {
    name: "chosen and learned players",
    script: ["Solar Prodigy", "Lunar Prodigy", "Puzzlemaster"],
    claims: [
      {
        type: "Prodigy",
        name: "Ada",
        checks: [
          { chosen: "Ben", learned: "Cara", timing: "night_1" },
          { chosen: "Cara", learned: "Ada", timing: "night_2" },
        ],
      },
      {
        type: "Puzzlemaster",
        name: "Ada",
        guesses: [{ player: "Ben", learnedDemon: "Cara", timing: "day_2" }],
        timing: "day_2",
      },
    ],
  },
  {
    name: "role choices, drunk timings, and conditional ability fields",
    script: ["Courtier", "Philosopher", "Seamstress", "Imp"],
    claims: [
      {
        type: "Courtier",
        name: "Ada",
        role: "Imp",
        timing: "night_2",
        drunkTimings: ["night_2", "night_3", "night_4"],
      },
      {
        type: "Philosopher",
        name: "Ada",
        role: "Seamstress",
        timing: "night_1",
        seamstress: { among: ["Cara", "Ben"], aligned: false, timing: "night_2" },
      },
    ],
  },
  {
    name: "expression fields and advanced claim details",
    script: ["Artist", "Savant", "Gossip", "Soldier", "Drunk", "Evil Twin", "Imp", "Widow"],
    claims: [
      {
        type: "Artist",
        name: "Ada",
        timing: "day_1",
        info: [{ expression: "Ben.initial_role == Imp", timing: "day_1" }],
      },
      {
        type: "Savant",
        name: "Ada",
        timing: "day_1",
        statements: [{ options: ["Ben.initial_role == Imp", "Cara.alignment == Evil"] }],
      },
      {
        type: "Gossip",
        name: "Ada",
        statements: [
          { expression: "Ben.initial_role == Imp", timing: "day_1" },
          { expression: "Cara.alignment == Evil", timing: "day_2" },
        ],
      },
      {
        type: "Soldier",
        name: "Ada",
        roleTiming: "night_2",
        alignment: "good",
        possibleActualRoles: ["Drunk", "Soldier"],
        heardWidowCall: true,
        knownEvilTwin: "Cara",
      },
    ],
  },
];
