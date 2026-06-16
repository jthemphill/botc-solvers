import { beforeAll, describe, expect, test } from "bun:test";
import { buildFromDoc } from "../builders/buildFromDoc";
import { CharacterType, roleCharacterType } from "../model/core";
import type { Timing, World } from "../model/model";
import { roleByName } from "../model/roleRegistry";
import { KissatBackend, type SatBackend } from "../model/sat";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { validatePuzzleDoc } from "../schema/validate";
import { PUZZLE_EXAMPLES } from "./puzzleCatalog";

const JSON_SOLUTION_COUNTS: Readonly<Record<string, number>> = {
  "puzzle-01-sober-savant": 1,
  "puzzle-02-come-fly-with-me": 1,
  "puzzle-03a-not-throwing-away-my-shot": 11,
  "puzzle-03b-not-throwing-away-my-shot": 12,
  "puzzle-04-the-many-headed-monster": 16,
  "puzzle-05a-you-only-guess-twice": 2,
  "puzzle-05b-you-only-guess-twice": 4,
  "puzzle-06-super-marionette-bros": 1,
  "puzzle-07-the-savant-strikes-back": 39,
  "puzzle-08-the-stitch-up": 2,
  "puzzle-09-the-new-acrobat": 88,
  "puzzle-10-dont-overcook-it": 1,
  "puzzle-11-false-is-the-new-black": 60,
  "puzzle-12a-thunderstruck": 17,
  "puzzle-12b-thunderstruck": 41,
  "puzzle-13-clockblocking": 1,
  "puzzle-14-new-super-marionette-bros": 1,
  "puzzle-15-wake-up-and-choose-violets": 60,
  "puzzle-16-who-watches-the-watchmen": 1,
  "puzzle-17-the-missing-piece": 89,
  "puzzle-18-x-and-the-city": 1,
  "puzzle-19-he-could-be-you-he-could-be-me": 1,
  "puzzle-20-the-three-wise-men": 1,
  "puzzle-21-eight-jugglers-juggling": 1,
  "puzzle-22-one-in-the-chamber": 54,
  "puzzle-23-goblincore": 6,
  "puzzle-24-the-ultimate-blunder": 1,
  "puzzle-26-a-major-problem": 36,
  "puzzle-27-is-this-a-legion-game": 1,
  "puzzle-28-a-study-in-scarlet": 1,
  "puzzle-29-a-dreamer-im-not-the-only-one": 1,
  "puzzle-30-the-babel-fish-is-a-dead-giveaway-left": 1,
  "puzzle-30-the-babel-fish-is-a-dead-giveaway-right": 1,
  "puzzle-31-no-your-other-left": 97,
  "puzzle-32-prepare-for-juggle-and-make-it-double": 35,
  "puzzle-33-twice-is-coincidence-thrice-is-proof": 59,
  "puzzle-34-the-vortox-conjecture": 1,
  "puzzle-35-typhon-season": 1,
  "puzzle-36-what-is-your-weapon-of-choice": 1,
  "puzzle-37-new-super-marionette-bros-u": 12,
  "puzzle-38-snakes-on-a-plane": 56,
  "puzzle-39-squid-game": 22,
  "puzzle-40-nine-lives": 1,
};

interface PoisonLock {
  readonly player: string;
  readonly timing: Timing;
}

interface PublishedWorldLock {
  readonly roles?: Readonly<Record<string, string>>;
  readonly roleIn?: Readonly<Record<string, readonly string[]>>;
  readonly characterTypes?: Readonly<Record<string, CharacterType>>;
  readonly poisoned?: readonly PoisonLock[];
  readonly drunk?: readonly string[];
}

interface PublishedSolutionLock {
  readonly id: string;
  readonly source: string;
  readonly worlds: readonly PublishedWorldLock[];
}

interface PublishedSolutionGap {
  readonly source: string;
  readonly reason: string;
}

interface PuzzleSolutionCase {
  readonly id: string;
  readonly data: unknown;
  readonly expectedCount: number;
}

const SOLUTION_COUNT_TIMEOUT_MS = 120_000;
const PUBLISHED_WORLD_TIMEOUT_MS = 60_000;

const PUBLISHED_SOLUTION_LOCKS: readonly PublishedSolutionLock[] = [
  {
    id: "puzzle-01-sober-savant",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1erb5e2/can_the_sober_savant_solve_the_puzzle/",
    worlds: [{ roles: { Anna: "Imp", Tim: "Scarlet Woman", Oscar: "Drunk" } }],
  },
  {
    id: "puzzle-02-come-fly-with-me",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1ewxu0r/weekly_puzzle_2_come_fly_with_me/",
    worlds: [{ roles: { Matthew: "Leviathan", Sarah: "Goblin", You: "Drunk" } }],
  },
  {
    id: "puzzle-03a-not-throwing-away-my-shot",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1f2jht3/weekly_puzzle_3a_3b_not_throwing_away_my_shot/",
    worlds: [{ roles: { Matthew: "Imp", Aoife: "Baron", Oscar: "Drunk" } }],
  },
  {
    id: "puzzle-03b-not-throwing-away-my-shot",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1f2jht3/weekly_puzzle_3a_3b_not_throwing_away_my_shot/",
    worlds: [{ roles: { Sarah: "Imp", Hannah: "Spy" } }],
  },
  {
    id: "puzzle-04-the-many-headed-monster",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1f823s4/weekly_puzzle_4_the_manyheaded_monster/",
    worlds: [
      {
        roles: { Fraser: "Lord of Typhon", Anna: "Drunk" },
        characterTypes: { Dan: CharacterType.Minion, Sarah: CharacterType.Minion },
        poisoned: [
          { player: "You", timing: "night_1" },
          { player: "Matt", timing: "night_2" },
        ],
      },
    ],
  },
  {
    id: "puzzle-05a-you-only-guess-twice",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1fcriex/weekly_puzzle_5a_5b_you_only_guess_twice/",
    worlds: [{ roles: { Oscar: "Leviathan", Anna: "Goblin" } }, { roles: { Hannah: "Leviathan", Oscar: "Goblin" } }],
  },
  {
    id: "puzzle-05b-you-only-guess-twice",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1fcriex/weekly_puzzle_5a_5b_you_only_guess_twice/",
    worlds: [
      { roles: { Aoife: "Leviathan", Sarah: "Goblin" } },
      { roles: { Aoife: "Leviathan", Steph: "Goblin" } },
      { roles: { Matthew: "Leviathan", Steph: "Goblin" } },
      { roles: { Sarah: "Leviathan", Steph: "Goblin" } },
    ],
  },
  {
    id: "puzzle-06-super-marionette-bros",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1fj1h0c/weekly_puzzle_6_super_marionette_bros/",
    worlds: [{ roles: { Matthew: "Vortox", You: "Marionette", Steph: "Drunk" } }],
  },
  {
    id: "puzzle-07-the-savant-strikes-back",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1foeq4d/weekly_puzzle_7_the_savant_strikes_back/",
    worlds: [
      {
        roles: {
          Anna: "Leviathan",
          Aoife: "Shugenja",
          Steph: "Mutant",
          Tim: "Village Idiot",
          Fraser: "Village Idiot",
          Sarah: "Fortune Teller",
          Oscar: "Goblin",
        },
        drunk: ["Tim"],
      },
    ],
  },
  {
    id: "puzzle-12a-thunderstruck",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1gexyoq/weekly_puzzle_12a_12b_thunderstruck/",
    worlds: [{ roles: { Sarah: "Spy", Jasmine: "Vortox", Fraser: "Lunatic" } }],
  },
  {
    id: "puzzle-12b-thunderstruck",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1gexyoq/weekly_puzzle_12a_12b_thunderstruck/",
    worlds: [{ roles: { Steph: "Scarlet Woman", Oscar: "Vortox", Anna: "Lunatic" } }],
  },
  {
    id: "puzzle-08-the-stitch-up",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1ftqc28/weekly_puzzle_8_the_stitchup/",
    worlds: [
      {
        roleIn: { Josh: ["Imp", "Poisoner"], Steph: ["Imp", "Poisoner"] },
        poisoned: [{ player: "You", timing: "night_1" }],
      },
    ],
  },
  {
    id: "puzzle-09-the-new-acrobat",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1fz4jqe/weekly_puzzle_9_the_new_acrobat/",
    worlds: [{ roles: { Anna: "Imp", Hannah: "Goblin", Josh: "Drunk" } }],
  },
  {
    id: "puzzle-10-dont-overcook-it",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1g49r8j/weekly_puzzle_10_dont_overcook_it/",
    worlds: [
      {
        roles: { Dan: "Imp", Fraser: "Poisoner" },
        poisoned: [
          { player: "Josh", timing: "night_1" },
          { player: "Matthew", timing: "night_2" },
        ],
      },
    ],
  },
  {
    id: "puzzle-11-false-is-the-new-black",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1g9k8ny/weekly_puzzle_11_false_is_the_new_black/",
    worlds: [{ roles: { Aoife: "Vortox" }, roleIn: { Sarah: ["Cerenovus", "Pit-Hag"] } }],
  },
  {
    id: "puzzle-13-clockblocking",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1gka3js/weekly_puzzle_13_clockblocking/",
    worlds: [{ roles: { Fraser: "Imp", Oscar: "Baron", Tim: "Drunk" } }],
  },
  {
    id: "puzzle-14-new-super-marionette-bros",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1gpo1xo/weekly_puzzle_14_new_super_marionette_bros/",
    worlds: [
      {
        roles: { Lav: "Imp", Lydia: "Poisoner" },
        poisoned: [
          { player: "Rob", timing: "night_1" },
          { player: "Rob", timing: "night_2" },
        ],
      },
    ],
  },
  {
    id: "puzzle-15-wake-up-and-choose-violets",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1gv12ck/weekly_puzzle_15_wake_up_and_choose_violets/",
    worlds: [{ roles: { Adam: "Vortox", Jasmine: "Evil Twin" } }],
  },
  {
    id: "puzzle-16-who-watches-the-watchmen",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1h0f8se/weekly_puzzle_16_who_watches_the_watchmen/",
    worlds: [
      {
        roles: { Oscar: "Imp", Fraser: "Poisoner" },
        poisoned: [
          { player: "Sarah", timing: "night_1" },
          { player: "Olivia", timing: "night_2" },
        ],
      },
    ],
  },
  {
    id: "puzzle-17-the-missing-piece",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1h5sgc7/weekly_puzzle_17_the_missing_piece/",
    worlds: [{ drunk: ["Steph"] }],
  },
  {
    id: "puzzle-18-x-and-the-city",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1hb72qg/weekly_puzzle_18_starring_the_xaan/",
    worlds: [
      {
        roles: {
          Aoife: "Balloonist",
          Tim: "Saint",
          Olivia: "Xaan",
          Sarah: "Recluse",
          You: "Drunk",
          Steph: "Juggler",
          Fraser: "Leviathan",
          Dan: "Fortune Teller",
        },
        poisoned: [
          { player: "Aoife", timing: "night_3" },
          { player: "Steph", timing: "night_3" },
          { player: "Dan", timing: "night_3" },
        ],
      },
    ],
  },
  {
    id: "puzzle-19-he-could-be-you-he-could-be-me",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1hgdsmp/weekly_puzzle_19_he_could_be_you_he_could_be_me/",
    worlds: [{ roles: { Olivia: "Imp", Fraser: "Spy" } }],
  },
  {
    id: "puzzle-20-the-three-wise-men",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1hlgh1w/weekly_puzzle_20_the_three_wise_men/",
    worlds: [
      {
        roles: {
          Melchior: "Village Idiot",
          Mary: "Baron",
          Balthazar: "Imp",
          Gabriel: "Drunk",
        },
        drunk: ["Caspar"],
      },
    ],
  },
  {
    id: "puzzle-21-eight-jugglers-juggling",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1hpqhai/weekly_puzzle_21_eight_jugglers_juggling/",
    worlds: [{ roles: { Oscar: "Leviathan", Tim: "Goblin", Aoife: "Drunk" } }],
  },
  {
    id: "puzzle-22-one-in-the-chamber",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1hvum3b/weekly_puzzle_22_one_in_the_chamber/",
    worlds: [{ roles: { Sarah: "Imp", Steph: "Baron", You: "Drunk" } }],
  },
  {
    id: "puzzle-23-goblincore",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1i199yv/weekly_puzzle_23_goblincore/",
    worlds: [{ roles: { Sula: "Imp", Aoife: "Goblin", Fraser: "Lunatic" } }],
  },
  {
    id: "puzzle-24-the-ultimate-blunder",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1i6m0ww/weekly_puzzle_24_the_ultimate_blunder/",
    worlds: [{ roles: { Adam: "Imp", Josh: "Poisoner" } }],
  },
  {
    id: "puzzle-26-a-major-problem",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1ihl8vs/weekly_puzzle_26_a_major_problem/",
    worlds: [{ roles: { Tom: "Imp", Matthew: "Poisoner" } }],
  },
  {
    id: "puzzle-27-is-this-a-legion-game",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1in214z/weekly_puzzle_27_starring_the_legionary_from_fall/",
    worlds: [
      {
        roles: { Adam: "Imp", Fraser: "Poisoner" },
        poisoned: [
          { player: "Sarah", timing: "night_1" },
          { player: "Sarah", timing: "night_2" },
        ],
      },
    ],
  },
  {
    id: "puzzle-28-a-study-in-scarlet",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1iu1vxo/weekly_puzzle_28_a_study_in_scarlet/",
    worlds: [{ roles: { Olivia: "No Dashii", Fraser: "Scarlet Woman", Matt: "Drunk" } }],
  },
  {
    id: "puzzle-29-a-dreamer-im-not-the-only-one",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1ixykmz/weekly_puzzle_29_a_dreamer_im_not_the_only_one/",
    worlds: [
      {
        roles: { Adam: "Imp", Jasmine: "Poisoner", Hannah: "Drunk" },
        poisoned: [{ player: "Steph", timing: "night_1" }],
      },
    ],
  },
  {
    id: "puzzle-30-the-babel-fish-is-a-dead-giveaway-left",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1j46gtl/weekly_puzzle_30_which_is_the_atheist_game/",
    worlds: [
      {
        roles: {
          Sarah: "Seamstress",
          Max: "Artist",
          Erika: "Noble",
          Lav: "Clockmaker",
          Oli: "Atheist",
          Callum: "Knight",
        },
      },
    ],
  },
  {
    id: "puzzle-30-the-babel-fish-is-a-dead-giveaway-right",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1j46gtl/weekly_puzzle_30_which_is_the_atheist_game/",
    worlds: [{ roles: { Owen: "Imp", Louisa: "Spy", Finn: "Drunk" } }],
  },
  {
    id: "puzzle-31-no-your-other-left",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1j8ub5q/weekly_puzzle_31_no_your_other_left/",
    worlds: [{ roles: { Adam: "Imp", Sarah: "Baron", Tim: "Drunk" } }],
  },
  {
    id: "puzzle-32-prepare-for-juggle-and-make-it-double",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1je8z17/weekly_puzzle_32_prepare_for_juggle_and_make_it/",
    worlds: [{ roles: { Olivia: "Imp", Matthew: "Poisoner", Fraser: "Saint" } }],
  },
  {
    id: "puzzle-33-twice-is-coincidence-thrice-is-proof",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1jl7cuv/weekly_puzzle_33_twice_is_coincidence_thrice_is/",
    worlds: [{ roles: { Tom: "Imp", Sula: "Poisoner" } }],
  },
  {
    id: "puzzle-34-the-vortox-conjecture",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1joxqgy/weekly_puzzle_34_the_vortox_conjecture/",
    worlds: [{ roles: { Sula: "Vortox", Sarah: "Witch" } }],
  },
  {
    id: "puzzle-35-typhon-season",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1jv7zh2/weekly_puzzle_35_typhon_season/",
    worlds: [
      {
        roles: {
          Olivia: "Lord of Typhon",
          Oscar: "Spy",
          Sarah: "Poisoner",
          Jasmine: "Drunk",
        },
        poisoned: [
          { player: "Tim", timing: "night_1" },
          { player: "Sula", timing: "night_2" },
        ],
      },
    ],
  },
  {
    id: "puzzle-36-what-is-your-weapon-of-choice",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1k1exb7/weekly_puzzle_36_what_is_your_weapon_of_choice/",
    worlds: [
      {
        roles: { Fraser: "Imp", Oscar: "Poisoner" },
        poisoned: [
          { player: "Sula", timing: "night_1" },
          { player: "Josh", timing: "night_2" },
        ],
      },
    ],
  },
  {
    id: "puzzle-37-new-super-marionette-bros-u",
    source:
      "https://www.reddit.com/r/BloodOnTheClocktower/comments/1k7n8hi/weekly_puzzle_37_new_super_marionette_bros_u/",
    worlds: [
      {
        roles: { Fraser: "Imp", Jasmine: "Poisoner", Adam: "Drunk" },
        poisoned: [
          { player: "Sula", timing: "night_1" },
          { player: "You", timing: "night_2" },
          { player: "You", timing: "night_3" },
        ],
      },
    ],
  },
  {
    id: "puzzle-38-snakes-on-a-plane",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1kccbp9/weekly_puzzle_38_snakes_on_a_plane/",
    worlds: [{ roles: { Dan: "Imp", Tim: "Baron", Hannah: "Drunk" } }],
  },
  {
    id: "puzzle-39-squid-game",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1kg6y94/weekly_puzzle_39_squid_game/",
    worlds: [{ roles: { Jasmine: "No Dashii", Hannah: "Witch", Matt: "Mutant" } }],
  },
  {
    id: "puzzle-40-nine-lives",
    source: "https://www.reddit.com/r/BloodOnTheClocktower/comments/1klqy8j/weekly_puzzle_40_nine_lives/",
    worlds: [{ roles: { Adam: "Imp", Tim: "Baron", Jasmine: "Drunk" } }],
  },
];

const PUBLISHED_SOLUTION_GAPS: Readonly<Record<string, PublishedSolutionGap>> = {};

const EXAMPLES_BY_ID = new Map(PUZZLE_EXAMPLES.map((example) => [example.id, example]));

const PUZZLE_SOLUTION_CASES: PuzzleSolutionCase[] = PUZZLE_EXAMPLES.flatMap((example): PuzzleSolutionCase[] => {
  if (example.id === "intro") return [];
  const expectedCount = JSON_SOLUTION_COUNTS[example.id];
  if (expectedCount === undefined) throw new Error(`Missing expected solution count for ${example.id}`);
  return [{ id: example.id, data: example.data, expectedCount }];
});

describe("JSON puzzle solutions", () => {
  let backend: SatBackend;

  beforeAll(async () => {
    backend = await KissatBackend.create();
  });

  test("every numbered JSON puzzle has source and count coverage", () => {
    const catalogIds = PUZZLE_EXAMPLES.map((example) => example.id).filter((id) => id !== "intro");
    const sourceIds = [...PUBLISHED_SOLUTION_LOCKS.map((lock) => lock.id), ...Object.keys(PUBLISHED_SOLUTION_GAPS)];

    expect(new Set(catalogIds)).toEqual(new Set(Object.keys(JSON_SOLUTION_COUNTS)));
    expect(new Set(catalogIds)).toEqual(new Set(sourceIds));
  });

  test("puzzle 31 has the largest modeled JSON search space", () => {
    const [id, count] = Object.entries(JSON_SOLUTION_COUNTS).sort(
      ([leftId, leftCount], [rightId, rightCount]) => rightCount - leftCount || leftId.localeCompare(rightId),
    )[0] as [string, number];

    expect({ id, count }).toEqual({ id: "puzzle-31-no-your-other-left", count: 97 });
  });

  test.each(PUZZLE_SOLUTION_CASES)(
    "$id solution count comes from JSON doc",
    async ({ id, data, expectedCount }) => {
      const doc = validatePuzzleDoc(data);
      const worlds = await buildFromDoc(doc, backend).solveAll();

      expect(worlds, id).toHaveLength(expectedCount);
    },
    SOLUTION_COUNT_TIMEOUT_MS,
  );

  test.each([...PUBLISHED_SOLUTION_LOCKS])(
    "$id includes each Reddit-published solution world",
    async ({ id, source, worlds: expectedWorlds }: PublishedSolutionLock) => {
      const example = EXAMPLES_BY_ID.get(id);
      if (example === undefined) throw new Error(`Missing puzzle example for ${id}`);
      const doc = validatePuzzleDoc(example.data);
      const worlds = await buildFromDoc(doc, backend).solveAll();
      const missingWorlds = expectedWorlds.filter(
        (expectedWorld) => !worlds.some((world) => matchesWorldLock(world, expectedWorld, doc)),
      );

      expect(missingWorlds, `${id} did not include all published worlds from ${source}`).toEqual([]);
    },
    PUBLISHED_WORLD_TIMEOUT_MS,
  );
});

function matchesWorldLock(world: World, expected: PublishedWorldLock, doc: PuzzleDoc): boolean {
  for (const [player, role] of Object.entries(expected.roles ?? {})) {
    if (world.actualRole(player) !== role) return false;
  }

  for (const [player, roles] of Object.entries(expected.roleIn ?? {})) {
    if (!roles.includes(world.actualRole(player))) return false;
  }

  for (const [player, type] of Object.entries(expected.characterTypes ?? {})) {
    const actualRole = world.actualRole(player);
    if (!doc.script.includes(actualRole)) return false;
    if (roleCharacterType(roleByName(actualRole)) !== type) return false;
  }

  for (const { player, timing } of expected.poisoned ?? []) {
    if (!world.isPoisoned(player, timing)) return false;
  }

  for (const player of expected.drunk ?? []) {
    if (!world.isDrunk(player)) return false;
  }

  return true;
}
