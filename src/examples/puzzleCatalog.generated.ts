import doc_puzzle_02_come_fly_with_me from "./generated/puzzle-02-come-fly-with-me.json";
import doc_puzzle_03a_not_throwing_away_my_shot from "./generated/puzzle-03a-not-throwing-away-my-shot.json";
import doc_puzzle_03b_not_throwing_away_my_shot from "./generated/puzzle-03b-not-throwing-away-my-shot.json";
import doc_puzzle_04_the_many_headed_monster from "./generated/puzzle-04-the-many-headed-monster.json";
import doc_puzzle_06_super_marionette_bros from "./generated/puzzle-06-super-marionette-bros.json";
import doc_puzzle_07_the_savant_strikes_back from "./generated/puzzle-07-the-savant-strikes-back.json";
import doc_puzzle_08_the_stitch_up from "./generated/puzzle-08-the-stitch-up.json";
import doc_puzzle_09_the_new_acrobat from "./generated/puzzle-09-the-new-acrobat.json";
import doc_puzzle_10_dont_overcook_it from "./generated/puzzle-10-dont-overcook-it.json";
import doc_puzzle_11_false_is_the_new_black from "./generated/puzzle-11-false-is-the-new-black.json";
import doc_puzzle_12a_thunderstruck from "./generated/puzzle-12a-thunderstruck.json";
import doc_puzzle_12b_thunderstruck from "./generated/puzzle-12b-thunderstruck.json";
import doc_puzzle_13_clockblocking from "./generated/puzzle-13-clockblocking.json";
import doc_puzzle_14_new_super_marionette_bros from "./generated/puzzle-14-new-super-marionette-bros.json";
import doc_puzzle_15_wake_up_and_choose_violets from "./generated/puzzle-15-wake-up-and-choose-violets.json";
import doc_puzzle_16_who_watches_the_watchmen from "./generated/puzzle-16-who-watches-the-watchmen.json";
import doc_puzzle_17_the_missing_piece from "./generated/puzzle-17-the-missing-piece.json";
import doc_puzzle_18_x_and_the_city from "./generated/puzzle-18-x-and-the-city.json";
import doc_puzzle_19_he_could_be_you_he_could_be_me from "./generated/puzzle-19-he-could-be-you-he-could-be-me.json";
import doc_puzzle_20_the_three_wise_men from "./generated/puzzle-20-the-three-wise-men.json";
import doc_puzzle_21_eight_jugglers_juggling from "./generated/puzzle-21-eight-jugglers-juggling.json";
import doc_puzzle_22_one_in_the_chamber from "./generated/puzzle-22-one-in-the-chamber.json";
import doc_puzzle_23_goblincore from "./generated/puzzle-23-goblincore.json";
import doc_puzzle_24_the_ultimate_blunder from "./generated/puzzle-24-the-ultimate-blunder.json";
import doc_puzzle_26_a_major_problem from "./generated/puzzle-26-a-major-problem.json";
import doc_puzzle_27_is_this_a_legion_game from "./generated/puzzle-27-is-this-a-legion-game.json";
import doc_puzzle_28_a_study_in_scarlet from "./generated/puzzle-28-a-study-in-scarlet.json";
import doc_puzzle_29_a_dreamer_im_not_the_only_one from "./generated/puzzle-29-a-dreamer-im-not-the-only-one.json";
import doc_puzzle_30_the_babel_fish_is_a_dead_giveaway_left from "./generated/puzzle-30-the-babel-fish-is-a-dead-giveaway-left.json";
import doc_puzzle_30_the_babel_fish_is_a_dead_giveaway_right from "./generated/puzzle-30-the-babel-fish-is-a-dead-giveaway-right.json";
import doc_puzzle_31_no_your_other_left from "./generated/puzzle-31-no-your-other-left.json";
import doc_puzzle_32_prepare_for_juggle_and_make_it_double from "./generated/puzzle-32-prepare-for-juggle-and-make-it-double.json";
import doc_puzzle_33_twice_is_coincidence_thrice_is_proof from "./generated/puzzle-33-twice-is-coincidence-thrice-is-proof.json";
import doc_puzzle_35_typhon_season from "./generated/puzzle-35-typhon-season.json";
import doc_puzzle_36_what_is_your_weapon_of_choice from "./generated/puzzle-36-what-is-your-weapon-of-choice.json";
import doc_puzzle_37_new_super_marionette_bros_u from "./generated/puzzle-37-new-super-marionette-bros-u.json";
import doc_puzzle_38_snakes_on_a_plane from "./generated/puzzle-38-snakes-on-a-plane.json";
import doc_puzzle_39_squid_game from "./generated/puzzle-39-squid-game.json";
import doc_puzzle_40_nine_lives from "./generated/puzzle-40-nine-lives.json";

export interface GeneratedPuzzleCatalogEntry {
  readonly id: string;
  readonly label: string;
  readonly data?: unknown;
}

export const GENERATED_PUZZLE_CATALOG = [
  {
    id: "puzzle-01-sober-savant",
    label: "Puzzle 1 - Sober Savant",
  },
  {
    id: "puzzle-02-come-fly-with-me",
    label: "Puzzle 2 - Come Fly With Me",
    data: doc_puzzle_02_come_fly_with_me,
  },
  {
    id: "puzzle-03a-not-throwing-away-my-shot",
    label: "Puzzle 3a - Not Throwing Away My Shot",
    data: doc_puzzle_03a_not_throwing_away_my_shot,
  },
  {
    id: "puzzle-03b-not-throwing-away-my-shot",
    label: "Puzzle 3b - Not Throwing Away My Shot",
    data: doc_puzzle_03b_not_throwing_away_my_shot,
  },
  {
    id: "puzzle-04-the-many-headed-monster",
    label: "Puzzle 4 - The Many Headed Monster",
    data: doc_puzzle_04_the_many_headed_monster,
  },
  {
    id: "puzzle-05a-you-only-guess-twice",
    label: "Puzzle 5a - You Only Guess Twice",
  },
  {
    id: "puzzle-05b-you-only-guess-twice",
    label: "Puzzle 5b - You Only Guess Twice",
  },
  {
    id: "puzzle-06-super-marionette-bros",
    label: "Puzzle 6 - Super Marionette Bros",
    data: doc_puzzle_06_super_marionette_bros,
  },
  {
    id: "puzzle-07-the-savant-strikes-back",
    label: "Puzzle 7 - The Savant Strikes Back",
    data: doc_puzzle_07_the_savant_strikes_back,
  },
  {
    id: "puzzle-08-the-stitch-up",
    label: "Puzzle 8 - The Stitch Up",
    data: doc_puzzle_08_the_stitch_up,
  },
  {
    id: "puzzle-09-the-new-acrobat",
    label: "Puzzle 9 - The New Acrobat",
    data: doc_puzzle_09_the_new_acrobat,
  },
  {
    id: "puzzle-10-dont-overcook-it",
    label: "Puzzle 10 - Dont Overcook It",
    data: doc_puzzle_10_dont_overcook_it,
  },
  {
    id: "puzzle-11-false-is-the-new-black",
    label: "Puzzle 11 - False Is The New Black",
    data: doc_puzzle_11_false_is_the_new_black,
  },
  {
    id: "puzzle-12a-thunderstruck",
    label: "Puzzle 12a - Thunderstruck",
    data: doc_puzzle_12a_thunderstruck,
  },
  {
    id: "puzzle-12b-thunderstruck",
    label: "Puzzle 12b - Thunderstruck",
    data: doc_puzzle_12b_thunderstruck,
  },
  {
    id: "puzzle-13-clockblocking",
    label: "Puzzle 13 - Clockblocking",
    data: doc_puzzle_13_clockblocking,
  },
  {
    id: "puzzle-14-new-super-marionette-bros",
    label: "Puzzle 14 - New Super Marionette Bros",
    data: doc_puzzle_14_new_super_marionette_bros,
  },
  {
    id: "puzzle-15-wake-up-and-choose-violets",
    label: "Puzzle 15 - Wake Up And Choose Violets",
    data: doc_puzzle_15_wake_up_and_choose_violets,
  },
  {
    id: "puzzle-16-who-watches-the-watchmen",
    label: "Puzzle 16 - Who Watches The Watchmen",
    data: doc_puzzle_16_who_watches_the_watchmen,
  },
  {
    id: "puzzle-17-the-missing-piece",
    label: "Puzzle 17 - The Missing Piece",
    data: doc_puzzle_17_the_missing_piece,
  },
  {
    id: "puzzle-18-x-and-the-city",
    label: "Puzzle 18 - X And The City",
    data: doc_puzzle_18_x_and_the_city,
  },
  {
    id: "puzzle-19-he-could-be-you-he-could-be-me",
    label: "Puzzle 19 - He Could Be You He Could Be Me",
    data: doc_puzzle_19_he_could_be_you_he_could_be_me,
  },
  {
    id: "puzzle-20-the-three-wise-men",
    label: "Puzzle 20 - The Three Wise Men",
    data: doc_puzzle_20_the_three_wise_men,
  },
  {
    id: "puzzle-21-eight-jugglers-juggling",
    label: "Puzzle 21 - Eight Jugglers Juggling",
    data: doc_puzzle_21_eight_jugglers_juggling,
  },
  {
    id: "puzzle-22-one-in-the-chamber",
    label: "Puzzle 22 - One In The Chamber",
    data: doc_puzzle_22_one_in_the_chamber,
  },
  {
    id: "puzzle-23-goblincore",
    label: "Puzzle 23 - Goblincore",
    data: doc_puzzle_23_goblincore,
  },
  {
    id: "puzzle-24-the-ultimate-blunder",
    label: "Puzzle 24 - The Ultimate Blunder",
    data: doc_puzzle_24_the_ultimate_blunder,
  },
  {
    id: "puzzle-26-a-major-problem",
    label: "Puzzle 26 - A Major Problem",
    data: doc_puzzle_26_a_major_problem,
  },
  {
    id: "puzzle-27-is-this-a-legion-game",
    label: "Puzzle 27 - Is This A Legion Game",
    data: doc_puzzle_27_is_this_a_legion_game,
  },
  {
    id: "puzzle-28-a-study-in-scarlet",
    label: "Puzzle 28 - A Study In Scarlet",
    data: doc_puzzle_28_a_study_in_scarlet,
  },
  {
    id: "puzzle-29-a-dreamer-im-not-the-only-one",
    label: "Puzzle 29 - A Dreamer Im Not The Only One",
    data: doc_puzzle_29_a_dreamer_im_not_the_only_one,
  },
  {
    id: "puzzle-30-the-babel-fish-is-a-dead-giveaway-left",
    label: "Puzzle 30 - The Babel Fish Is A Dead Giveaway (left game)",
    data: doc_puzzle_30_the_babel_fish_is_a_dead_giveaway_left,
  },
  {
    id: "puzzle-30-the-babel-fish-is-a-dead-giveaway-right",
    label: "Puzzle 30 - The Babel Fish Is A Dead Giveaway (right game)",
    data: doc_puzzle_30_the_babel_fish_is_a_dead_giveaway_right,
  },
  {
    id: "puzzle-31-no-your-other-left",
    label: "Puzzle 31 - No Your Other Left",
    data: doc_puzzle_31_no_your_other_left,
  },
  {
    id: "puzzle-32-prepare-for-juggle-and-make-it-double",
    label: "Puzzle 32 - Prepare For Juggle And Make It Double",
    data: doc_puzzle_32_prepare_for_juggle_and_make_it_double,
  },
  {
    id: "puzzle-33-twice-is-coincidence-thrice-is-proof",
    label: "Puzzle 33 - Twice Is Coincidence Thrice Is Proof",
    data: doc_puzzle_33_twice_is_coincidence_thrice_is_proof,
  },
  {
    id: "puzzle-34-the-vortox-conjecture",
    label: "Puzzle 34 - The Vortox Conjecture",
  },
  {
    id: "puzzle-35-typhon-season",
    label: "Puzzle 35 - Typhon Season",
    data: doc_puzzle_35_typhon_season,
  },
  {
    id: "puzzle-36-what-is-your-weapon-of-choice",
    label: "Puzzle 36 - What Is Your Weapon Of Choice",
    data: doc_puzzle_36_what_is_your_weapon_of_choice,
  },
  {
    id: "puzzle-37-new-super-marionette-bros-u",
    label: "Puzzle 37 - New Super Marionette Bros U",
    data: doc_puzzle_37_new_super_marionette_bros_u,
  },
  {
    id: "puzzle-38-snakes-on-a-plane",
    label: "Puzzle 38 - Snakes On A Plane",
    data: doc_puzzle_38_snakes_on_a_plane,
  },
  {
    id: "puzzle-39-squid-game",
    label: "Puzzle 39 - Squid Game",
    data: doc_puzzle_39_squid_game,
  },
  {
    id: "puzzle-40-nine-lives",
    label: "Puzzle 40 - Nine Lives",
    data: doc_puzzle_40_nine_lives,
  },
] as const satisfies readonly GeneratedPuzzleCatalogEntry[];
