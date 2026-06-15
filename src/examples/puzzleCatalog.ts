import puzzleIntro from "./puzzle-intro-chef-empath.json";
import doc_01_sober_savant from "./puzzle-01-sober-savant.json";
import doc_02_come_fly_with_me from "./puzzle-02-come-fly-with-me.json";
import doc_03a_not_throwing_away_my_shot from "./puzzle-03a-not-throwing-away-my-shot.json";
import doc_03b_not_throwing_away_my_shot from "./puzzle-03b-not-throwing-away-my-shot.json";
import doc_04_the_many_headed_monster from "./puzzle-04-the-many-headed-monster.json";
import doc_05a_you_only_guess_twice from "./puzzle-05a-you-only-guess-twice.json";
import doc_05b_you_only_guess_twice from "./puzzle-05b-you-only-guess-twice.json";
import doc_06_super_marionette_bros from "./puzzle-06-super-marionette-bros.json";
import doc_07_the_savant_strikes_back from "./puzzle-07-the-savant-strikes-back.json";
import doc_08_the_stitch_up from "./puzzle-08-the-stitch-up.json";
import doc_09_the_new_acrobat from "./puzzle-09-the-new-acrobat.json";
import doc_10_dont_overcook_it from "./puzzle-10-dont-overcook-it.json";
import doc_11_false_is_the_new_black from "./puzzle-11-false-is-the-new-black.json";
import doc_12a_thunderstruck from "./puzzle-12a-thunderstruck.json";
import doc_12b_thunderstruck from "./puzzle-12b-thunderstruck.json";
import doc_13_clockblocking from "./puzzle-13-clockblocking.json";
import doc_14_new_super_marionette_bros from "./puzzle-14-new-super-marionette-bros.json";
import doc_15_wake_up_and_choose_violets from "./puzzle-15-wake-up-and-choose-violets.json";
import doc_16_who_watches_the_watchmen from "./puzzle-16-who-watches-the-watchmen.json";
import doc_17_the_missing_piece from "./puzzle-17-the-missing-piece.json";
import doc_18_x_and_the_city from "./puzzle-18-x-and-the-city.json";
import doc_19_he_could_be_you_he_could_be_me from "./puzzle-19-he-could-be-you-he-could-be-me.json";
import doc_20_the_three_wise_men from "./puzzle-20-the-three-wise-men.json";
import doc_21_eight_jugglers_juggling from "./puzzle-21-eight-jugglers-juggling.json";
import doc_22_one_in_the_chamber from "./puzzle-22-one-in-the-chamber.json";
import doc_23_goblincore from "./puzzle-23-goblincore.json";
import doc_24_the_ultimate_blunder from "./puzzle-24-the-ultimate-blunder.json";
import doc_26_a_major_problem from "./puzzle-26-a-major-problem.json";
import doc_27_is_this_a_legion_game from "./puzzle-27-is-this-a-legion-game.json";
import doc_28_a_study_in_scarlet from "./puzzle-28-a-study-in-scarlet.json";
import doc_29_a_dreamer_im_not_the_only_one from "./puzzle-29-a-dreamer-im-not-the-only-one.json";
import doc_30_the_babel_fish_is_a_dead_giveaway_left from "./puzzle-30-the-babel-fish-is-a-dead-giveaway-left.json";
import doc_30_the_babel_fish_is_a_dead_giveaway_right from "./puzzle-30-the-babel-fish-is-a-dead-giveaway-right.json";
import doc_31_no_your_other_left from "./puzzle-31-no-your-other-left.json";
import doc_32_prepare_for_juggle_and_make_it_double from "./puzzle-32-prepare-for-juggle-and-make-it-double.json";
import doc_33_twice_is_coincidence_thrice_is_proof from "./puzzle-33-twice-is-coincidence-thrice-is-proof.json";
import doc_34_the_vortox_conjecture from "./puzzle-34-the-vortox-conjecture.json";
import doc_35_typhon_season from "./puzzle-35-typhon-season.json";
import doc_36_what_is_your_weapon_of_choice from "./puzzle-36-what-is-your-weapon-of-choice.json";
import doc_37_new_super_marionette_bros_u from "./puzzle-37-new-super-marionette-bros-u.json";
import doc_38_snakes_on_a_plane from "./puzzle-38-snakes-on-a-plane.json";
import doc_39_squid_game from "./puzzle-39-squid-game.json";
import doc_40_nine_lives from "./puzzle-40-nine-lives.json";

export interface PuzzleExample {
  readonly id: string;
  readonly label: string;
  readonly data: unknown;
}

function titleOf(data: unknown): string | undefined {
  return typeof data === "object" &&
    data !== null &&
    "title" in data &&
    typeof (data as { readonly title?: unknown }).title === "string"
    ? (data as { readonly title: string }).title
    : undefined;
}

const PUZZLE_DOCS = [
  { id: "puzzle-01-sober-savant", data: doc_01_sober_savant },
  { id: "puzzle-02-come-fly-with-me", data: doc_02_come_fly_with_me },
  { id: "puzzle-03a-not-throwing-away-my-shot", data: doc_03a_not_throwing_away_my_shot },
  { id: "puzzle-03b-not-throwing-away-my-shot", data: doc_03b_not_throwing_away_my_shot },
  { id: "puzzle-04-the-many-headed-monster", data: doc_04_the_many_headed_monster },
  { id: "puzzle-05a-you-only-guess-twice", data: doc_05a_you_only_guess_twice },
  { id: "puzzle-05b-you-only-guess-twice", data: doc_05b_you_only_guess_twice },
  { id: "puzzle-06-super-marionette-bros", data: doc_06_super_marionette_bros },
  { id: "puzzle-07-the-savant-strikes-back", data: doc_07_the_savant_strikes_back },
  { id: "puzzle-08-the-stitch-up", data: doc_08_the_stitch_up },
  { id: "puzzle-09-the-new-acrobat", data: doc_09_the_new_acrobat },
  { id: "puzzle-10-dont-overcook-it", data: doc_10_dont_overcook_it },
  { id: "puzzle-11-false-is-the-new-black", data: doc_11_false_is_the_new_black },
  { id: "puzzle-12a-thunderstruck", data: doc_12a_thunderstruck },
  { id: "puzzle-12b-thunderstruck", data: doc_12b_thunderstruck },
  { id: "puzzle-13-clockblocking", data: doc_13_clockblocking },
  { id: "puzzle-14-new-super-marionette-bros", data: doc_14_new_super_marionette_bros },
  { id: "puzzle-15-wake-up-and-choose-violets", data: doc_15_wake_up_and_choose_violets },
  { id: "puzzle-16-who-watches-the-watchmen", data: doc_16_who_watches_the_watchmen },
  { id: "puzzle-17-the-missing-piece", data: doc_17_the_missing_piece },
  { id: "puzzle-18-x-and-the-city", data: doc_18_x_and_the_city },
  { id: "puzzle-19-he-could-be-you-he-could-be-me", data: doc_19_he_could_be_you_he_could_be_me },
  { id: "puzzle-20-the-three-wise-men", data: doc_20_the_three_wise_men },
  { id: "puzzle-21-eight-jugglers-juggling", data: doc_21_eight_jugglers_juggling },
  { id: "puzzle-22-one-in-the-chamber", data: doc_22_one_in_the_chamber },
  { id: "puzzle-23-goblincore", data: doc_23_goblincore },
  { id: "puzzle-24-the-ultimate-blunder", data: doc_24_the_ultimate_blunder },
  { id: "puzzle-26-a-major-problem", data: doc_26_a_major_problem },
  { id: "puzzle-27-is-this-a-legion-game", data: doc_27_is_this_a_legion_game },
  { id: "puzzle-28-a-study-in-scarlet", data: doc_28_a_study_in_scarlet },
  { id: "puzzle-29-a-dreamer-im-not-the-only-one", data: doc_29_a_dreamer_im_not_the_only_one },
  { id: "puzzle-30-the-babel-fish-is-a-dead-giveaway-left", data: doc_30_the_babel_fish_is_a_dead_giveaway_left },
  { id: "puzzle-30-the-babel-fish-is-a-dead-giveaway-right", data: doc_30_the_babel_fish_is_a_dead_giveaway_right },
  { id: "puzzle-31-no-your-other-left", data: doc_31_no_your_other_left },
  { id: "puzzle-32-prepare-for-juggle-and-make-it-double", data: doc_32_prepare_for_juggle_and_make_it_double },
  { id: "puzzle-33-twice-is-coincidence-thrice-is-proof", data: doc_33_twice_is_coincidence_thrice_is_proof },
  { id: "puzzle-34-the-vortox-conjecture", data: doc_34_the_vortox_conjecture },
  { id: "puzzle-35-typhon-season", data: doc_35_typhon_season },
  { id: "puzzle-36-what-is-your-weapon-of-choice", data: doc_36_what_is_your_weapon_of_choice },
  { id: "puzzle-37-new-super-marionette-bros-u", data: doc_37_new_super_marionette_bros_u },
  { id: "puzzle-38-snakes-on-a-plane", data: doc_38_snakes_on_a_plane },
  { id: "puzzle-39-squid-game", data: doc_39_squid_game },
  { id: "puzzle-40-nine-lives", data: doc_40_nine_lives },
] as const;

export const PUZZLE_EXAMPLES: readonly PuzzleExample[] = [
  { id: "intro", label: titleOf(puzzleIntro) ?? "Intro - Chef + Empath", data: puzzleIntro },
  ...PUZZLE_DOCS.map(({ id, data }) => ({ id, label: titleOf(data) ?? id, data })),
];
