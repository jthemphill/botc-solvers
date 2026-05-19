'''
"Can the sober Savant solve the puzzle?"
by Not Quite Tangible

https://www.reddit.com/r/BloodOnTheClocktower/comments/1erb5e2/can_the_sober_savant_solve_the_puzzle/
'''

from __future__ import annotations

from botc_solver import BOTCModel, print_solution
from botc_solver.characters import (
    Chef,
    Drunk,
    Imp,
    Investigator,
    Knight,
    Noble,
    Savant,
    ScarletWoman,
    Seamstress,
    Steward,
    apply_claims,
    player_names,
    script,
)
from botc_solver.predicates import (
    drunk_between_two_townsfolk,
)


PLAYERS = [
    Investigator(
        name="Oscar",
        minion_role=ScarletWoman,
        among=["Anna", "Sula"],
    ),
    Noble(
        name="Matt",
        one_evil_among=["Tim", "Oscar", "Sula"],
    ),
    Seamstress(
        name="Anna",
        aligned=False,
        among=["Oscar", "Sula"],
    ),
    Savant(
        name="You",
        statements=[
            lambda game: (
                game.role_in_play(Investigator),
                game.sits_next_to_evil("You"),
            ),
            lambda game: (
                Chef.learns_count(game, 1, "you_savant_chef", registers=False),
                drunk_between_two_townsfolk(game),
            ),
            lambda game: (
                game.any_of(
                    [game.is_minion("Tim"), game.is_minion("Sula")],
                    "tim_or_sula_minion",
                ),
                game.not_(game.role_in_play(Noble), "noble_not_in_play"),
            ),
        ],
    ),
    Knight(
        name="Tim",
        no_demon_among=["Anna", "Sula"],
    ),
    Steward(
        name="Sula",
        good_player="Matt",
    ),
]
PLAYER_NAMES = player_names(PLAYERS)
CHARACTERS = script(
    Imp,
    ScarletWoman,
    Drunk,
    Investigator,
    Knight,
    Noble,
    Savant,
    Seamstress,
    Steward,
)


def build_model() -> BOTCModel:
    game = BOTCModel(PLAYER_NAMES, characters=CHARACTERS, seating=PLAYER_NAMES)

    game.set_character_count(Imp, 1)
    game.set_character_count(ScarletWoman, 1)
    game.set_character_count(Drunk, 1)

    game.fix_actual("You", Savant)
    apply_claims(game, PLAYERS)

    return game


def solve():
    return build_model().solve_all()


def main() -> None:
    print_solution(solve(), PLAYER_NAMES, forced_roles=[Imp, ScarletWoman, Drunk])


if __name__ == "__main__":
    main()
