"""
"Come Fly With Me"
by Not Quite Tangible

https://www.reddit.com/r/BloodOnTheClocktower/comments/1ewxu0r/weekly_puzzle_2_come_fly_with_me/
"""

from __future__ import annotations

from botc_solver import BOTCModel, CharacterType, print_solution
from botc_solver.characters import (
    Balloonist,
    Clockmaker,
    Drunk,
    FortuneTeller,
    FortuneTellerCheck,
    Goblin,
    Investigator,
    Juggler,
    Knight,
    Leviathan,
    Saint,
    Seamstress,
    apply_claims,
    player_names,
    script,
)
from botc_solver.core import role_character_type

PLAYERS = [
    Investigator(name="Sarah", role=Goblin, among=["Matthew", "Fraser"]),
    Juggler(
        name="Matthew",
        guesses={
            "Steph": Knight,
            "Sarah": Leviathan,
            "Anna": Goblin,
            "Sula": Goblin,
            "You": Seamstress,
        },
        correct_count=2,
    ),
    Clockmaker(name="Anna", demon_next_to_minion=True),
    Balloonist(
        name="Sula",
        different_character_type_pairs=[
            ("Tim", "Matthew"),
            ("Matthew", "Steph"),
        ],
    ),
    Seamstress(name="You", aligned=True, among=["Matthew", "Sula"]),
    Knight(name="Steph", no_demon_among=["Tim", "Sula"]),
    FortuneTeller(
        name="Fraser",
        checks=[
            FortuneTellerCheck(left="Sarah", right="Anna", yes=False),
            FortuneTellerCheck(left="You", right="Fraser", yes=False),
            FortuneTellerCheck(left="Steph", right="Sarah", yes=False),
        ],
    ),
    Saint(name="Tim"),
]
PLAYER_NAMES = player_names(PLAYERS)
CHARACTERS = script(
    Leviathan,
    Goblin,
    Drunk,
    Saint,
    Balloonist,
    Clockmaker,
    FortuneTeller,
    Investigator,
    Juggler,
    Knight,
    Seamstress,
)


def build_model() -> BOTCModel:
    game = BOTCModel(PLAYER_NAMES, characters=CHARACTERS, seating=PLAYER_NAMES)

    game.set_character_count(Leviathan, 1)
    game.set_character_count(Goblin, 1)
    game.fix_not_actual("You", Leviathan)
    game.fix_not_actual("You", Goblin)

    for player in PLAYER_NAMES:
        game.fix_poisoned(player, False)

    outsider_count = sum(
        game.actual_is(player, role)
        for player in PLAYER_NAMES
        for role, character in game.characters.items()
        if role_character_type(character) == CharacterType.OUTSIDER
    )
    balloonist_in_play = game.role_in_play(Balloonist)
    game.add_enforced(outsider_count == 1, balloonist_in_play.Not())
    game.add_enforced(outsider_count >= 1, balloonist_in_play)
    game.add_enforced(outsider_count <= 2, balloonist_in_play)

    apply_claims(game, PLAYERS)

    return game


def solve():
    return build_model().solve_all()


def main() -> None:
    print_solution(
        solve(),
        PLAYER_NAMES,
        forced_roles=[Goblin, Leviathan, Drunk],
        forced_missing="not in every world",
    )


if __name__ == "__main__":
    main()
