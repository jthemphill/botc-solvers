'''
"Come Fly With Me"
by Not Quite Tangible

https://www.reddit.com/r/BloodOnTheClocktower/comments/1ewxu0r/weekly_puzzle_2_come_fly_with_me/
'''

from __future__ import annotations

from botc_solver import BOTCModel, CharacterType, RoleClaim, print_solution
from botc_solver.characters import (
    BALLOONIST,
    CLOCKMAKER,
    DRUNK,
    FORTUNE_TELLER,
    GOBLIN,
    INVESTIGATOR,
    JUGGLER,
    KNIGHT,
    LEVIATHAN,
    SAINT,
    SEAMSTRESS,
    script,
)
from botc_solver.predicates import (
    different_character_types,
    registers_as_role_among,
    same_alignment,
)


PLAYERS = ["Sarah", "Matthew", "Anna", "Sula", "You", "Steph", "Fraser", "Tim"]
CHARACTERS = script(
    LEVIATHAN,
    GOBLIN,
    DRUNK,
    SAINT,
    BALLOONIST,
    CLOCKMAKER,
    FORTUNE_TELLER,
    INVESTIGATOR,
    JUGGLER,
    KNIGHT,
    SEAMSTRESS,
)
CLAIMS = {
    "Sarah": "Investigator",
    "Matthew": "Juggler",
    "Anna": "Clockmaker",
    "Sula": "Balloonist",
    "You": "Seamstress",
    "Steph": "Knight",
    "Fraser": "Fortune Teller",
    "Tim": "Saint",
}


def build_model() -> BOTCModel:
    game = BOTCModel(PLAYERS, characters=CHARACTERS, seating=PLAYERS)

    game.set_character_count("Leviathan", 1)
    game.set_character_count("Goblin", 1)
    game.fix_not_actual("You", "Leviathan")
    game.fix_not_actual("You", "Goblin")

    for player in PLAYERS:
        game.fix_poisoned(player, False)
        game.add_role_claim(RoleClaim(player, CLAIMS[player]), drunk_role="Drunk")

    outsider_count = sum(
        game.actual_is(player, role)
        for player in PLAYERS
        for role, character in game.characters.items()
        if character.character_type == CharacterType.OUTSIDER
    )
    balloonist_in_play = game.role_in_play("Balloonist")
    game.add_enforced(outsider_count == 1, balloonist_in_play.Not())
    game.add_enforced(outsider_count >= 1, balloonist_in_play)
    game.add_enforced(outsider_count <= 2, balloonist_in_play)

    sarah_claim = registers_as_role_among(
        game,
        ["Matthew", "Fraser"],
        "Goblin",
        "sarah_investigator",
    )
    matthew_claim = game.bool_sum_equals(
        [
            game.actual_is("Steph", "Knight"),
            game.actual_is("Sarah", "Leviathan"),
            game.actual_is("Anna", "Goblin"),
            game.actual_is("Sula", "Goblin"),
            game.actual_is("You", "Seamstress"),
        ],
        2,
        "matthew_juggler_two_correct",
    )
    anna_claim = game.any_of(
        [
            game.all_of(
                [game.is_demon(left), game.is_minion(right)],
                f"{left}_{right}_demon_minion_neighbors",
            )
            for left, right in game.adjacent_pairs()
        ]
        + [
            game.all_of(
                [game.is_minion(left), game.is_demon(right)],
                f"{left}_{right}_minion_demon_neighbors",
            )
            for left, right in game.adjacent_pairs()
        ],
        "clockmaker_demon_next_to_minion",
    )
    sula_claim = game.all_of(
        [
            different_character_types(game, "Tim", "Matthew"),
            different_character_types(game, "Matthew", "Steph"),
        ],
        "sula_balloonist_two_type_statements",
    )
    you_claim = same_alignment(game, "Matthew", "Sula")
    steph_claim = game.not_(
        game.any_of(
            [game.actual_is("Tim", "Leviathan"), game.actual_is("Sula", "Leviathan")],
            "tim_or_sula_leviathan",
        ),
        "neither_tim_nor_sula_leviathan",
    )
    fraser_claim = game.all_of(
        [
            game.not_(
                game.any_of([game.is_demon("Sarah"), game.is_demon("Anna")], "sarah_or_anna_demon"),
                "fortune_teller_sarah_anna_no",
            ),
            game.not_(
                game.any_of([game.is_demon("You"), game.is_demon("Fraser")], "you_or_fraser_demon"),
                "fortune_teller_you_fraser_no",
            ),
            game.not_(
                game.any_of([game.is_demon("Steph"), game.is_demon("Sarah")], "steph_or_sarah_demon"),
                "fortune_teller_steph_sarah_no",
            ),
        ],
        "fraser_fortune_teller_all_no",
    )

    game.add_truthful_info_claim("Sarah", "Investigator", sarah_claim)
    game.add_truthful_info_claim("Matthew", "Juggler", matthew_claim)
    game.add_truthful_info_claim("Anna", "Clockmaker", anna_claim)
    game.add_truthful_info_claim("Sula", "Balloonist", sula_claim)
    game.add_truthful_info_claim("You", "Seamstress", you_claim)
    game.add_truthful_info_claim("Steph", "Knight", steph_claim)
    game.add_truthful_info_claim("Fraser", "Fortune Teller", fraser_claim)

    return game


def solve():
    return build_model().solve_all()


def main() -> None:
    print_solution(
        solve(),
        PLAYERS,
        forced_roles=["Goblin", "Leviathan", "Drunk"],
        forced_missing="not in every world",
    )


if __name__ == "__main__":
    main()
