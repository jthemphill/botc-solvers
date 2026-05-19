'''
"Not Throwing Away My Shot" (part b)
by Not Quite Tangible

https://www.reddit.com/r/BloodOnTheClocktower/comments/1f2jht3/weekly_puzzle_3a_3b_not_throwing_away_my_shot/
'''

from __future__ import annotations

from botc_solver import (
    Alignment,
    BOTCModel,
    Character,
    CharacterType,
    RoleClaim,
    forced_role,
    print_solution,
)
from botc_solver.predicates import chef_count_registers_as, registers_as_role_among


PLAYERS = ["Dan", "Anna", "Matt", "Fraser", "You", "Tim", "Sarah", "Hannah"]
CHARACTERS = (
    Character("Imp", Alignment.EVIL, CharacterType.DEMON),
    Character("Baron", Alignment.EVIL, CharacterType.MINION),
    Character("Spy", Alignment.EVIL, CharacterType.MINION),
    Character("Poisoner", Alignment.EVIL, CharacterType.MINION),
    Character("Scarlet Woman", Alignment.EVIL, CharacterType.MINION),
    Character("Drunk", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Recluse", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Saint", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Chef", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Empath", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Investigator", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Librarian", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Slayer", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Washerwoman", Alignment.GOOD, CharacterType.TOWNSFOLK),
)
MINION_ROLES = tuple(
    character.name for character in CHARACTERS if character.character_type == CharacterType.MINION
)
EVIL_ROLES = [character.name for character in CHARACTERS if character.alignment == Alignment.EVIL]
CLAIMS = {
    "Dan": "Chef",
    "Anna": "Recluse",
    "Matt": "Washerwoman",
    "Fraser": "Empath",
    "You": "Slayer",
    "Tim": "Librarian",
    "Sarah": "Investigator",
    "Hannah": "Saint",
}
POISON_CONTEXT = "day_1"


def _outsider_count(game: BOTCModel):
    return sum(game.has_character_type(player, CharacterType.OUTSIDER) for player in PLAYERS)


def build_model() -> BOTCModel:
    game = BOTCModel(PLAYERS, characters=CHARACTERS, seating=PLAYERS)

    game.set_character_count("Imp", 1)
    game.model.add(sum(game.is_minion(player) for player in PLAYERS) == 1)
    game.add_false(game.is_evil("You"))

    for player in PLAYERS:
        game.add_role_claim(
            RoleClaim(player, CLAIMS[player]),
            evil_roles=EVIL_ROLES,
            drunk_role="Drunk",
        )

    outsider_count = _outsider_count(game)
    baron_in_play = game.role_in_play("Baron")
    game.add_enforced(outsider_count == 3, baron_in_play)
    game.add_enforced(outsider_count == 1, baron_in_play.Not())

    game.add_poisoner_effect(POISON_CONTEXT)

    dan_claim = chef_count_registers_as(game, 0, "dan_chef")
    matt_claim = registers_as_role_among(game, ["Tim", "Dan"], "Librarian", "matt_washerwoman")
    fraser_claim = game.not_(
        game.any_of(
            [
                game.registers_as_evil("You", "fraser_empath"),
                game.registers_as_evil("Matt", "fraser_empath"),
            ],
            "you_or_matt_evil",
        ),
        "neither_you_nor_matt_evil",
    )
    tim_claim = registers_as_role_among(game, ["You", "Hannah"], "Drunk", "tim_librarian")
    sarah_claim = registers_as_role_among(
        game,
        ["Tim", "Fraser"],
        "Scarlet Woman",
        "sarah_investigator",
    )

    game.add_truthful_info_claim("Dan", "Chef", dan_claim, poison_context=POISON_CONTEXT)
    game.add_truthful_info_claim("Matt", "Washerwoman", matt_claim, poison_context=POISON_CONTEXT)
    game.add_truthful_info_claim("Fraser", "Empath", fraser_claim, poison_context=POISON_CONTEXT)
    game.add_truthful_info_claim("Tim", "Librarian", tim_claim, poison_context=POISON_CONTEXT)
    game.add_truthful_info_claim("Sarah", "Investigator", sarah_claim, poison_context=POISON_CONTEXT)

    game.add_truth(game.actual_is("You", "Slayer"))
    game.add_false(game.poisoned("You", POISON_CONTEXT))
    anna_imp_with_scarlet_woman = game.all_of(
        [game.actual_is("Anna", "Imp"), game.role_in_play("Scarlet Woman")],
        "anna_imp_with_scarlet_woman",
    )
    anna_recluse_registers_as_imp = game.all_of(
        [
            game.actual_is("Anna", "Recluse"),
            game.registers_as_role("Anna", "Imp", "you_slayer"),
        ],
        "anna_recluse_registers_as_imp",
    )
    game.add_truth(
        game.any_of(
            [anna_recluse_registers_as_imp, anna_imp_with_scarlet_woman],
            "slayer_shot_anna_died_without_game_ending",
        )
    )

    return game


def solve():
    return build_model().solve_all()


def main() -> None:
    print_solution(
        solve(),
        PLAYERS,
        poison_context=POISON_CONTEXT,
        forced_roles=[
            forced_role("Demon", "Imp", include_role=True),
            forced_role("Minion", MINION_ROLES, include_role=True),
            forced_role("Drunk", missing="not in play"),
            forced_role("Recluse", missing="not in play"),
        ],
    )


if __name__ == "__main__":
    main()
