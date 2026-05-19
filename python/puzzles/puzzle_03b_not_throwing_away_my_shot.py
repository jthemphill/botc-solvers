"""
"Not Throwing Away My Shot" (part b)
by Not Quite Tangible

https://www.reddit.com/r/BloodOnTheClocktower/comments/1f2jht3/weekly_puzzle_3a_3b_not_throwing_away_my_shot/
"""

from __future__ import annotations

from botc_solver import BOTCModel, CharacterType, forced_role, print_solution
from botc_solver.characters import (
    Baron,
    Chef,
    Drunk,
    Empath,
    Imp,
    Investigator,
    Librarian,
    Poisoner,
    Recluse,
    Saint,
    ScarletWoman,
    Slayer,
    Spy,
    Washerwoman,
    apply_claims,
    player_names,
    role_names,
    script,
)

PLAYERS = [
    Chef(name="Dan", count=0),
    Recluse(name="Anna"),
    Washerwoman(name="Matt", role=Librarian, among=["Tim", "Dan"]),
    Empath(name="Fraser", count=0),
    Slayer(name="You"),
    Librarian(name="Tim", role=Drunk, among=["You", "Hannah"]),
    Investigator(name="Sarah", role=ScarletWoman, among=["Tim", "Fraser"]),
    Saint(name="Hannah"),
]
PLAYER_NAMES = player_names(PLAYERS)
CHARACTERS = script(
    Imp,
    Baron,
    Spy,
    Poisoner,
    ScarletWoman,
    Drunk,
    Recluse,
    Saint,
    Chef,
    Empath,
    Investigator,
    Librarian,
    Slayer,
    Washerwoman,
)
MINION_ROLES = role_names(CHARACTERS, character_type=CharacterType.MINION)
POISON_CONTEXT = "day_1"


def _outsider_count(game: BOTCModel):
    return sum(
        game.has_character_type(player, CharacterType.OUTSIDER)
        for player in PLAYER_NAMES
    )


def build_model() -> BOTCModel:
    game = BOTCModel(PLAYER_NAMES, characters=CHARACTERS, seating=PLAYER_NAMES)

    game.set_character_count(Imp, 1)
    game.model.add(sum(game.is_minion(player) for player in PLAYER_NAMES) == 1)
    game.add_false(game.is_evil("You"))

    outsider_count = _outsider_count(game)
    baron_in_play = game.role_in_play(Baron)
    game.add_enforced(outsider_count == 3, baron_in_play)
    game.add_enforced(outsider_count == 1, baron_in_play.Not())

    game.add_poisoner_effect(POISON_CONTEXT)

    apply_claims(game, PLAYERS, poison_context=POISON_CONTEXT)

    game.add_truth(game.actual_is("You", Slayer))
    game.add_false(game.poisoned("You", POISON_CONTEXT))
    anna_imp_with_scarlet_woman = game.all_of(
        [game.actual_is("Anna", Imp), game.role_in_play(ScarletWoman)],
        "anna_imp_with_scarlet_woman",
    )
    anna_recluse_registers_as_imp = game.all_of(
        [
            game.actual_is("Anna", Recluse),
            game.registers_as_role("Anna", Imp, "you_slayer"),
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
        PLAYER_NAMES,
        poison_context=POISON_CONTEXT,
        forced_roles=[
            forced_role("Demon", Imp, include_role=True),
            forced_role("Minion", MINION_ROLES, include_role=True),
            forced_role("Drunk", Drunk, missing="not in play"),
            forced_role("Recluse", Recluse, missing="not in play"),
        ],
    )


if __name__ == "__main__":
    main()
