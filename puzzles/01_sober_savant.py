from __future__ import annotations

from botc_solver import Alignment, BOTCModel, Character, CharacterType, RoleClaim, forced_role_holders
from botc_solver.predicates import (
    chef_count_is,
    different_alignments,
    drunk_between_two_townsfolk,
    exactly_n_evil,
    sits_next_to_evil,
)


PLAYERS = ["Oscar", "Matt", "Anna", "You", "Tim", "Sula"]
CHARACTERS = (
    Character("Demon", Alignment.EVIL, CharacterType.DEMON),
    Character("Minion", Alignment.EVIL, CharacterType.MINION),
    Character("Drunk", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Investigator", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Knight", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Noble", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Savant", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Seamstress", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Steward", Alignment.GOOD, CharacterType.TOWNSFOLK),
)
CLAIMS = {
    "Oscar": "Investigator",
    "Matt": "Noble",
    "Anna": "Seamstress",
    "You": "Savant",
    "Tim": "Knight",
    "Sula": "Steward",
}


def build_model() -> BOTCModel:
    game = BOTCModel(PLAYERS, characters=CHARACTERS, seating=PLAYERS)

    game.set_character_count("Demon", 1)
    game.set_character_count("Minion", 1)
    game.set_character_count("Drunk", 1)

    game.fix_actual("You", "Savant")
    for player in PLAYERS:
        game.fix_poisoned(player, False)
        game.set_apparent_role(player, CLAIMS[player])

    for player in PLAYERS:
        if player != "You":
            game.add_role_claim(RoleClaim(player, CLAIMS[player]))

    oscar_claim = game.any_of(
        [game.is_minion("Anna"), game.is_minion("Sula")],
        "oscar_claim_anna_or_sula_minion",
    )
    sula_claim = game.is_good("Matt")
    matt_claim = exactly_n_evil(game, ["Tim", "Oscar", "Sula"], 1)
    anna_claim = different_alignments(game, "Oscar", "Sula")
    tim_claim = game.not_(
        game.any_of(
            [game.is_demon("Anna"), game.is_demon("Sula")],
            "anna_or_sula_demon",
        ),
        "neither_anna_nor_sula_demon",
    )

    game.add_truthful_info_claim("Oscar", "Investigator", oscar_claim)
    game.add_truthful_info_claim("Sula", "Steward", sula_claim)
    game.add_truthful_info_claim("Matt", "Noble", matt_claim)
    game.add_truthful_info_claim("Anna", "Seamstress", anna_claim)
    game.add_truthful_info_claim("Tim", "Knight", tim_claim)

    game.add_exactly_one(
        [
            game.role_in_play("Investigator"),
            sits_next_to_evil(game, "You"),
        ]
    )
    game.add_exactly_one(
        [
            chef_count_is(game, 1),
            drunk_between_two_townsfolk(game),
        ]
    )
    game.add_exactly_one(
        [
            game.any_of(
                [game.is_minion("Tim"), game.is_minion("Sula")],
                "tim_or_sula_minion",
            ),
            game.not_(game.role_in_play("Noble"), "noble_not_in_play"),
        ]
    )

    return game


def solve():
    return build_model().solve_all()


def main() -> None:
    worlds = solve()
    print(f"{len(worlds)} satisfying world(s)")
    for index, world in enumerate(worlds, start=1):
        print(f"\nWorld {index}")
        for player in PLAYERS:
            actual = world.actual_role(player)
            apparent = world.apparent.get(player)
            poison_suffix = " poisoned" if world.is_poisoned(player) else ""
            if apparent and apparent != actual:
                print(f"  {player}: {actual} (appears as {apparent}){poison_suffix}")
            else:
                print(f"  {player}: {actual}{poison_suffix}")

    print("\nForced facts")
    for role, holder in forced_role_holders(worlds, ["Demon", "Minion", "Drunk"]).items():
        print(f"  {role}: {holder or 'not forced'}")


if __name__ == "__main__":
    main()
