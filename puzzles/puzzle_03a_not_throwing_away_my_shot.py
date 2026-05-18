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
from botc_solver.predicates import chef_count_registers_as


PLAYERS = ["Sula", "Matthew", "Oscar", "Josh", "You", "Aoife", "Tom"]
MINION_ROLES = ("Baron", "Spy", "Poisoner", "Scarlet Woman")
EVIL_ROLES = ("Imp", *MINION_ROLES)
CHARACTERS = (
    Character("Imp", Alignment.EVIL, CharacterType.DEMON),
    Character("Baron", Alignment.EVIL, CharacterType.MINION),
    Character("Spy", Alignment.EVIL, CharacterType.MINION),
    Character("Poisoner", Alignment.EVIL, CharacterType.MINION),
    Character("Scarlet Woman", Alignment.EVIL, CharacterType.MINION),
    Character("Drunk", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Recluse", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Chef", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Empath", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Investigator", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Librarian", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Slayer", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Washerwoman", Alignment.GOOD, CharacterType.TOWNSFOLK),
)
CLAIMS = {
    "Sula": "Investigator",
    "Matthew": "Washerwoman",
    "Oscar": "Librarian",
    "Josh": "Empath",
    "You": "Slayer",
    "Aoife": "Chef",
    "Tom": "Recluse",
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
    game.add_enforced(outsider_count == 2, baron_in_play)
    game.add_enforced(outsider_count == 0, baron_in_play.Not())

    game.add_poisoner_effect(POISON_CONTEXT)

    sula_claim = game.any_of(
        [
            game.registers_as_role("You", "Baron", "sula_investigator"),
            game.registers_as_role("Aoife", "Baron", "sula_investigator"),
        ],
        "sula_claim_you_or_aoife_baron",
    )
    matthew_claim = game.any_of(
        [
            game.registers_as_role("Aoife", "Librarian", "matthew_washerwoman"),
            game.registers_as_role("Oscar", "Librarian", "matthew_washerwoman"),
        ],
        "matthew_claim_aoife_or_oscar_librarian",
    )
    oscar_claim = game.bool_sum_equals(
        [
            game.registers_as_character_type(player, CharacterType.OUTSIDER, "oscar_librarian")
            for player in PLAYERS
        ],
        0,
        "oscar_claim_no_outsiders",
    )
    josh_claim = game.not_(
        game.any_of(
            [
                game.registers_as_evil("You", "josh_empath"),
                game.registers_as_evil("Oscar", "josh_empath"),
            ],
            "you_or_oscar_evil",
        ),
        "neither_you_nor_oscar_evil",
    )
    aoife_claim = chef_count_registers_as(game, 0, "aoife_chef")

    game.add_truthful_info_claim("Sula", "Investigator", sula_claim, poison_context=POISON_CONTEXT)
    game.add_truthful_info_claim(
        "Matthew",
        "Washerwoman",
        matthew_claim,
        poison_context=POISON_CONTEXT,
    )
    game.add_truthful_info_claim("Oscar", "Librarian", oscar_claim, poison_context=POISON_CONTEXT)
    game.add_truthful_info_claim("Josh", "Empath", josh_claim, poison_context=POISON_CONTEXT)
    game.add_truthful_info_claim("Aoife", "Chef", aoife_claim, poison_context=POISON_CONTEXT)

    game.add_truth(game.actual_is("You", "Slayer"))
    game.add_false(game.poisoned("You", POISON_CONTEXT))
    tom_imp_with_scarlet_woman = game.all_of(
        [game.actual_is("Tom", "Imp"), game.role_in_play("Scarlet Woman")],
        "tom_imp_with_scarlet_woman",
    )
    tom_recluse_registers_as_imp = game.all_of(
        [
            game.actual_is("Tom", "Recluse"),
            game.registers_as_role("Tom", "Imp", "you_slayer"),
        ],
        "tom_recluse_registers_as_imp",
    )
    game.add_truth(
        game.any_of(
            [tom_recluse_registers_as_imp, tom_imp_with_scarlet_woman],
            "slayer_shot_tom_died_without_game_ending",
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
