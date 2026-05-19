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


PLAYERS = ["Sarah", "Tim", "Matt", "Hannah", "You", "Anna", "Dan", "Fraser"]
MINION_ROLES = ("Marionette", "Poisoner")
EVIL_ROLES = ("Lord of Typhon", *MINION_ROLES)
CHARACTERS = (
    Character("Lord of Typhon", Alignment.EVIL, CharacterType.DEMON),
    Character("Marionette", Alignment.EVIL, CharacterType.MINION),
    Character("Poisoner", Alignment.EVIL, CharacterType.MINION),
    Character("Drunk", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Recluse", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Investigator", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Librarian", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Fortune Teller", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Juggler", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Dreamer", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Empath", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Undertaker", Alignment.GOOD, CharacterType.TOWNSFOLK),
)
CLAIMS = {
    "Sarah": "Librarian",
    "Tim": "Recluse",
    "Matt": "Juggler",
    "Hannah": "Dreamer",
    "You": "Investigator",
    "Anna": "Empath",
    "Dan": "Undertaker",
    "Fraser": "Fortune Teller",
}

NIGHT_1 = "night_1"
NIGHT_2 = "night_2"
NIGHT_3 = "night_3"


def _fortune_teller_check(
    game: BOTCModel,
    left: str,
    right: str,
    *,
    yes: bool,
    name: str,
):
    either_registers_as_demon = game.any_of(
        [
            game.registers_as_role(left, "Lord of Typhon", name),
            game.registers_as_role(right, "Lord of Typhon", name),
        ],
        f"{name}_{left}_{right}_either_registers_as_demon",
    )
    if yes:
        return either_registers_as_demon
    return game.not_(
        either_registers_as_demon,
        f"{name}_{left}_{right}_neither_registers_as_demon",
    )


def build_model() -> BOTCModel:
    game = BOTCModel(PLAYERS, characters=CHARACTERS, seating=PLAYERS)

    for role in EVIL_ROLES:
        game.set_character_count(role, 1)

    for player in PLAYERS:
        game.add_role_claim(
            RoleClaim(player, CLAIMS[player]),
            evil_roles=EVIL_ROLES,
            drunk_role="Drunk",
        )

    # You were shown Investigator, but the puzzle only allows Drunk or Marionette as alternatives.
    game.set_possible_actual_roles("You", ["Investigator", "Drunk", "Marionette"])

    for player in PLAYERS:
        left, right = game.neighbors(player)
        game.add_implication(game.actual_is(player, "Lord of Typhon"), game.is_minion(left))
        game.add_implication(game.actual_is(player, "Lord of Typhon"), game.is_minion(right))

    for dead_or_executed in ["Anna", "Hannah", "Dan", "Tim"]:
        game.fix_not_actual(dead_or_executed, "Lord of Typhon")

    game.add_poisoner_effect(NIGHT_1)
    anna_is_not_poisoner = game.not_(game.actual_is("Anna", "Poisoner"), "anna_is_not_poisoner")
    game.add_poisoner_effect(NIGHT_2, active_if=anna_is_not_poisoner)
    poisoner_alive_night_3 = game.all_of(
        [game.actual_is(player, "Poisoner").Not() for player in ["Anna", "Hannah", "Dan"]],
        "poisoner_alive_night_3",
    )
    game.add_poisoner_effect(NIGHT_3, active_if=poisoner_alive_night_3)

    sarah_librarian_claim = game.any_of(
        [game.actual_is("You", "Drunk"), game.actual_is("Hannah", "Drunk")],
        "sarah_librarian_you_or_hannah_drunk",
    )
    you_investigator_claim = game.any_of(
        [
            game.actual_is("Matt", "Marionette"),
            game.actual_is("Hannah", "Marionette"),
        ],
        "you_investigator_matt_or_hannah_marionette",
    )
    hannah_dreamer_claim = game.bool_sum_equals(
        [
            game.actual_is("You", "Investigator"),
            game.actual_is("You", "Lord of Typhon"),
        ],
        1,
        "hannah_dreamer_one_option_correct",
    )
    anna_empath_claim = game.all_of(
        [
            game.registers_as_evil("You", "anna_empath"),
            game.registers_as_evil("Dan", "anna_empath"),
        ],
        "anna_empath_both_neighbors_register_evil",
    )
    fraser_fortune_teller_night_1 = _fortune_teller_check(
        game,
        "Anna",
        "Tim",
        yes=True,
        name="fraser_fortune_teller_night_1",
    )

    game.add_truthful_info_claim(
        "Sarah",
        "Librarian",
        sarah_librarian_claim,
        poison_context=NIGHT_1,
    )
    game.add_truthful_info_claim(
        "You",
        "Investigator",
        you_investigator_claim,
        poison_context=NIGHT_1,
    )
    game.add_truthful_info_claim(
        "Hannah",
        "Dreamer",
        hannah_dreamer_claim,
        poison_context=NIGHT_1,
    )
    game.add_truthful_info_claim(
        "Anna",
        "Empath",
        anna_empath_claim,
        poison_context=NIGHT_1,
    )
    game.add_truthful_info_claim(
        "Fraser",
        "Fortune Teller",
        fraser_fortune_teller_night_1,
        poison_context=NIGHT_1,
    )

    dan_undertaker_claim = game.actual_is("Anna", "Empath")
    matt_juggler_claim = game.bool_sum_equals(
        [
            game.actual_is("You", "Investigator"),
            game.actual_is("Dan", "Lord of Typhon"),
            game.actual_is("Tim", "Recluse"),
            game.actual_is("Hannah", "Dreamer"),
        ],
        1,
        "matt_juggler_one_correct",
    )
    fraser_fortune_teller_night_2 = _fortune_teller_check(
        game,
        "You",
        "Fraser",
        yes=False,
        name="fraser_fortune_teller_night_2",
    )

    game.add_truthful_info_claim(
        "Dan",
        "Undertaker",
        dan_undertaker_claim,
        poison_context=NIGHT_2,
    )
    game.add_truthful_info_claim(
        "Matt",
        "Juggler",
        matt_juggler_claim,
        poison_context=NIGHT_2,
    )
    game.add_truthful_info_claim(
        "Fraser",
        "Fortune Teller",
        fraser_fortune_teller_night_2,
        poison_context=NIGHT_2,
    )

    fraser_fortune_teller_night_3 = _fortune_teller_check(
        game,
        "You",
        "Sarah",
        yes=True,
        name="fraser_fortune_teller_night_3",
    )
    game.add_truthful_info_claim(
        "Fraser",
        "Fortune Teller",
        fraser_fortune_teller_night_3,
        poison_context=NIGHT_3,
    )

    return game


def solve():
    return build_model().solve_all()


def main() -> None:
    print_solution(
        solve(),
        PLAYERS,
        poison_context=NIGHT_2,
        forced_roles=[
            forced_role("Demon", "Lord of Typhon", include_role=True),
        ],
    )


if __name__ == "__main__":
    main()
