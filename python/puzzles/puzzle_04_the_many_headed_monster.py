"""
"The Many-Headed Monster"
by Not Quite Tangible

https://www.reddit.com/r/BloodOnTheClocktower/comments/1f823s4/weekly_puzzle_4_the_manyheaded_monster/
"""

from __future__ import annotations

from botc_solver import (
    Alignment,
    BOTCModel,
    CharacterType,
    forced_role,
    print_solution,
)
from botc_solver.characters import (
    Dreamer,
    Drunk,
    Empath,
    FortuneTeller,
    FortuneTellerCheck,
    Investigator,
    Juggler,
    Librarian,
    LordOfTyphon,
    Marionette,
    Poisoner,
    Recluse,
    Undertaker,
    apply_claims,
    player_names,
    role_names,
    script,
)

NIGHT_1 = "night_1"
NIGHT_2 = "night_2"
NIGHT_3 = "night_3"
PLAYERS = [
    Librarian(
        name="Sarah",
        role=Drunk,
        among=["You", "Hannah"],
        registers=False,
        poison_context=NIGHT_1,
    ),
    Recluse(name="Tim"),
    Juggler(
        name="Matt",
        guesses={
            "You": Investigator,
            "Dan": LordOfTyphon,
            "Tim": Recluse,
            "Hannah": Dreamer,
        },
        correct_count=1,
        poison_context=NIGHT_2,
    ),
    Dreamer(
        name="Hannah",
        player="You",
        roles=[Investigator, LordOfTyphon],
        poison_context=NIGHT_1,
    ),
    Investigator(
        name="You",
        role=Marionette,
        among=["Matt", "Hannah"],
        registers=False,
        poison_context=NIGHT_1,
    ),
    Empath(name="Anna", count=2, poison_context=NIGHT_1),
    Undertaker(name="Dan", player="Anna", role=Empath, poison_context=NIGHT_2),
    FortuneTeller(
        name="Fraser",
        checks=[
            FortuneTellerCheck(
                left="Anna",
                right="Tim",
                yes=True,
                demon_role=LordOfTyphon,
                registers=True,
                poison_context=NIGHT_1,
            ),
            FortuneTellerCheck(
                left="You",
                right="Fraser",
                yes=False,
                demon_role=LordOfTyphon,
                registers=True,
                poison_context=NIGHT_2,
            ),
            FortuneTellerCheck(
                left="You",
                right="Sarah",
                yes=True,
                demon_role=LordOfTyphon,
                registers=True,
                poison_context=NIGHT_3,
            ),
        ],
    ),
]
PLAYER_NAMES = player_names(PLAYERS)
CHARACTERS = script(
    LordOfTyphon,
    Marionette,
    Poisoner,
    Drunk,
    Recluse,
    Investigator,
    Librarian,
    FortuneTeller,
    Juggler,
    Dreamer,
    Empath,
    Undertaker,
)
MINION_ROLES = role_names(CHARACTERS, character_type=CharacterType.MINION)
EVIL_ROLES = role_names(CHARACTERS, alignment=Alignment.EVIL)


def build_model() -> BOTCModel:
    game = BOTCModel(PLAYER_NAMES, characters=CHARACTERS, seating=PLAYER_NAMES)

    for role in EVIL_ROLES:
        game.set_character_count(role, 1)

    for player in PLAYER_NAMES:
        left, right = game.neighbors(player)
        game.add_implication(game.actual_is(player, LordOfTyphon), game.is_minion(left))
        game.add_implication(
            game.actual_is(player, LordOfTyphon), game.is_minion(right)
        )

    for dead_or_executed in ["Anna", "Hannah", "Dan", "Tim"]:
        game.fix_not_actual(dead_or_executed, LordOfTyphon)

    game.add_poisoner_effect(NIGHT_1)
    anna_is_not_poisoner = game.not_(
        game.actual_is("Anna", Poisoner), "anna_is_not_poisoner"
    )
    game.add_poisoner_effect(NIGHT_2, active_if=anna_is_not_poisoner)
    poisoner_alive_night_3 = game.all_of(
        [
            game.actual_is(player, Poisoner).Not()
            for player in ["Anna", "Hannah", "Dan"]
        ],
        "poisoner_alive_night_3",
    )
    game.add_poisoner_effect(NIGHT_3, active_if=poisoner_alive_night_3)

    apply_claims(game, PLAYERS)
    # You were shown Investigator, but the puzzle only allows Drunk or Marionette as alternatives.
    game.set_possible_actual_roles("You", [Investigator, Drunk, Marionette])

    return game


def solve():
    return build_model().solve_all()


def main() -> None:
    print_solution(
        solve(),
        PLAYER_NAMES,
        poison_context=NIGHT_2,
        forced_roles=[
            forced_role("Demon", LordOfTyphon, include_role=True),
        ],
    )


if __name__ == "__main__":
    main()
