from __future__ import annotations

from botc_solver import Alignment, BOTCModel, Character, CharacterType, RoleClaim, World, forced_role_holders
from botc_solver.predicates import chef_count_is


PLAYERS = ["Dan", "Anna", "Matt", "Fraser", "You", "Tim", "Sarah", "Hannah"]
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
    Character("Saint", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Chef", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Empath", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Investigator", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Librarian", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Slayer", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Washerwoman", Alignment.GOOD, CharacterType.TOWNSFOLK),
)
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

    poisoned_count = sum(game.poisoned(player) for player in PLAYERS)
    poisoner_in_play = game.role_in_play("Poisoner")
    game.add_enforced(poisoned_count == 1, poisoner_in_play)
    game.add_enforced(poisoned_count == 0, poisoner_in_play.Not())

    dan_claim = chef_count_is(game, 0)
    matt_claim = game.any_of(
        [game.actual_is("Tim", "Librarian"), game.actual_is("Dan", "Librarian")],
        "matt_claim_tim_or_dan_librarian",
    )
    fraser_claim = game.not_(
        game.any_of([game.is_evil("You"), game.is_evil("Matt")], "you_or_matt_evil"),
        "neither_you_nor_matt_evil",
    )
    tim_claim = game.any_of(
        [game.actual_is("You", "Drunk"), game.actual_is("Hannah", "Drunk")],
        "tim_claim_you_or_hannah_drunk",
    )
    sarah_claim = game.any_of(
        [
            game.actual_is("Tim", "Scarlet Woman"),
            game.actual_is("Fraser", "Scarlet Woman"),
        ],
        "sarah_claim_tim_or_fraser_scarlet_woman",
    )

    game.add_truthful_info_claim("Dan", "Chef", dan_claim)
    game.add_truthful_info_claim("Matt", "Washerwoman", matt_claim)
    game.add_truthful_info_claim("Fraser", "Empath", fraser_claim)
    game.add_truthful_info_claim("Tim", "Librarian", tim_claim)
    game.add_truthful_info_claim("Sarah", "Investigator", sarah_claim)

    game.add_truth(game.actual_is("You", "Slayer"))
    game.add_false(game.poisoned("You"))
    anna_imp_with_scarlet_woman = game.all_of(
        [game.actual_is("Anna", "Imp"), game.role_in_play("Scarlet Woman")],
        "anna_imp_with_scarlet_woman",
    )
    game.add_truth(
        game.any_of(
            [game.actual_is("Anna", "Recluse"), anna_imp_with_scarlet_woman],
            "slayer_shot_anna_died_without_game_ending",
        )
    )

    return game


def solve():
    return build_model().solve_all()


def _forced_minion(worlds: list[World]):
    minions = {
        (holder, role)
        for world in worlds
        for role in MINION_ROLES
        for holder in [world.holder(role)]
        if holder is not None
    }
    if len(minions) == 1:
        return next(iter(minions))
    return None


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
    forced = forced_role_holders(worlds, ["Imp", "Drunk", "Recluse"])
    minion = _forced_minion(worlds)
    print(f"  Demon: {forced['Imp'] or 'not forced'} (Imp)")
    if minion is None:
        print("  Minion: not forced")
    else:
        holder, role = minion
        print(f"  Minion: {holder} ({role})")
    print(f"  Drunk: {forced['Drunk'] or 'not in play'}")
    print(f"  Recluse: {forced['Recluse'] or 'not in play'}")


if __name__ == "__main__":
    main()
