from __future__ import annotations

from botc_solver import Alignment, BOTCModel, Character, CharacterType, RoleClaim, World, forced_role_holders
from botc_solver.predicates import chef_count_is


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

    poisoned_count = sum(game.poisoned(player) for player in PLAYERS)
    poisoner_in_play = game.role_in_play("Poisoner")
    game.add_enforced(poisoned_count == 1, poisoner_in_play)
    game.add_enforced(poisoned_count == 0, poisoner_in_play.Not())

    sula_claim = game.any_of(
        [game.actual_is("You", "Baron"), game.actual_is("Aoife", "Baron")],
        "sula_claim_you_or_aoife_baron",
    )
    matthew_claim = game.any_of(
        [game.actual_is("Aoife", "Librarian"), game.actual_is("Oscar", "Librarian")],
        "matthew_claim_aoife_or_oscar_librarian",
    )
    oscar_claim = game.bool_sum_equals(
        [game.has_character_type(player, CharacterType.OUTSIDER) for player in PLAYERS],
        0,
        "oscar_claim_no_outsiders",
    )
    josh_claim = game.not_(
        game.any_of([game.is_evil("You"), game.is_evil("Oscar")], "you_or_oscar_evil"),
        "neither_you_nor_oscar_evil",
    )
    aoife_claim = chef_count_is(game, 0)

    game.add_truthful_info_claim("Sula", "Investigator", sula_claim)
    game.add_truthful_info_claim("Matthew", "Washerwoman", matthew_claim)
    game.add_truthful_info_claim("Oscar", "Librarian", oscar_claim)
    game.add_truthful_info_claim("Josh", "Empath", josh_claim)
    game.add_truthful_info_claim("Aoife", "Chef", aoife_claim)

    game.add_truth(game.actual_is("You", "Slayer"))
    game.add_false(game.poisoned("You"))
    tom_imp_with_scarlet_woman = game.all_of(
        [game.actual_is("Tom", "Imp"), game.role_in_play("Scarlet Woman")],
        "tom_imp_with_scarlet_woman",
    )
    game.add_truth(
        game.any_of(
            [game.actual_is("Tom", "Recluse"), tom_imp_with_scarlet_woman],
            "slayer_shot_tom_died_without_game_ending",
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
