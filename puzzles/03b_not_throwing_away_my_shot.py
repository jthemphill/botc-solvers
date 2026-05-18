from __future__ import annotations

from botc_solver import Alignment, BOTCModel, Character, CharacterType, RoleClaim, World, forced_role_holders
from botc_solver.predicates import chef_count_registers_as


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
MINION_ROLES = (character.name for character in CHARACTERS if character.character_type == CharacterType.MINION)
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
    matt_claim = game.any_of(
        [
            game.registers_as_role("Tim", "Librarian", "matt_washerwoman"),
            game.registers_as_role("Dan", "Librarian", "matt_washerwoman"),
        ],
        "matt_claim_tim_or_dan_librarian",
    )
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
    tim_claim = game.any_of(
        [
            game.registers_as_role("You", "Drunk", "tim_librarian"),
            game.registers_as_role("Hannah", "Drunk", "tim_librarian"),
        ],
        "tim_claim_you_or_hannah_drunk",
    )
    sarah_claim = game.any_of(
        [
            game.registers_as_role("Tim", "Scarlet Woman", "sarah_investigator"),
            game.registers_as_role("Fraser", "Scarlet Woman", "sarah_investigator"),
        ],
        "sarah_claim_tim_or_fraser_scarlet_woman",
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
            poison_suffix = " poisoned" if world.is_poisoned(player, POISON_CONTEXT) else ""
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
