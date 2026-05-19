from __future__ import annotations

from collections.abc import Iterable

from botc_solver.core import Alignment, Character, CharacterType


def _character(name: str, alignment: Alignment, character_type: CharacterType) -> Character:
    return Character(name, alignment, character_type)


IMP = _character("Imp", Alignment.EVIL, CharacterType.DEMON)
LEVIATHAN = _character("Leviathan", Alignment.EVIL, CharacterType.DEMON)
LORD_OF_TYPHON = _character("Lord of Typhon", Alignment.EVIL, CharacterType.DEMON)

BARON = _character("Baron", Alignment.EVIL, CharacterType.MINION)
GOBLIN = _character("Goblin", Alignment.EVIL, CharacterType.MINION)
MARIONETTE = _character("Marionette", Alignment.EVIL, CharacterType.MINION)
POISONER = _character("Poisoner", Alignment.EVIL, CharacterType.MINION)
SCARLET_WOMAN = _character("Scarlet Woman", Alignment.EVIL, CharacterType.MINION)
SPY = _character("Spy", Alignment.EVIL, CharacterType.MINION)

DRUNK = _character("Drunk", Alignment.GOOD, CharacterType.OUTSIDER)
RECLUSE = _character("Recluse", Alignment.GOOD, CharacterType.OUTSIDER)
SAINT = _character("Saint", Alignment.GOOD, CharacterType.OUTSIDER)

BALLOONIST = _character("Balloonist", Alignment.GOOD, CharacterType.TOWNSFOLK)
CHEF = _character("Chef", Alignment.GOOD, CharacterType.TOWNSFOLK)
CLOCKMAKER = _character("Clockmaker", Alignment.GOOD, CharacterType.TOWNSFOLK)
DREAMER = _character("Dreamer", Alignment.GOOD, CharacterType.TOWNSFOLK)
EMPATH = _character("Empath", Alignment.GOOD, CharacterType.TOWNSFOLK)
FORTUNE_TELLER = _character("Fortune Teller", Alignment.GOOD, CharacterType.TOWNSFOLK)
INVESTIGATOR = _character("Investigator", Alignment.GOOD, CharacterType.TOWNSFOLK)
JUGGLER = _character("Juggler", Alignment.GOOD, CharacterType.TOWNSFOLK)
KNIGHT = _character("Knight", Alignment.GOOD, CharacterType.TOWNSFOLK)
LIBRARIAN = _character("Librarian", Alignment.GOOD, CharacterType.TOWNSFOLK)
NOBLE = _character("Noble", Alignment.GOOD, CharacterType.TOWNSFOLK)
SAVANT = _character("Savant", Alignment.GOOD, CharacterType.TOWNSFOLK)
SEAMSTRESS = _character("Seamstress", Alignment.GOOD, CharacterType.TOWNSFOLK)
SLAYER = _character("Slayer", Alignment.GOOD, CharacterType.TOWNSFOLK)
STEWARD = _character("Steward", Alignment.GOOD, CharacterType.TOWNSFOLK)
UNDERTAKER = _character("Undertaker", Alignment.GOOD, CharacterType.TOWNSFOLK)
WASHERWOMAN = _character("Washerwoman", Alignment.GOOD, CharacterType.TOWNSFOLK)


def script(*characters: Character) -> tuple[Character, ...]:
    return characters


def role_names(
    characters: Iterable[Character],
    *,
    alignment: Alignment | None = None,
    character_type: CharacterType | None = None,
) -> tuple[str, ...]:
    return tuple(
        character.name
        for character in characters
        if (alignment is None or character.alignment == alignment)
        and (character_type is None or character.character_type == character_type)
    )


__all__ = [
    "BALLOONIST",
    "BARON",
    "CHEF",
    "CLOCKMAKER",
    "DREAMER",
    "DRUNK",
    "EMPATH",
    "FORTUNE_TELLER",
    "GOBLIN",
    "IMP",
    "INVESTIGATOR",
    "JUGGLER",
    "KNIGHT",
    "LEVIATHAN",
    "LIBRARIAN",
    "LORD_OF_TYPHON",
    "MARIONETTE",
    "NOBLE",
    "POISONER",
    "RECLUSE",
    "SAINT",
    "SAVANT",
    "SCARLET_WOMAN",
    "SEAMSTRESS",
    "SLAYER",
    "SPY",
    "STEWARD",
    "UNDERTAKER",
    "WASHERWOMAN",
    "role_names",
    "script",
]
