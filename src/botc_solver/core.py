from __future__ import annotations

from dataclasses import dataclass
from enum import Enum


class Alignment(str, Enum):
    GOOD = "good"
    EVIL = "evil"


class CharacterType(str, Enum):
    TOWNSFOLK = "townsfolk"
    OUTSIDER = "outsider"
    MINION = "minion"
    DEMON = "demon"


class StatusEffect(str, Enum):
    POISONED = "poisoned"


@dataclass(frozen=True)
class Character:
    name: str
    alignment: Alignment
    character_type: CharacterType


@dataclass(frozen=True)
class RoleClaim:
    player: str
    apparent_role: str

