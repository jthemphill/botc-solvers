from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ortools.sat.python import cp_model

    from botc_solver.model import BOTCModel


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


def role_name(role: object) -> str:
    if isinstance(role, str):
        return role

    named_role = getattr(role, "role_name", None)
    if isinstance(named_role, str):
        return named_role

    legacy_name = getattr(role, "name", None)
    if isinstance(legacy_name, str):
        return legacy_name

    raise TypeError(f"Expected a role name, Character, or role class; got {role!r}.")


def role_alignment(role: object) -> Alignment:
    alignment = getattr(role, "alignment", None)
    if isinstance(alignment, Alignment):
        return alignment
    raise TypeError(f"Role {role!r} does not expose Alignment metadata.")


def role_character_type(role: object) -> CharacterType:
    character_type = getattr(role, "character_type", None)
    if isinstance(character_type, CharacterType):
        return character_type
    raise TypeError(f"Role {role!r} does not expose CharacterType metadata.")


@dataclass(frozen=True)
class Character:
    name: str
    alignment: Alignment
    character_type: CharacterType

    def claim(
        self,
        game: BOTCModel,
        player: str,
        *,
        learned: cp_model.IntVar | None = None,
        poison_context: str | None = None,
        drunk_role: str = "Drunk",
    ) -> None:
        game.add_role_claim(RoleClaim(player, self.name), drunk_role=drunk_role)
        if learned is not None:
            game.add_truthful_info_claim(
                player,
                self.name,
                learned,
                poison_context=poison_context,
            )


@dataclass(frozen=True)
class RoleClaim:
    player: str
    apparent_role: object
