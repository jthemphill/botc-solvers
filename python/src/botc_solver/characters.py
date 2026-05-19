from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, ClassVar, Protocol

from ortools.sat.python import cp_model

from botc_solver import predicates
from botc_solver.core import (
    Alignment,
    CharacterType,
    RoleClaim,
    role_alignment,
    role_character_type,
    role_name,
)

if TYPE_CHECKING:
    from botc_solver.model import BOTCModel


RoleRef = object
StatementResult = cp_model.IntVar | Sequence[cp_model.IntVar]


class StatementFactory(Protocol):
    def __call__(self, game: BOTCModel) -> StatementResult: ...


StatementBuilder = StatementResult | StatementFactory


def _slug(value: str) -> str:
    return "".join(ch.lower() if ch.isalnum() else "_" for ch in value).strip("_")


def _claim_name(player: str, role: RoleRef, suffix: str) -> str:
    return f"{_slug(player)}_{_slug(role_name(role))}_{suffix}"


def _build_statement(
    game: BOTCModel,
    player: str,
    index: int,
    statement: StatementBuilder,
) -> cp_model.IntVar:
    if callable(statement):
        statement = statement(game)
    if isinstance(statement, Sequence):
        return Savant.learns_exactly_one(
            game,
            statement,
            _claim_name(player, Savant, f"statement_{index}"),
        )
    return statement


def _learns_role_among(
    game: BOTCModel,
    players: Sequence[str],
    role: RoleRef,
    name: str,
    *,
    registers: bool = True,
) -> cp_model.IntVar:
    if registers:
        return predicates.registers_as_role_among(game, players, role, name)
    role_ref = role_name(role)
    return game.any_of(
        [game.actual_is(player, role_ref) for player in players],
        f"{name}_{'_'.join(players)}_actual_{role_ref}",
    )


def _learns_character_type_among(
    game: BOTCModel,
    players: Sequence[str],
    character_type: CharacterType,
    name: str,
    *,
    registers: bool = False,
) -> cp_model.IntVar:
    if registers:
        options = [
            game.registers_as_character_type(player, character_type, name)
            for player in players
        ]
    else:
        options = [
            game.has_character_type(player, character_type) for player in players
        ]
    return game.any_of(
        options, f"{name}_{'_'.join(players)}_has_{character_type.value}"
    )


def _learns_character_type_count(
    game: BOTCModel,
    players: Sequence[str],
    character_type: CharacterType,
    count: int,
    name: str,
    *,
    registers: bool = True,
) -> cp_model.IntVar:
    if registers:
        options = [
            game.registers_as_character_type(player, character_type, name)
            for player in players
        ]
    else:
        options = [
            game.has_character_type(player, character_type) for player in players
        ]
    return game.bool_sum_equals(
        options,
        count,
        f"{name}_{character_type.value}_count_is_{count}",
    )


@dataclass(frozen=True, kw_only=True)
class Role:
    role_name: ClassVar[str]
    alignment: ClassVar[Alignment]
    character_type: ClassVar[CharacterType]

    name: str
    poison_context: str | None = None

    @classmethod
    def claim(
        cls,
        game: BOTCModel,
        player: str,
        *,
        learned: cp_model.IntVar | None = None,
        poison_context: str | None = None,
        drunk_role: RoleRef = "Drunk",
    ) -> None:
        game.add_role_claim(RoleClaim(player, cls), drunk_role=drunk_role)
        if learned is not None:
            game.add_truthful_info_claim(
                player,
                cls,
                learned,
                poison_context=poison_context,
            )

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        return None

    def apply(
        self,
        game: BOTCModel,
        *,
        poison_context: str | None = None,
        drunk_role: RoleRef = "Drunk",
    ) -> None:
        type(self).claim(
            game,
            self.name,
            learned=self.learned_info(game),
            poison_context=(
                self.poison_context
                if self.poison_context is not None
                else poison_context
            ),
            drunk_role=drunk_role,
        )


class Imp(Role):
    role_name = "Imp"
    alignment = Alignment.EVIL
    character_type = CharacterType.DEMON


class Leviathan(Role):
    role_name = "Leviathan"
    alignment = Alignment.EVIL
    character_type = CharacterType.DEMON


class LordOfTyphon(Role):
    role_name = "Lord of Typhon"
    alignment = Alignment.EVIL
    character_type = CharacterType.DEMON


class Baron(Role):
    role_name = "Baron"
    alignment = Alignment.EVIL
    character_type = CharacterType.MINION


class Goblin(Role):
    role_name = "Goblin"
    alignment = Alignment.EVIL
    character_type = CharacterType.MINION


class Marionette(Role):
    role_name = "Marionette"
    alignment = Alignment.EVIL
    character_type = CharacterType.MINION


class Poisoner(Role):
    role_name = "Poisoner"
    alignment = Alignment.EVIL
    character_type = CharacterType.MINION


class ScarletWoman(Role):
    role_name = "Scarlet Woman"
    alignment = Alignment.EVIL
    character_type = CharacterType.MINION


class Spy(Role):
    role_name = "Spy"
    alignment = Alignment.EVIL
    character_type = CharacterType.MINION


class Drunk(Role):
    role_name = "Drunk"
    alignment = Alignment.GOOD
    character_type = CharacterType.OUTSIDER


class Recluse(Role):
    role_name = "Recluse"
    alignment = Alignment.GOOD
    character_type = CharacterType.OUTSIDER


class Saint(Role):
    role_name = "Saint"
    alignment = Alignment.GOOD
    character_type = CharacterType.OUTSIDER


@dataclass(frozen=True, kw_only=True)
class Balloonist(Role):
    role_name = "Balloonist"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    different_character_type_pairs: Sequence[tuple[str, str]] = ()

    @classmethod
    def learns_different_character_types(
        cls,
        game: BOTCModel,
        pairs: Sequence[tuple[str, str]],
        name: str,
    ) -> cp_model.IntVar:
        return game.all_of(
            [
                predicates.different_character_types(game, left, right)
                for left, right in pairs
            ],
            name,
        )

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if not self.different_character_type_pairs:
            return None
        return type(self).learns_different_character_types(
            game,
            self.different_character_type_pairs,
            _claim_name(self.name, type(self), "different_types"),
        )


@dataclass(frozen=True, kw_only=True)
class Chef(Role):
    role_name = "Chef"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    count: int | None = None
    registers: bool = True

    @classmethod
    def learns_count(
        cls,
        game: BOTCModel,
        count: int,
        name: str,
        *,
        registers: bool = True,
    ) -> cp_model.IntVar:
        if registers:
            return predicates.chef_count_registers_as(game, count, name)
        return predicates.chef_count_is(game, count)

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.count is None:
            return None
        return type(self).learns_count(
            game,
            self.count,
            _claim_name(self.name, type(self), "count"),
            registers=self.registers,
        )


@dataclass(frozen=True, kw_only=True)
class Clockmaker(Role):
    role_name = "Clockmaker"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    demon_next_to_minion: bool | None = None

    @classmethod
    def learns_demon_next_to_minion(cls, game: BOTCModel, name: str) -> cp_model.IntVar:
        return game.any_of(
            [
                game.all_of(
                    [game.is_demon(left), game.is_minion(right)],
                    f"{left}_{right}_demon_minion_neighbors",
                )
                for left, right in game.adjacent_pairs()
            ]
            + [
                game.all_of(
                    [game.is_minion(left), game.is_demon(right)],
                    f"{left}_{right}_minion_demon_neighbors",
                )
                for left, right in game.adjacent_pairs()
            ],
            name,
        )

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.demon_next_to_minion is None:
            return None
        claim = type(self).learns_demon_next_to_minion(
            game,
            _claim_name(self.name, type(self), "demon_next_to_minion"),
        )
        if self.demon_next_to_minion:
            return claim
        return game.not_(
            claim, _claim_name(self.name, type(self), "demon_not_next_to_minion")
        )


@dataclass(frozen=True, kw_only=True)
class Dreamer(Role):
    role_name = "Dreamer"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    player: str | None = None
    roles: Sequence[RoleRef] = ()

    @classmethod
    def learns_one_of(
        cls,
        game: BOTCModel,
        player: str,
        roles: Sequence[RoleRef],
        name: str,
    ) -> cp_model.IntVar:
        return game.bool_sum_equals(
            [game.actual_is(player, role) for role in roles],
            1,
            name,
        )

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.player is None or not self.roles:
            return None
        return type(self).learns_one_of(
            game,
            self.player,
            self.roles,
            _claim_name(self.name, type(self), "one_of"),
        )


@dataclass(frozen=True, kw_only=True)
class Empath(Role):
    role_name = "Empath"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    count: int | None = None
    player: str | None = None

    @classmethod
    def learns_count(
        cls,
        game: BOTCModel,
        player: str,
        count: int,
        name: str,
    ) -> cp_model.IntVar:
        left, right = game.neighbors(player)
        return game.bool_sum_equals(
            [
                game.registers_as_evil(left, name),
                game.registers_as_evil(right, name),
            ],
            count,
            f"{name}_empath_count_is_{count}",
        )

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.count is None:
            return None
        return type(self).learns_count(
            game,
            self.player or self.name,
            self.count,
            _claim_name(self.name, type(self), "count"),
        )


@dataclass(frozen=True, kw_only=True)
class FortuneTellerCheck:
    left: str
    right: str
    yes: bool
    name: str | None = None
    demon_role: RoleRef | None = None
    registers: bool = False
    poison_context: str | None = None


@dataclass(frozen=True, kw_only=True)
class FortuneTeller(Role):
    role_name = "Fortune Teller"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    checks: Sequence[FortuneTellerCheck] = ()

    @classmethod
    def learns_check(
        cls,
        game: BOTCModel,
        left: str,
        right: str,
        *,
        yes: bool,
        name: str,
        demon_role: RoleRef | None = None,
        registers: bool = False,
    ) -> cp_model.IntVar:
        if demon_role is None:
            options = [game.is_demon(left), game.is_demon(right)]
        elif registers:
            options = [
                game.registers_as_role(left, demon_role, name),
                game.registers_as_role(right, demon_role, name),
            ]
        else:
            options = [
                game.actual_is(left, demon_role),
                game.actual_is(right, demon_role),
            ]

        either_is_demon = game.any_of(options, f"{name}_{left}_{right}_either_demon")
        if yes:
            return either_is_demon
        return game.not_(either_is_demon, f"{name}_{left}_{right}_neither_demon")

    def apply(
        self,
        game: BOTCModel,
        *,
        poison_context: str | None = None,
        drunk_role: RoleRef = "Drunk",
    ) -> None:
        if not self.checks:
            super().apply(game, poison_context=poison_context, drunk_role=drunk_role)
            return

        for index, check in enumerate(self.checks, start=1):
            learned = type(self).learns_check(
                game,
                check.left,
                check.right,
                yes=check.yes,
                name=check.name or _claim_name(self.name, type(self), f"check_{index}"),
                demon_role=check.demon_role,
                registers=check.registers,
            )
            type(self).claim(
                game,
                self.name,
                learned=learned,
                poison_context=(
                    check.poison_context
                    if check.poison_context is not None
                    else (
                        self.poison_context
                        if self.poison_context is not None
                        else poison_context
                    )
                ),
                drunk_role=drunk_role,
            )


@dataclass(frozen=True, kw_only=True)
class Investigator(Role):
    role_name = "Investigator"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    among: Sequence[str] = ()
    role: RoleRef | None = None
    minion_role: RoleRef | None = None
    registers: bool = True

    @classmethod
    def learns_role_among(
        cls,
        game: BOTCModel,
        players: Sequence[str],
        role: RoleRef,
        name: str,
        *,
        registers: bool = True,
    ) -> cp_model.IntVar:
        return _learns_role_among(game, players, role, name, registers=registers)

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        role = self.role if self.role is not None else self.minion_role
        if role is None:
            return None
        return type(self).learns_role_among(
            game,
            self.among,
            role,
            _claim_name(self.name, type(self), "role_among"),
            registers=self.registers,
        )


@dataclass(frozen=True, kw_only=True)
class Juggler(Role):
    role_name = "Juggler"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    guesses: Mapping[str, RoleRef] | Sequence[tuple[str, RoleRef]] = ()
    correct_count: int | None = None

    @classmethod
    def learns_correct_count(
        cls,
        game: BOTCModel,
        guesses: Mapping[str, RoleRef] | Sequence[tuple[str, RoleRef]],
        count: int,
        name: str,
    ) -> cp_model.IntVar:
        items = guesses.items() if isinstance(guesses, Mapping) else guesses
        return game.bool_sum_equals(
            [game.actual_is(player, role) for player, role in items],
            count,
            name,
        )

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.correct_count is None:
            return None
        return type(self).learns_correct_count(
            game,
            self.guesses,
            self.correct_count,
            _claim_name(self.name, type(self), "correct_count"),
        )


@dataclass(frozen=True, kw_only=True)
class Knight(Role):
    role_name = "Knight"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    no_demon_among: Sequence[str] = ()

    @classmethod
    def learns_no_demon_among(
        cls,
        game: BOTCModel,
        players: Sequence[str],
        name: str,
    ) -> cp_model.IntVar:
        any_demon = game.any_of(
            [game.is_demon(player) for player in players],
            f"{name}_{'_'.join(players)}_any_demon",
        )
        return game.not_(any_demon, f"{name}_{'_'.join(players)}_no_demon")

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if not self.no_demon_among:
            return None
        return type(self).learns_no_demon_among(
            game,
            self.no_demon_among,
            _claim_name(self.name, type(self), "no_demon"),
        )


@dataclass(frozen=True, kw_only=True)
class Librarian(Role):
    role_name = "Librarian"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    among: Sequence[str] = ()
    role: RoleRef | None = None
    outsider_count: int | None = None
    registers: bool = True

    @classmethod
    def learns_role_among(
        cls,
        game: BOTCModel,
        players: Sequence[str],
        role: RoleRef,
        name: str,
        *,
        registers: bool = True,
    ) -> cp_model.IntVar:
        return _learns_role_among(game, players, role, name, registers=registers)

    @classmethod
    def learns_character_type_count(
        cls,
        game: BOTCModel,
        players: Sequence[str],
        character_type: CharacterType,
        count: int,
        name: str,
        *,
        registers: bool = True,
    ) -> cp_model.IntVar:
        return _learns_character_type_count(
            game,
            players,
            character_type,
            count,
            name,
            registers=registers,
        )

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.role is not None:
            return type(self).learns_role_among(
                game,
                self.among,
                self.role,
                _claim_name(self.name, type(self), "role_among"),
                registers=self.registers,
            )
        if self.outsider_count is not None:
            return type(self).learns_character_type_count(
                game,
                game.players,
                CharacterType.OUTSIDER,
                self.outsider_count,
                _claim_name(self.name, type(self), "outsider_count"),
                registers=self.registers,
            )
        return None


@dataclass(frozen=True, kw_only=True)
class Noble(Role):
    role_name = "Noble"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    one_evil_among: Sequence[str] = ()
    among: Sequence[str] = ()
    evil_count: int | None = None

    @classmethod
    def learns_evil_count(
        cls,
        game: BOTCModel,
        players: Sequence[str],
        count: int,
    ) -> cp_model.IntVar:
        return predicates.exactly_n_evil(game, players, count)

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.one_evil_among:
            return type(self).learns_evil_count(game, self.one_evil_among, 1)
        if self.evil_count is None:
            return None
        return type(self).learns_evil_count(game, self.among, self.evil_count)


@dataclass(frozen=True, kw_only=True)
class Savant(Role):
    role_name = "Savant"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    statements: Sequence[StatementBuilder] = ()

    @classmethod
    def learns_exactly_one(
        cls,
        game: BOTCModel,
        statements: Iterable[cp_model.IntVar],
        name: str,
    ) -> cp_model.IntVar:
        return game.bool_sum_equals(statements, 1, name)

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if not self.statements:
            return None
        return game.all_of(
            [
                _build_statement(game, self.name, index, statement)
                for index, statement in enumerate(self.statements, start=1)
            ],
            _claim_name(self.name, type(self), "all_statements"),
        )


@dataclass(frozen=True, kw_only=True)
class Seamstress(Role):
    role_name = "Seamstress"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    among: Sequence[str] = ()
    aligned: bool | None = None

    @classmethod
    def learns_same_alignment(
        cls,
        game: BOTCModel,
        left: str,
        right: str,
    ) -> cp_model.IntVar:
        return predicates.same_alignment(game, left, right)

    @classmethod
    def learns_different_alignment(
        cls,
        game: BOTCModel,
        left: str,
        right: str,
    ) -> cp_model.IntVar:
        return predicates.different_alignments(game, left, right)

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.aligned is None:
            return None
        left, right = self.among
        if self.aligned:
            return type(self).learns_same_alignment(game, left, right)
        return type(self).learns_different_alignment(game, left, right)


class Slayer(Role):
    role_name = "Slayer"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK


@dataclass(frozen=True, kw_only=True)
class Steward(Role):
    role_name = "Steward"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    good_player: str | None = None

    @classmethod
    def learns_good_player(cls, game: BOTCModel, player: str) -> cp_model.IntVar:
        return game.is_good(player)

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.good_player is None:
            return None
        return type(self).learns_good_player(game, self.good_player)


@dataclass(frozen=True, kw_only=True)
class Undertaker(Role):
    role_name = "Undertaker"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    player: str | None = None
    role: RoleRef | None = None

    @classmethod
    def learns_role(
        cls,
        game: BOTCModel,
        player: str,
        role: RoleRef,
    ) -> cp_model.IntVar:
        return game.actual_is(player, role)

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.player is None or self.role is None:
            return None
        return type(self).learns_role(game, self.player, self.role)


@dataclass(frozen=True, kw_only=True)
class Washerwoman(Role):
    role_name = "Washerwoman"
    alignment = Alignment.GOOD
    character_type = CharacterType.TOWNSFOLK

    among: Sequence[str] = ()
    role: RoleRef | None = None
    registers: bool = True

    @classmethod
    def learns_role_among(
        cls,
        game: BOTCModel,
        players: Sequence[str],
        role: RoleRef,
        name: str,
        *,
        registers: bool = True,
    ) -> cp_model.IntVar:
        return _learns_role_among(game, players, role, name, registers=registers)

    def learned_info(self, game: BOTCModel) -> cp_model.IntVar | None:
        if self.role is None:
            return None
        return type(self).learns_role_among(
            game,
            self.among,
            self.role,
            _claim_name(self.name, type(self), "role_among"),
            registers=self.registers,
        )


ClaimRef = str | Role


def player_name(player: ClaimRef) -> str:
    if isinstance(player, Role):
        return player.name
    return player


def player_names(players: Iterable[ClaimRef]) -> list[str]:
    names: list[str] = []
    seen: set[str] = set()
    for player in players:
        name = player_name(player)
        if name not in seen:
            seen.add(name)
            names.append(name)
    return names


def apply_claims(
    game: BOTCModel,
    claims: Iterable[Role],
    *,
    poison_context: str | None = None,
    drunk_role: RoleRef = "Drunk",
) -> None:
    for claim in claims:
        claim.apply(game, poison_context=poison_context, drunk_role=drunk_role)


def script(*characters: RoleRef) -> tuple[RoleRef, ...]:
    return characters


def role_names(
    characters: Iterable[RoleRef],
    *,
    alignment: Alignment | None = None,
    character_type: CharacterType | None = None,
) -> tuple[str, ...]:
    return tuple(
        role_name(character)
        for character in characters
        if (alignment is None or role_alignment(character) == alignment)
        and (character_type is None or role_character_type(character) == character_type)
    )


__all__ = [
    "Balloonist",
    "Baron",
    "Chef",
    "Clockmaker",
    "Dreamer",
    "Drunk",
    "Empath",
    "FortuneTeller",
    "FortuneTellerCheck",
    "Goblin",
    "Imp",
    "Investigator",
    "Juggler",
    "Knight",
    "Leviathan",
    "Librarian",
    "LordOfTyphon",
    "Marionette",
    "Noble",
    "Poisoner",
    "Recluse",
    "Role",
    "Saint",
    "Savant",
    "ScarletWoman",
    "Seamstress",
    "Slayer",
    "Spy",
    "Steward",
    "Undertaker",
    "Washerwoman",
    "apply_claims",
    "player_name",
    "player_names",
    "role_names",
    "script",
]
