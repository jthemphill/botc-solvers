from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Protocol, cast

from ortools.sat.python import cp_model

from botc_solver.core import (
    Alignment,
    CharacterType,
    RoleClaim,
    role_alignment,
    role_character_type,
    role_name,
)

DEFAULT_POISON_CONTEXT = "default"


def _slug(value: str) -> str:
    return "".join(ch.lower() if ch.isalnum() else "_" for ch in value).strip("_")


class _EnforceableConstraint(Protocol):
    def only_enforce_if(self, literal: object) -> cp_model.Constraint: ...


def _only_enforce_if(
    constraint: cp_model.Constraint,
    literal: object,
) -> cp_model.Constraint:
    return cast(_EnforceableConstraint, constraint).only_enforce_if(literal)


@dataclass(frozen=True)
class World:
    actual: Mapping[str, str]
    apparent: Mapping[str, str]
    poisoned: frozenset[str]
    seating: tuple[str, ...]
    poisoned_by_context: Mapping[str, frozenset[str]] = field(
        default_factory=dict[str, frozenset[str]]
    )

    def holder(self, role: object) -> str | None:
        role_ref = role_name(role)
        holders = [
            player
            for player, actual_role in self.actual.items()
            if actual_role == role_ref
        ]
        if len(holders) == 1:
            return holders[0]
        return None

    def actual_role(self, player: str) -> str:
        return self.actual[player]

    def is_poisoned(self, player: str, context: str | None = None) -> bool:
        if context is None:
            return player in self.poisoned
        return player in self.poisoned_by_context.get(context, frozenset())


def forced_role_holders(
    worlds: Sequence[World], roles: Iterable[object]
) -> dict[str, str | None]:
    summary: dict[str, str | None] = {}
    for role in roles:
        role_ref = role_name(role)
        holders = {world.holder(role_ref) for world in worlds}
        summary[role_ref] = next(iter(holders)) if len(holders) == 1 else None
    return summary


class _WorldCollector(cp_model.CpSolverSolutionCallback):
    def __init__(self, game: BOTCModel, limit: int | None) -> None:
        super().__init__()
        self._game = game
        self._limit = limit
        self.worlds: list[World] = []
        self._seen: set[
            tuple[
                tuple[tuple[str, str], ...],
                tuple[tuple[str, str], ...],
                tuple[tuple[str, tuple[str, ...]], ...],
                tuple[str, ...],
            ]
        ] = set()

    def on_solution_callback(self) -> None:
        actual: dict[str, str] = {}
        for player in self._game.players:
            matching = [
                role
                for role in self._game.characters
                if self.value(self._game.actual_is(player, role))
            ]
            if len(matching) != 1:
                raise RuntimeError(
                    f"Expected exactly one actual character for {player}."
                )
            actual[player] = matching[0]

        poisoned_by_context = {
            context: frozenset(
                player
                for player, poison_var in self._game.poisoned_literals(context)
                if self.value(poison_var)
            )
            for context in sorted(self._game.poison_contexts)
        }
        poisoned = poisoned_by_context.get(DEFAULT_POISON_CONTEXT, frozenset())
        key = (
            tuple(sorted(actual.items())),
            tuple(sorted(self._game.apparent_roles.items())),
            tuple(
                (context, tuple(sorted(poisoned_players)))
                for context, poisoned_players in sorted(poisoned_by_context.items())
            ),
            tuple(self._game.seating),
        )
        if key in self._seen:
            return
        self._seen.add(key)
        self.worlds.append(
            World(
                actual=actual,
                apparent=dict(self._game.apparent_roles),
                poisoned=poisoned,
                seating=tuple(self._game.seating),
                poisoned_by_context=poisoned_by_context,
            )
        )
        if self._limit is not None and len(self.worlds) >= self._limit:
            self.stop_search()


class BOTCModel:
    def __init__(
        self,
        players: Sequence[str],
        *,
        characters: Sequence[object],
        seating: Sequence[str] | None = None,
        unique_characters: bool = True,
    ) -> None:
        if not players:
            raise ValueError("At least one player is required.")

        self.players = list(players)
        if len(set(self.players)) != len(self.players):
            raise ValueError("Player names must be unique.")

        self.seating = list(seating or players)
        if len(self.seating) != len(self.players) or set(self.players) != set(
            self.seating
        ):
            raise ValueError("Seating must contain exactly the model players.")

        self.characters = {role_name(character): character for character in characters}
        if len(self.characters) != len(characters):
            raise ValueError("Character names must be unique.")

        self.model: cp_model.CpModel = cp_model.CpModel()
        self.apparent_roles: dict[str, str] = {}
        self._counter = 0
        self._actual = {
            (player, role): self.model.new_bool_var(
                f"{_slug(player)}__actual__{_slug(role)}"
            )
            for player in self.players
            for role in self.characters
        }
        self._poisoned: dict[tuple[str, str], cp_model.IntVar] = {}
        self.poison_contexts: set[str] = set()
        self._predicate_cache: dict[tuple[str, str], cp_model.IntVar] = {}

        for player in self.players:
            self.model.add_exactly_one(
                self.actual_is(player, role) for role in self.characters
            )

        if unique_characters:
            for role in self.characters:
                self.model.add_at_most_one(
                    self.actual_is(player, role) for player in self.players
                )

    def _check_player(self, player: str) -> None:
        if player not in self.players:
            raise KeyError(f"Unknown player: {player}")

    def _check_role(self, role: str) -> None:
        if role not in self.characters:
            raise KeyError(f"Unknown character: {role}")

    def _name(self, stem: str) -> str:
        self._counter += 1
        return f"{_slug(stem)}__{self._counter}"

    def new_bool(self, name: str) -> cp_model.IntVar:
        return self.model.new_bool_var(self._name(name))

    def constant_bool(self, value: bool, name: str) -> cp_model.IntVar:
        result = self.new_bool(name)
        self.model.add(result == int(value))
        return result

    def actual_is(self, player: str, role: object) -> cp_model.IntVar:
        self._check_player(player)
        role_ref = role_name(role)
        self._check_role(role_ref)
        return self._actual[(player, role_ref)]

    def _poison_context(self, context: str | None) -> str:
        if context is None:
            return DEFAULT_POISON_CONTEXT
        if not context:
            raise ValueError("Poison context must not be empty.")
        return context

    def poisoned(self, player: str, context: str | None = None) -> cp_model.IntVar:
        self._check_player(player)
        poison_context = self._poison_context(context)
        key = (poison_context, player)
        if key not in self._poisoned:
            self._poisoned[key] = self.model.new_bool_var(
                f"{_slug(player)}__poisoned__{_slug(poison_context)}"
            )
        self.poison_contexts.add(poison_context)
        return self._poisoned[key]

    def poisoned_literals(self, context: str) -> list[tuple[str, cp_model.IntVar]]:
        poison_context = self._poison_context(context)
        result: list[tuple[str, cp_model.IntVar]] = []
        for player in self.players:
            poison_var = self._poisoned.get((poison_context, player))
            if poison_var is not None:
                result.append((player, poison_var))
        return result

    def set_apparent_role(self, player: str, role: object) -> None:
        self._check_player(player)
        role_ref = role_name(role)
        self._check_role(role_ref)
        self.apparent_roles[player] = role_ref

    def add_role_claim(
        self,
        claim: RoleClaim,
        *,
        evil_roles: Sequence[object] | None = None,
        drunk_role: object = "Drunk",
    ) -> None:
        apparent_role = role_name(claim.apparent_role)
        self.set_apparent_role(claim.player, apparent_role)
        if evil_roles is None:
            evil_roles = tuple(
                role
                for role, character in self.characters.items()
                if role_alignment(character) == Alignment.EVIL
            )
        possible_roles: list[object] = [
            apparent_role,
            *(role_name(role) for role in evil_roles),
        ]
        if (
            role_character_type(self.characters[apparent_role])
            == CharacterType.TOWNSFOLK
        ):
            possible_roles.append(drunk_role)
        self.set_possible_actual_roles(
            claim.player,
            possible_roles,
        )

    def set_possible_actual_roles(self, player: str, roles: Iterable[object]) -> None:
        self._check_player(player)
        allowed = {role_name(role) for role in roles}
        for role in allowed:
            self._check_role(role)
        for role in self.characters:
            if role not in allowed:
                self.add_false(self.actual_is(player, role))

    def fix_actual(self, player: str, role: object) -> None:
        self.add_truth(self.actual_is(player, role))

    def fix_not_actual(self, player: str, role: object) -> None:
        self.add_false(self.actual_is(player, role))

    def fix_poisoned(
        self, player: str, value: bool, context: str | None = None
    ) -> None:
        self.model.add(self.poisoned(player, context) == int(value))

    def add_poisoner_effect(
        self,
        context: str,
        *,
        poisoner_role: object = "Poisoner",
        active_if: cp_model.IntVar | bool | None = None,
    ) -> None:
        poisoned_count = sum(self.poisoned(player, context) for player in self.players)
        poisoner_in_play = self.role_in_play(poisoner_role)
        poisoner_name = role_name(poisoner_role)
        if active_if is None:
            poisoner_active = poisoner_in_play
        elif isinstance(active_if, bool):
            poisoner_active = self.all_of(
                [
                    poisoner_in_play,
                    self.constant_bool(
                        active_if, f"{context}_{poisoner_name}_active_if"
                    ),
                ],
                f"{context}_{poisoner_name}_active",
            )
        else:
            poisoner_active = self.all_of(
                [poisoner_in_play, active_if],
                f"{context}_{poisoner_name}_active",
            )
        self.add_enforced(poisoned_count == 1, poisoner_active)
        self.add_enforced(poisoned_count == 0, poisoner_active.Not())

    def set_character_count(self, role: object, count: int) -> None:
        role_ref = role_name(role)
        self._check_role(role_ref)
        self.model.add(
            sum(self.actual_is(player, role_ref) for player in self.players) == count
        )

    def add_truth(self, literal: cp_model.BoolVarT) -> None:
        self.model.add_bool_or([literal])

    def add_false(self, literal: cp_model.BoolVarT) -> None:
        self.model.add_bool_or([literal.Not()])

    def add_implication(
        self, condition: cp_model.BoolVarT, conclusion: cp_model.BoolVarT
    ) -> None:
        self.model.add_implication(condition, conclusion)

    def add_exactly_one(self, literals: Iterable[cp_model.BoolVarT]) -> None:
        self.model.add_exactly_one(list(literals))

    def add_exactly_n(self, literals: Iterable[cp_model.IntVar], count: int) -> None:
        self.model.add(sum(literals) == count)

    def add_enforced(
        self,
        constraint: cp_model.BoundedLinearExpression | bool,
        condition: object,
    ) -> None:
        _only_enforce_if(self.model.add(constraint), condition)

    def bool_sum_equals(
        self,
        literals: Iterable[cp_model.IntVar],
        count: int,
        name: str,
    ) -> cp_model.IntVar:
        literals = list(literals)
        result = self.new_bool(name)
        total = sum(literals)
        self.add_enforced(total == count, result)
        self.add_enforced(total != count, result.Not())
        return result

    def all_of(
        self, literals: Iterable[cp_model.BoolVarT], name: str
    ) -> cp_model.IntVar:
        literals = list(literals)
        if not literals:
            return self.constant_bool(True, name)
        result = self.new_bool(name)
        _only_enforce_if(self.model.add_bool_and(literals), result)
        _only_enforce_if(
            self.model.add_bool_or([literal.Not() for literal in literals]),
            result.Not(),
        )
        return result

    def any_of(
        self, literals: Iterable[cp_model.BoolVarT], name: str
    ) -> cp_model.IntVar:
        literals = list(literals)
        if not literals:
            return self.constant_bool(False, name)
        result = self.new_bool(name)
        _only_enforce_if(self.model.add_bool_or(literals), result)
        _only_enforce_if(
            self.model.add_bool_and([literal.Not() for literal in literals]),
            result.Not(),
        )
        return result

    def not_(self, literal: cp_model.IntVar, name: str) -> cp_model.IntVar:
        result = self.new_bool(name)
        self.model.add(result + literal == 1)
        return result

    def xor(
        self, left: cp_model.IntVar, right: cp_model.IntVar, name: str
    ) -> cp_model.IntVar:
        return self.bool_sum_equals([left, right], 1, name)

    def is_evil(self, player: str) -> cp_model.IntVar:
        return self._cached_player_predicate(
            "is_evil",
            player,
            [
                self.actual_is(player, role)
                for role, character in self.characters.items()
                if role_alignment(character) == Alignment.EVIL
            ],
        )

    def is_good(self, player: str) -> cp_model.IntVar:
        return self._cached_player_predicate(
            "is_good",
            player,
            [
                self.actual_is(player, role)
                for role, character in self.characters.items()
                if role_alignment(character) == Alignment.GOOD
            ],
        )

    def is_townsfolk(self, player: str) -> cp_model.IntVar:
        return self.has_character_type(player, CharacterType.TOWNSFOLK)

    def has_character_type(
        self,
        player: str,
        character_type: CharacterType,
    ) -> cp_model.IntVar:
        return self._cached_player_predicate(
            f"is_{character_type.value}",
            player,
            [
                self.actual_is(player, role)
                for role, character in self.characters.items()
                if role_character_type(character) == character_type
            ],
        )

    def is_demon(self, player: str) -> cp_model.IntVar:
        return self._cached_player_predicate(
            "is_demon",
            player,
            [
                self.actual_is(player, role)
                for role, character in self.characters.items()
                if role_character_type(character) == CharacterType.DEMON
            ],
        )

    def is_minion(self, player: str) -> cp_model.IntVar:
        return self._cached_player_predicate(
            "is_minion",
            player,
            [
                self.actual_is(player, role)
                for role, character in self.characters.items()
                if role_character_type(character) == CharacterType.MINION
            ],
        )

    def role_in_play(self, role: object) -> cp_model.IntVar:
        role_ref = role_name(role)
        self._check_role(role_ref)
        key = ("role_in_play", role_ref)
        if key not in self._predicate_cache:
            self._predicate_cache[key] = self.any_of(
                [self.actual_is(player, role_ref) for player in self.players],
                f"{role_ref}_in_play",
            )
        return self._predicate_cache[key]

    def registers_as_evil(self, player: str, name: str) -> cp_model.IntVar:
        return self._registers_as_alignment(player, Alignment.EVIL, name)

    def registers_as_good(self, player: str, name: str) -> cp_model.IntVar:
        return self._registers_as_alignment(player, Alignment.GOOD, name)

    def registers_as_character_type(
        self,
        player: str,
        character_type: CharacterType,
        name: str,
    ) -> cp_model.IntVar:
        self._check_player(player)
        result = self.new_bool(f"{name}_{player}_registers_as_{character_type.value}")
        for role, character in self.characters.items():
            actual = self.actual_is(player, role)
            if self._role_can_flexibly_register_as_type(role, character_type):
                continue
            if role_character_type(character) == character_type:
                self.add_implication(actual, result)
            else:
                self.add_implication(actual, result.Not())
        return result

    def registers_as_role(
        self, player: str, role: object, name: str
    ) -> cp_model.IntVar:
        self._check_player(player)
        role_ref = role_name(role)
        self._check_role(role_ref)
        result = self.new_bool(f"{name}_{player}_registers_as_{role_ref}")
        for actual_role in self.characters:
            actual = self.actual_is(player, actual_role)
            if self._role_can_flexibly_register_as_role(actual_role, role_ref):
                continue
            if actual_role == role_ref:
                self.add_implication(actual, result)
            else:
                self.add_implication(actual, result.Not())
        return result

    def add_truthful_info_claim(
        self,
        player: str,
        apparent_role: object,
        claim_truth: cp_model.IntVar,
        *,
        poison_context: str | None = None,
    ) -> None:
        apparent_role_ref = role_name(apparent_role)
        active_claimed_role = self.all_of(
            [
                self.actual_is(player, apparent_role_ref),
                self.poisoned(player, poison_context).Not(),
            ],
            f"{player}_{apparent_role_ref}_sober_healthy_claim",
        )
        self.add_implication(active_claimed_role, claim_truth)

    def neighbors(self, player: str) -> tuple[str, str]:
        self._check_player(player)
        index = self.seating.index(player)
        return (
            self.seating[(index - 1) % len(self.seating)],
            self.seating[(index + 1) % len(self.seating)],
        )

    def adjacent_pairs(self) -> list[tuple[str, str]]:
        return [
            (player, self.seating[(index + 1) % len(self.seating)])
            for index, player in enumerate(self.seating)
        ]

    def sits_next_to_evil(self, player: str) -> cp_model.IntVar:
        left, right = self.neighbors(player)
        return self.any_of(
            [self.is_evil(left), self.is_evil(right)],
            f"{player}_sits_next_to_evil",
        )

    def solve_all(
        self,
        *,
        limit: int | None = None,
        max_time_seconds: float | None = None,
    ) -> list[World]:
        solver = cp_model.CpSolver()
        solver.parameters.enumerate_all_solutions = True
        if max_time_seconds is not None:
            solver.parameters.max_time_in_seconds = max_time_seconds
        collector = _WorldCollector(self, limit)
        solver.solve(self.model, collector)
        return collector.worlds

    def _cached_player_predicate(
        self,
        predicate: str,
        player: str,
        literals: Sequence[cp_model.IntVar],
    ) -> cp_model.IntVar:
        self._check_player(player)
        key = (predicate, player)
        if key not in self._predicate_cache:
            self._predicate_cache[key] = self.bool_sum_equals(
                literals,
                1,
                f"{predicate}_{player}",
            )
        return self._predicate_cache[key]

    def _registers_as_alignment(
        self,
        player: str,
        alignment: Alignment,
        name: str,
    ) -> cp_model.IntVar:
        self._check_player(player)
        result = self.new_bool(f"{name}_{player}_registers_as_{alignment.value}")
        for role, character in self.characters.items():
            actual = self.actual_is(player, role)
            if self._role_can_flexibly_register_as_alignment(role):
                continue
            if role_alignment(character) == alignment:
                self.add_implication(actual, result)
            else:
                self.add_implication(actual, result.Not())
        return result

    def _role_can_flexibly_register_as_alignment(self, actual_role: str) -> bool:
        return actual_role in {"Spy", "Recluse"} and actual_role in self.characters

    def _role_can_flexibly_register_as_type(
        self,
        actual_role: str,
        character_type: CharacterType,
    ) -> bool:
        if actual_role == "Spy" and actual_role in self.characters:
            return character_type in {
                CharacterType.MINION,
                CharacterType.OUTSIDER,
                CharacterType.TOWNSFOLK,
            }
        if actual_role == "Recluse" and actual_role in self.characters:
            return character_type in {
                CharacterType.DEMON,
                CharacterType.MINION,
                CharacterType.OUTSIDER,
            }
        return False

    def _role_can_flexibly_register_as_role(
        self, actual_role: str, observed_role: str
    ) -> bool:
        observed_character = self.characters[observed_role]
        if actual_role == "Spy" and actual_role in self.characters:
            return observed_role == "Spy" or (
                role_alignment(observed_character) == Alignment.GOOD
                and role_character_type(observed_character)
                in {CharacterType.OUTSIDER, CharacterType.TOWNSFOLK}
            )
        if actual_role == "Recluse" and actual_role in self.characters:
            return observed_role == "Recluse" or (
                role_alignment(observed_character) == Alignment.EVIL
                and role_character_type(observed_character)
                in {CharacterType.DEMON, CharacterType.MINION}
            )
        return False
