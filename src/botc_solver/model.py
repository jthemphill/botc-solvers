from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from typing import Protocol, cast

from ortools.sat.python import cp_model

from botc_solver.core import Alignment, Character, CharacterType, RoleClaim


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

    def holder(self, role: str) -> str | None:
        holders = [player for player, actual_role in self.actual.items() if actual_role == role]
        if len(holders) == 1:
            return holders[0]
        return None

    def actual_role(self, player: str) -> str:
        return self.actual[player]

    def is_poisoned(self, player: str) -> bool:
        return player in self.poisoned


def forced_role_holders(worlds: Sequence[World], roles: Iterable[str]) -> dict[str, str | None]:
    summary: dict[str, str | None] = {}
    for role in roles:
        holders = {world.holder(role) for world in worlds}
        summary[role] = next(iter(holders)) if len(holders) == 1 else None
    return summary


class _WorldCollector(cp_model.CpSolverSolutionCallback):
    def __init__(self, game: BOTCModel, limit: int | None) -> None:
        super().__init__()
        self._game = game
        self._limit = limit
        self.worlds: list[World] = []

    def on_solution_callback(self) -> None:
        actual: dict[str, str] = {}
        for player in self._game.players:
            matching = [
                role
                for role in self._game.characters
                if self.value(self._game.actual_is(player, role))
            ]
            if len(matching) != 1:
                raise RuntimeError(f"Expected exactly one actual character for {player}.")
            actual[player] = matching[0]

        poisoned = frozenset(
            player for player in self._game.players if self.value(self._game.poisoned(player))
        )
        self.worlds.append(
            World(
                actual=actual,
                apparent=dict(self._game.apparent_roles),
                poisoned=poisoned,
                seating=tuple(self._game.seating),
            )
        )
        if self._limit is not None and len(self.worlds) >= self._limit:
            self.stop_search()


class BOTCModel:
    def __init__(
        self,
        players: Sequence[str],
        *,
        characters: Sequence[Character],
        seating: Sequence[str] | None = None,
        unique_characters: bool = True,
    ) -> None:
        if not players:
            raise ValueError("At least one player is required.")

        self.players = list(players)
        if len(set(self.players)) != len(self.players):
            raise ValueError("Player names must be unique.")

        self.seating = list(seating or players)
        if len(self.seating) != len(self.players) or set(self.players) != set(self.seating):
            raise ValueError("Seating must contain exactly the model players.")

        self.characters = {character.name: character for character in characters}
        if len(self.characters) != len(characters):
            raise ValueError("Character names must be unique.")

        self.model: cp_model.CpModel = cp_model.CpModel()
        self.apparent_roles: dict[str, str] = {}
        self._counter = 0
        self._actual = {
            (player, role): self.model.new_bool_var(f"{_slug(player)}__actual__{_slug(role)}")
            for player in self.players
            for role in self.characters
        }
        self._poisoned = {
            player: self.model.new_bool_var(f"{_slug(player)}__poisoned")
            for player in self.players
        }
        self._predicate_cache: dict[tuple[str, str], cp_model.IntVar] = {}

        for player in self.players:
            self.model.add_exactly_one(self.actual_is(player, role) for role in self.characters)

        if unique_characters:
            for role in self.characters:
                self.model.add_at_most_one(self.actual_is(player, role) for player in self.players)

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

    def actual_is(self, player: str, role: str) -> cp_model.IntVar:
        self._check_player(player)
        self._check_role(role)
        return self._actual[(player, role)]

    def poisoned(self, player: str) -> cp_model.IntVar:
        self._check_player(player)
        return self._poisoned[player]

    def set_apparent_role(self, player: str, role: str) -> None:
        self._check_player(player)
        self._check_role(role)
        self.apparent_roles[player] = role

    def add_role_claim(
        self,
        claim: RoleClaim,
        *,
        evil_roles: Sequence[str] = ("Demon", "Minion"),
        drunk_role: str = "Drunk",
    ) -> None:
        self.set_apparent_role(claim.player, claim.apparent_role)
        self.set_possible_actual_roles(
            claim.player,
            [claim.apparent_role, *evil_roles, drunk_role],
        )

    def set_possible_actual_roles(self, player: str, roles: Iterable[str]) -> None:
        self._check_player(player)
        allowed = set(roles)
        for role in allowed:
            self._check_role(role)
        for role in self.characters:
            if role not in allowed:
                self.add_false(self.actual_is(player, role))

    def fix_actual(self, player: str, role: str) -> None:
        self.add_truth(self.actual_is(player, role))

    def fix_not_actual(self, player: str, role: str) -> None:
        self.add_false(self.actual_is(player, role))

    def fix_poisoned(self, player: str, value: bool) -> None:
        self.model.add(self.poisoned(player) == int(value))

    def set_character_count(self, role: str, count: int) -> None:
        self._check_role(role)
        self.model.add(sum(self.actual_is(player, role) for player in self.players) == count)

    def add_truth(self, literal: cp_model.IntVar) -> None:
        self.model.add_bool_or([literal])

    def add_false(self, literal: cp_model.IntVar) -> None:
        self.model.add_bool_or([literal.Not()])

    def add_implication(self, condition: cp_model.IntVar, conclusion: cp_model.IntVar) -> None:
        self.model.add_implication(condition, conclusion)

    def add_exactly_one(self, literals: Iterable[cp_model.IntVar]) -> None:
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

    def all_of(self, literals: Iterable[cp_model.IntVar], name: str) -> cp_model.IntVar:
        literals = list(literals)
        if not literals:
            return self.constant_bool(True, name)
        result = self.new_bool(name)
        _only_enforce_if(self.model.add_bool_and(literals), result)
        _only_enforce_if(self.model.add_bool_or([literal.Not() for literal in literals]), result.Not())
        return result

    def any_of(self, literals: Iterable[cp_model.IntVar], name: str) -> cp_model.IntVar:
        literals = list(literals)
        if not literals:
            return self.constant_bool(False, name)
        result = self.new_bool(name)
        _only_enforce_if(self.model.add_bool_or(literals), result)
        _only_enforce_if(self.model.add_bool_and([literal.Not() for literal in literals]), result.Not())
        return result

    def not_(self, literal: cp_model.IntVar, name: str) -> cp_model.IntVar:
        result = self.new_bool(name)
        self.model.add(result + literal == 1)
        return result

    def xor(self, left: cp_model.IntVar, right: cp_model.IntVar, name: str) -> cp_model.IntVar:
        return self.bool_sum_equals([left, right], 1, name)

    def is_evil(self, player: str) -> cp_model.IntVar:
        return self._cached_player_predicate(
            "is_evil",
            player,
            [
                self.actual_is(player, role)
                for role, character in self.characters.items()
                if character.alignment == Alignment.EVIL
            ],
        )

    def is_good(self, player: str) -> cp_model.IntVar:
        return self._cached_player_predicate(
            "is_good",
            player,
            [
                self.actual_is(player, role)
                for role, character in self.characters.items()
                if character.alignment == Alignment.GOOD
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
                if character.character_type == character_type
            ],
        )

    def is_demon(self, player: str) -> cp_model.IntVar:
        return self._cached_player_predicate(
            "is_demon",
            player,
            [
                self.actual_is(player, role)
                for role, character in self.characters.items()
                if character.character_type == CharacterType.DEMON
            ],
        )

    def is_minion(self, player: str) -> cp_model.IntVar:
        return self._cached_player_predicate(
            "is_minion",
            player,
            [
                self.actual_is(player, role)
                for role, character in self.characters.items()
                if character.character_type == CharacterType.MINION
            ],
        )

    def role_in_play(self, role: str) -> cp_model.IntVar:
        self._check_role(role)
        key = ("role_in_play", role)
        if key not in self._predicate_cache:
            self._predicate_cache[key] = self.any_of(
                [self.actual_is(player, role) for player in self.players],
                f"{role}_in_play",
            )
        return self._predicate_cache[key]

    def add_truthful_info_claim(
        self,
        player: str,
        apparent_role: str,
        claim_truth: cp_model.IntVar,
    ) -> None:
        active_claimed_role = self.all_of(
            [
                self.actual_is(player, apparent_role),
                self.poisoned(player).Not(),
            ],
            f"{player}_{apparent_role}_sober_healthy_claim",
        )
        self.add_implication(active_claimed_role, claim_truth)

    def neighbors(self, player: str) -> tuple[str, str]:
        self._check_player(player)
        index = self.seating.index(player)
        return self.seating[(index - 1) % len(self.seating)], self.seating[(index + 1) % len(self.seating)]

    def adjacent_pairs(self) -> list[tuple[str, str]]:
        return [
            (player, self.seating[(index + 1) % len(self.seating)])
            for index, player in enumerate(self.seating)
        ]

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
