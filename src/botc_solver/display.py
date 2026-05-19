from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from typing import TextIO, cast

from botc_solver.core import role_name
from botc_solver.model import World


@dataclass(frozen=True)
class ForcedRole:
    label: str
    roles: tuple[str, ...]
    missing: str = "not forced"
    include_role: bool = False


ForcedRoleSpec = object


def forced_role(
    label: object,
    roles: object | Iterable[object] | None = None,
    *,
    missing: str = "not forced",
    include_role: bool = False,
) -> ForcedRole:
    label_name = role_name(label)
    if roles is None:
        role_names = (label_name,)
    elif isinstance(roles, str) or hasattr(roles, "role_name") or hasattr(roles, "name"):
        role_names = (role_name(roles),)
    else:
        role_names = tuple(role_name(role) for role in cast(Iterable[object], roles))

    if not role_names:
        raise ValueError("At least one role is required.")

    return ForcedRole(
        label=label_name,
        roles=role_names,
        missing=missing,
        include_role=include_role,
    )


def format_solution(
    worlds: Sequence[World],
    players: Iterable[str],
    *,
    forced_roles: Iterable[ForcedRoleSpec] = (),
    forced_missing: str = "not forced",
    poison_context: str | None = None,
) -> str:
    player_order = tuple(players)
    facts = tuple(_coerce_forced_role(role, forced_missing) for role in forced_roles)

    lines = [f"{len(worlds)} satisfying world(s)"]
    for index, world in enumerate(worlds, start=1):
        lines.append("")
        lines.append(f"World {index}")
        lines.extend(_format_world_lines(world, player_order, poison_context=poison_context))

    if facts:
        lines.append("")
        lines.append("Forced facts")
        for fact in facts:
            lines.append(f"  {_format_forced_role(worlds, fact)}")

    return "\n".join(lines)


def print_solution(
    worlds: Sequence[World],
    players: Iterable[str],
    *,
    forced_roles: Iterable[ForcedRoleSpec] = (),
    forced_missing: str = "not forced",
    poison_context: str | None = None,
    file: TextIO | None = None,
) -> None:
    print(
        format_solution(
            worlds,
            players,
            forced_roles=forced_roles,
            forced_missing=forced_missing,
            poison_context=poison_context,
        ),
        file=file,
    )


def _coerce_forced_role(role: ForcedRoleSpec, forced_missing: str) -> ForcedRole:
    if isinstance(role, ForcedRole):
        return role
    return forced_role(role, missing=forced_missing)


def _format_world_lines(
    world: World,
    players: Sequence[str],
    *,
    poison_context: str | None,
) -> list[str]:
    lines: list[str] = []
    for player in players:
        actual = world.actual_role(player)
        apparent = world.apparent.get(player)
        poison_suffix = " poisoned" if world.is_poisoned(player, poison_context) else ""
        if apparent and apparent != actual:
            lines.append(f"  {player}: {actual} (appears as {apparent}){poison_suffix}")
        else:
            lines.append(f"  {player}: {actual}{poison_suffix}")
    return lines


def _format_forced_role(worlds: Sequence[World], role: ForcedRole) -> str:
    assignment = _forced_assignment(worlds, role.roles)
    if assignment is None:
        return f"{role.label}: {role.missing}"

    holder, actual_role = assignment
    if role.include_role:
        return f"{role.label}: {holder} ({actual_role})"
    return f"{role.label}: {holder}"


def _forced_assignment(
    worlds: Sequence[World],
    roles: Sequence[str],
) -> tuple[str, str] | None:
    assignments = {_world_assignment(world, roles) for world in worlds}
    if len(assignments) != 1:
        return None

    return next(iter(assignments))


def _world_assignment(world: World, roles: Sequence[str]) -> tuple[str, str] | None:
    assignments = [
        (holder, role)
        for role in roles
        for holder in [world.holder(role)]
        if holder is not None
    ]
    if len(assignments) == 1:
        return assignments[0]
    return None
