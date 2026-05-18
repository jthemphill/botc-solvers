from __future__ import annotations

from collections.abc import Sequence

from ortools.sat.python import cp_model

from botc_solver.model import BOTCModel


def exactly_n_evil(game: BOTCModel, players: Sequence[str], count: int) -> cp_model.IntVar:
    return game.bool_sum_equals(
        [game.is_evil(player) for player in players],
        count,
        f"exactly_{count}_evil_among_{'_'.join(players)}",
    )


def different_alignments(game: BOTCModel, left: str, right: str) -> cp_model.IntVar:
    return game.xor(game.is_evil(left), game.is_evil(right), f"{left}_{right}_different_alignments")


def same_alignment(game: BOTCModel, left: str, right: str) -> cp_model.IntVar:
    return game.not_(
        different_alignments(game, left, right),
        f"{left}_{right}_same_alignment",
    )


def different_character_types(game: BOTCModel, left: str, right: str) -> cp_model.IntVar:
    same_type_options: list[cp_model.IntVar] = []
    for character_type in {character.character_type for character in game.characters.values()}:
        same_type_options.append(
            game.all_of(
                [
                    game.has_character_type(left, character_type),
                    game.has_character_type(right, character_type),
                ],
                f"{left}_{right}_both_{character_type.value}",
            )
        )
    return game.not_(
        game.any_of(same_type_options, f"{left}_{right}_same_character_type"),
        f"{left}_{right}_different_character_types",
    )


def chef_count_is(game: BOTCModel, count: int) -> cp_model.IntVar:
    evil_pairs = [
        game.all_of([game.is_evil(left), game.is_evil(right)], f"{left}_{right}_evil_pair")
        for left, right in game.adjacent_pairs()
    ]
    return game.bool_sum_equals(evil_pairs, count, f"chef_count_is_{count}")


def chef_count_registers_as(game: BOTCModel, count: int, name: str) -> cp_model.IntVar:
    registers_as_evil = {
        player: game.registers_as_evil(player, name)
        for player in game.players
    }
    evil_pairs = [
        game.all_of(
            [registers_as_evil[left], registers_as_evil[right]],
            f"{name}_{left}_{right}_evil_pair",
        )
        for left, right in game.adjacent_pairs()
    ]
    return game.bool_sum_equals(evil_pairs, count, f"{name}_chef_count_is_{count}")


def registers_as_role_among(
    game: BOTCModel,
    players: Sequence[str],
    role: str,
    name: str,
) -> cp_model.IntVar:
    return game.any_of(
        [game.registers_as_role(player, role, name) for player in players],
        f"{name}_{'_'.join(players)}_registers_as_{role}",
    )


def sits_next_to_evil(game: BOTCModel, player: str) -> cp_model.IntVar:
    left, right = game.neighbors(player)
    return game.any_of(
        [game.is_evil(left), game.is_evil(right)],
        f"{player}_sits_next_to_evil",
    )


def drunk_between_two_townsfolk(game: BOTCModel) -> cp_model.IntVar:
    possibilities: list[cp_model.IntVar] = []
    for player in game.players:
        left, right = game.neighbors(player)
        possibilities.append(
            game.all_of(
                [
                    game.actual_is(player, "Drunk"),
                    game.is_townsfolk(left),
                    game.is_townsfolk(right),
                ],
                f"{player}_drunk_between_two_townsfolk",
            )
        )
    return game.any_of(possibilities, "drunk_between_two_townsfolk")
