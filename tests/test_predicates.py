from collections import abc

from botc_solver import Alignment, BOTCModel, Character, CharacterType
from botc_solver.predicates import (
    chef_count_is,
    different_character_types,
    drunk_between_two_townsfolk,
    same_alignment,
    sits_next_to_evil,
)


TEST_CHARACTERS = (
    Character("Demon", Alignment.EVIL, CharacterType.DEMON),
    Character("Minion", Alignment.EVIL, CharacterType.MINION),
    Character("Drunk", Alignment.GOOD, CharacterType.OUTSIDER),
    Character("Investigator", Alignment.GOOD, CharacterType.TOWNSFOLK),
    Character("Noble", Alignment.GOOD, CharacterType.TOWNSFOLK),
)


def assert_satisfies(predicate_builder: abc.Callable[[], BOTCModel]):
    game = predicate_builder()
    assert len(game.solve_all(limit=1)) == 1


def test_drunk_apparent_role_is_not_in_play():
    def model():
        game = BOTCModel(["A", "B"], characters=TEST_CHARACTERS)
        game.fix_actual("A", "Drunk")
        game.set_apparent_role("A", "Investigator")
        game.fix_actual("B", "Demon")
        game.add_false(game.role_in_play("Investigator"))
        return game

    assert_satisfies(model)


def test_poisoned_actual_role_remains_in_play():
    def model():
        game = BOTCModel(["A", "B"], characters=TEST_CHARACTERS)
        game.fix_actual("A", "Investigator")
        game.fix_poisoned("A", True)
        game.fix_actual("B", "Demon")
        game.add_truth(game.role_in_play("Investigator"))
        return game

    assert_satisfies(model)


def test_seating_predicates():
    def model():
        game = BOTCModel(
            ["A", "B", "C", "D"],
            characters=TEST_CHARACTERS,
            seating=["A", "B", "C", "D"],
        )
        game.fix_actual("A", "Demon")
        game.fix_actual("B", "Minion")
        game.fix_actual("C", "Drunk")
        game.fix_actual("D", "Investigator")
        game.add_truth(chef_count_is(game, 1))
        game.add_truth(sits_next_to_evil(game, "C"))
        game.add_false(drunk_between_two_townsfolk(game))
        return game

    assert_satisfies(model)


def test_drunk_between_two_townsfolk():
    def model():
        game = BOTCModel(
            ["A", "B", "C", "D"],
            characters=TEST_CHARACTERS,
            seating=["A", "B", "C", "D"],
        )
        game.fix_actual("A", "Investigator")
        game.fix_actual("B", "Drunk")
        game.fix_actual("C", "Noble")
        game.fix_actual("D", "Demon")
        game.add_truth(drunk_between_two_townsfolk(game))
        return game

    assert_satisfies(model)


def test_alignment_and_character_type_predicates():
    def model():
        game = BOTCModel(
            ["A", "B", "C"],
            characters=TEST_CHARACTERS,
            seating=["A", "B", "C"],
        )
        game.fix_actual("A", "Demon")
        game.fix_actual("B", "Minion")
        game.fix_actual("C", "Drunk")
        game.add_truth(same_alignment(game, "A", "B"))
        game.add_truth(different_character_types(game, "A", "B"))
        game.add_truth(different_character_types(game, "A", "C"))
        return game

    assert_satisfies(model)
