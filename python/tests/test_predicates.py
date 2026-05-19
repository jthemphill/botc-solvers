from collections import abc

from botc_solver import BOTCModel, CharacterType, RoleClaim
from botc_solver.characters import (
    Chef,
    Drunk,
    Imp,
    Investigator,
    Librarian,
    Noble,
    Poisoner,
    Recluse,
    ScarletWoman,
    Spy,
    script,
)
from botc_solver.predicates import (
    chef_count_is,
    chef_count_registers_as,
    different_character_types,
    drunk_between_two_townsfolk,
    registers_as_role_among,
    same_alignment,
    sits_next_to_evil,
)

TEST_CHARACTERS = script(
    Imp,
    ScarletWoman,
    Drunk,
    Recluse,
    Investigator,
    Noble,
)
POISON_CHARACTERS = script(
    Imp,
    Poisoner,
    Investigator,
)
REGISTRATION_CHARACTERS = script(
    Imp,
    Spy,
    Poisoner,
    Drunk,
    Recluse,
    Chef,
    Librarian,
)


def assert_satisfies(predicate_builder: abc.Callable[[], BOTCModel]):
    game = predicate_builder()
    assert len(game.solve_all(limit=1)) == 1


def test_drunk_apparent_role_is_not_in_play():
    def model():
        game = BOTCModel(["A", "B"], characters=TEST_CHARACTERS)
        game.fix_actual("A", "Drunk")
        game.set_apparent_role("A", "Investigator")
        game.fix_actual("B", "Imp")
        game.add_false(game.role_in_play("Investigator"))
        return game

    assert_satisfies(model)


def test_poisoned_actual_role_remains_in_play():
    def model():
        game = BOTCModel(["A", "B"], characters=TEST_CHARACTERS)
        game.fix_actual("A", "Investigator")
        game.fix_poisoned("A", True)
        game.fix_actual("B", "Imp")
        game.add_truth(game.role_in_play("Investigator"))
        return game

    assert_satisfies(model)


def test_drunk_can_think_they_are_a_townsfolk():
    game = BOTCModel(["A", "B"], characters=TEST_CHARACTERS)
    game.add_role_claim(RoleClaim("A", "Investigator"))
    game.fix_actual("A", "Drunk")
    game.fix_actual("B", "Imp")

    assert len(game.solve_all(limit=1)) == 1


def test_role_claim_defaults_to_model_evil_roles():
    game = BOTCModel(["A", "B"], characters=TEST_CHARACTERS)
    game.add_role_claim(RoleClaim("A", Investigator))
    game.fix_actual("A", ScarletWoman)
    game.fix_actual("B", Imp)

    assert len(game.solve_all(limit=1)) == 1


def test_drunk_cannot_think_they_are_an_outsider():
    game = BOTCModel(["A", "B"], characters=TEST_CHARACTERS)
    game.add_role_claim(RoleClaim("A", "Recluse"))
    game.fix_actual("A", "Drunk")
    game.fix_actual("B", "Imp")

    assert game.solve_all(limit=1) == []


def test_poisoning_is_scoped_to_a_context():
    game = BOTCModel(["A", "B", "C"], characters=POISON_CHARACTERS)
    game.fix_actual("A", "Poisoner")
    game.fix_actual("B", "Imp")
    game.fix_actual("C", "Investigator")
    game.add_poisoner_effect("day_1")
    game.add_poisoner_effect("day_2")
    game.fix_poisoned("B", True, "day_1")
    game.fix_poisoned("C", True, "day_2")

    worlds = game.solve_all()

    assert len(worlds) == 1
    world = worlds[0]
    assert world.is_poisoned("B", "day_1")
    assert not world.is_poisoned("B", "day_2")
    assert world.is_poisoned("C", "day_2")
    assert not world.is_poisoned("C", "day_1")
    assert not world.is_poisoned("B")


def test_poisoner_effect_can_be_disabled_when_poisoner_is_inactive():
    game = BOTCModel(["A", "B", "C"], characters=POISON_CHARACTERS)
    game.fix_actual("A", "Poisoner")
    game.fix_actual("B", "Imp")
    game.fix_actual("C", "Investigator")
    game.add_poisoner_effect("day_2", active_if=False)
    game.add_truth(game.poisoned("B", "day_2"))

    assert game.solve_all(limit=1) == []


def test_truthful_claim_uses_matching_poison_context():
    game = BOTCModel(["A", "B", "C"], characters=POISON_CHARACTERS)
    game.fix_actual("A", "Investigator")
    game.fix_actual("B", "Imp")
    game.fix_actual("C", "Poisoner")
    false_claim = game.actual_is("B", "Investigator")
    game.fix_poisoned("A", True, "day_1")
    game.fix_poisoned("A", False, "day_2")
    game.add_truthful_info_claim(
        "A", "Investigator", false_claim, poison_context="day_2"
    )

    assert game.solve_all(limit=1) == []


def test_spy_can_register_as_drunk_without_actual_drunk():
    game = BOTCModel(["A", "B"], characters=REGISTRATION_CHARACTERS)
    game.fix_actual("A", "Spy")
    game.fix_actual("B", "Imp")
    game.add_truth(game.registers_as_role("A", "Drunk", "librarian"))
    game.add_false(game.role_in_play("Drunk"))

    worlds = game.solve_all()

    assert len(worlds) == 1
    assert worlds[0].holder("Spy") == "A"
    assert worlds[0].holder("Drunk") is None


def test_spy_can_register_as_not_evil_for_chef():
    game = BOTCModel(
        ["A", "B", "C"],
        characters=REGISTRATION_CHARACTERS,
        seating=["A", "B", "C"],
    )
    game.fix_actual("A", "Imp")
    game.fix_actual("B", "Spy")
    game.fix_actual("C", "Chef")
    game.add_truth(chef_count_registers_as(game, 0, "chef"))

    worlds = game.solve_all()

    assert len(worlds) == 1
    assert worlds[0].holder("Spy") == "B"


def test_registers_as_role_among_allows_flexible_registration():
    game = BOTCModel(["A", "B", "C"], characters=REGISTRATION_CHARACTERS)
    game.fix_actual("A", "Recluse")
    game.fix_actual("B", "Chef")
    game.fix_actual("C", "Librarian")
    game.add_truth(registers_as_role_among(game, ["A", "B"], "Imp", "investigator"))
    game.add_false(game.role_in_play("Imp"))

    worlds = game.solve_all()

    assert len(worlds) == 1
    assert worlds[0].holder("Recluse") == "A"
    assert worlds[0].holder("Imp") is None


def test_registration_does_not_change_actual_counts_or_role_in_play():
    game = BOTCModel(["A", "B", "C"], characters=REGISTRATION_CHARACTERS)
    game.fix_actual("A", "Spy")
    game.fix_actual("B", "Imp")
    game.fix_actual("C", "Chef")
    game.add_truth(game.registers_as_role("A", "Drunk", "librarian"))
    game.add_false(game.role_in_play("Drunk"))
    game.add_truth(game.role_in_play("Spy"))
    game.model.add(sum(game.is_minion(player) for player in game.players) == 1)

    assert len(game.solve_all()) == 1


def test_solve_all_deduplicates_registration_only_differences():
    game = BOTCModel(["A", "B"], characters=REGISTRATION_CHARACTERS)
    game.fix_actual("A", "Spy")
    game.fix_actual("B", "Imp")
    drunk_registration = game.registers_as_role("A", "Drunk", "librarian")
    chef_registration = game.registers_as_role("A", "Chef", "washerwoman")
    game.add_truth(
        game.any_of(
            [drunk_registration, chef_registration],
            "at_least_one_registration_choice",
        )
    )

    worlds = game.solve_all()

    assert len(worlds) == 1
    assert worlds[0].holder("Spy") == "A"


def test_seating_predicates():
    def model():
        game = BOTCModel(
            ["A", "B", "C", "D"],
            characters=TEST_CHARACTERS,
            seating=["A", "B", "C", "D"],
        )
        game.fix_actual("A", "Imp")
        game.fix_actual("B", "Scarlet Woman")
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
        game.fix_actual("D", "Imp")
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
        game.fix_actual("A", "Imp")
        game.fix_actual("B", "Scarlet Woman")
        game.fix_actual("C", "Drunk")
        game.add_truth(same_alignment(game, "A", "B"))
        game.add_truth(different_character_types(game, "A", "B"))
        game.add_truth(different_character_types(game, "A", "C"))
        return game

    assert_satisfies(model)
