from botc_solver import BOTCModel
from botc_solver.characters import (
    Chef,
    Drunk,
    Empath,
    Imp,
    Investigator,
    Juggler,
    Recluse,
    Savant,
    ScarletWoman,
    apply_claims,
    player_names,
    script,
)


CLAIM_CHARACTERS = script(Imp, ScarletWoman, Drunk, Recluse, Investigator)


def test_role_classes_work_in_scripts_and_low_level_apis():
    game = BOTCModel(["A", "B"], characters=CLAIM_CHARACTERS)

    game.set_character_count(Imp, 1)
    game.fix_actual("A", Investigator)
    game.add_truth(game.role_in_play(Investigator))
    game.set_possible_actual_roles("B", [Imp, ScarletWoman])

    worlds = game.solve_all()

    assert len(worlds) == 1
    assert worlds[0].holder(Investigator) == "A"
    assert worlds[0].holder(Imp) == "B"


def test_character_claim_constrains_possible_actual_roles():
    game = BOTCModel(["A", "B"], characters=CLAIM_CHARACTERS)

    Investigator.claim(game, "A")
    game.fix_actual("A", "Recluse")
    game.fix_actual("B", "Imp")

    assert game.solve_all(limit=1) == []


def test_title_case_claim_objects_apply_claims():
    claims = [
        Investigator(
            name="A",
            minion_role=ScarletWoman,
            among=["B"],
        )
    ]
    game = BOTCModel(player_names([*claims, "B"]), characters=CLAIM_CHARACTERS)

    apply_claims(game, claims)
    game.fix_actual("A", "Investigator")
    game.fix_actual("B", "Scarlet Woman")
    game.fix_poisoned("A", False)

    assert len(game.solve_all()) == 1


def test_character_claim_with_learned_info_applies_when_sober_healthy():
    game = BOTCModel(["A", "B", "C"], characters=CLAIM_CHARACTERS)
    learned = game.actual_is("B", ScarletWoman)

    Investigator.claim(game, "A", learned=learned)
    game.fix_actual("A", Investigator)
    game.fix_actual("B", Imp)
    game.fix_actual("C", ScarletWoman)
    game.fix_poisoned("A", False)

    assert game.solve_all(limit=1) == []


def test_character_claim_uses_matching_poison_context():
    poisoned_in_claim_context = BOTCModel(["A", "B", "C"], characters=CLAIM_CHARACTERS)
    learned = poisoned_in_claim_context.actual_is("B", ScarletWoman)
    Investigator.claim(
        poisoned_in_claim_context,
        "A",
        learned=learned,
        poison_context="night_1",
    )
    poisoned_in_claim_context.fix_actual("A", Investigator)
    poisoned_in_claim_context.fix_actual("B", Imp)
    poisoned_in_claim_context.fix_actual("C", ScarletWoman)
    poisoned_in_claim_context.fix_poisoned("A", True, "night_1")
    poisoned_in_claim_context.fix_poisoned("A", False, "night_2")

    assert len(poisoned_in_claim_context.solve_all(limit=1)) == 1

    sober_in_claim_context = BOTCModel(["A", "B", "C"], characters=CLAIM_CHARACTERS)
    learned = sober_in_claim_context.actual_is("B", ScarletWoman)
    Investigator.claim(
        sober_in_claim_context,
        "A",
        learned=learned,
        poison_context="night_2",
    )
    sober_in_claim_context.fix_actual("A", Investigator)
    sober_in_claim_context.fix_actual("B", Imp)
    sober_in_claim_context.fix_actual("C", ScarletWoman)
    sober_in_claim_context.fix_poisoned("A", True, "night_1")
    sober_in_claim_context.fix_poisoned("A", False, "night_2")

    assert sober_in_claim_context.solve_all(limit=1) == []


def test_role_among_helper_uses_registration_by_default():
    game = BOTCModel(["A", "B", "C"], characters=script(Imp, Drunk, Recluse, Investigator))

    game.fix_actual("A", Recluse)
    game.fix_actual("B", Investigator)
    game.fix_actual("C", Drunk)
    game.add_false(game.role_in_play(Imp))
    game.add_truth(Investigator.learns_role_among(game, ["A"], Imp, "investigator"))

    assert len(game.solve_all()) == 1


def test_chef_and_empath_count_helpers():
    game = BOTCModel(
        ["A", "B", "C", "D"],
        characters=script(Imp, ScarletWoman, Chef, Empath),
        seating=["A", "B", "C", "D"],
    )

    game.fix_actual("A", Imp)
    game.fix_actual("B", ScarletWoman)
    game.fix_actual("C", Chef)
    game.fix_actual("D", Empath)
    game.add_truth(Chef.learns_count(game, 1, "chef"))
    game.add_truth(Empath.learns_count(game, "D", 1, "empath"))

    assert len(game.solve_all()) == 1


def test_juggler_and_savant_count_helpers():
    game = BOTCModel(["A", "B", "C"], characters=script(Imp, Drunk, Juggler, Savant))

    game.fix_actual("A", Juggler)
    game.fix_actual("B", Imp)
    game.fix_actual("C", Drunk)
    game.add_truth(
        Juggler.learns_correct_count(
            game,
            {"B": Imp, "C": Imp},
            1,
            "juggler_one_correct",
        )
    )
    game.add_truth(
        Savant.learns_exactly_one(
            game,
            [game.actual_is("B", Imp), game.actual_is("C", Imp)],
            "savant_one_true_statement",
        )
    )

    assert len(game.solve_all()) == 1


def test_savant_claim_statement_tuple_means_exactly_one():
    claims = [
        Savant(
            name="A",
            statements=[
                lambda game: (game.actual_is("B", Imp), game.actual_is("C", Imp)),
            ],
        )
    ]
    game = BOTCModel(
        ["A", "B", "C"],
        characters=script(Imp, Drunk, Savant),
        unique_characters=False,
    )

    apply_claims(game, claims)
    game.fix_actual("A", Savant)
    game.fix_actual("B", Imp)
    game.fix_actual("C", Imp)
    game.fix_poisoned("A", False)

    assert game.solve_all(limit=1) == []
