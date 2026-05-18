from botc_solver import World, forced_role, format_solution


def test_format_solution_renders_worlds_and_forced_roles():
    worlds = [
        World(
            actual={"Alice": "Imp", "Bob": "Drunk"},
            apparent={"Alice": "Fortune Teller", "Bob": "Drunk"},
            poisoned=frozenset(),
            poisoned_by_context={"day_1": frozenset({"Bob"})},
            seating=("Alice", "Bob"),
        )
    ]

    result = format_solution(
        worlds,
        ["Alice", "Bob"],
        poison_context="day_1",
        forced_roles=[
            forced_role("Demon", "Imp", include_role=True),
            "Drunk",
        ],
    )

    assert result == (
        "1 satisfying world(s)\n"
        "\n"
        "World 1\n"
        "  Alice: Imp (appears as Fortune Teller)\n"
        "  Bob: Drunk poisoned\n"
        "\n"
        "Forced facts\n"
        "  Demon: Alice (Imp)\n"
        "  Drunk: Bob"
    )


def test_grouped_forced_role_must_match_holder_and_role_in_every_world():
    worlds = [
        World(
            actual={"Alice": "Baron", "Bob": "Imp"},
            apparent={},
            poisoned=frozenset(),
            seating=("Alice", "Bob"),
        ),
        World(
            actual={"Alice": "Spy", "Bob": "Imp"},
            apparent={},
            poisoned=frozenset(),
            seating=("Alice", "Bob"),
        ),
    ]

    result = format_solution(
        worlds,
        ["Alice", "Bob"],
        forced_roles=[
            forced_role("Demon", "Imp", include_role=True),
            forced_role(
                "Minion",
                ["Baron", "Spy"],
                missing="not settled",
                include_role=True,
            ),
        ],
    )

    assert result.endswith(
        "\n"
        "Forced facts\n"
        "  Demon: Bob (Imp)\n"
        "  Minion: not settled"
    )
