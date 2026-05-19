from puzzles.puzzle_04_the_many_headed_monster import MINION_ROLES, solve


def test_many_headed_monster_forces_demon_and_minion_team():
    worlds = solve()

    assert worlds
    assert {world.holder("Lord of Typhon") for world in worlds} == {"Fraser"}
    assert {
        frozenset(
            player
            for role in MINION_ROLES
            for player in [world.holder(role)]
            if player is not None
        )
        for world in worlds
    } == {frozenset({"Sarah", "Dan"})}


def test_many_headed_monster_leaves_minion_roles_ambiguous():
    worlds = solve()

    assert {
        (world.holder("Marionette"), world.holder("Poisoner"))
        for world in worlds
    } == {
        ("Sarah", "Dan"),
        ("Dan", "Sarah"),
    }
