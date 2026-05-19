from puzzles.puzzle_02_come_fly_with_me import solve


def test_come_fly_with_me_has_unique_solution():
    worlds = solve()

    assert len(worlds) == 1
    world = worlds[0]
    assert world.holder("Goblin") == "Sarah"
    assert world.holder("Leviathan") == "Matthew"
    assert world.holder("Drunk") == "You"
