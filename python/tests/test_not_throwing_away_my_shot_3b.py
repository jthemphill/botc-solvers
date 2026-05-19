from puzzles.puzzle_03b_not_throwing_away_my_shot import solve


def test_not_throwing_away_my_shot_3b_has_one_solution():
    worlds = solve()

    assert len(worlds) == 1
    for world in worlds:
        assert world.holder("Spy") == "Hannah"
        assert world.holder("Imp") == "Sarah"
        assert world.holder("Drunk") is None
