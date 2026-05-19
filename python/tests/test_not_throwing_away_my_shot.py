from puzzles.puzzle_03a_not_throwing_away_my_shot import solve


def test_not_throwing_away_my_shot_has_unique_solution():
    worlds = solve()

    assert len(worlds) == 1
    world = worlds[0]
    assert world.holder("Imp") == "Matthew"
    assert world.holder("Baron") == "Aoife"
    assert world.holder("Drunk") == "Oscar"
    assert world.holder("Recluse") == "Tom"
