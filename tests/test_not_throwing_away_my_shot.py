from importlib import import_module


solve = import_module("puzzles.03a_not_throwing_away_my_shot").solve


def test_not_throwing_away_my_shot_has_unique_solution():
    worlds = solve()

    assert len(worlds) == 1
    world = worlds[0]
    assert world.holder("Imp") == "Matthew"
    assert world.holder("Baron") == "Aoife"
    assert world.holder("Drunk") == "Oscar"
    assert world.holder("Recluse") == "Tom"
