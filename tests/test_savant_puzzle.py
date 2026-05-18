from importlib import import_module


solve = import_module("puzzles.01_sober_savant").solve


def test_savant_puzzle_has_unique_solution():
    worlds = solve()

    assert len(worlds) == 1
    world = worlds[0]
    assert world.holder("Demon") == "Anna"
    assert world.holder("Minion") == "Tim"
    assert world.holder("Drunk") == "Oscar"
