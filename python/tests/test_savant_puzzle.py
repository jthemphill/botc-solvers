from puzzles.puzzle_01_sober_savant import solve


def test_savant_puzzle_has_unique_solution():
    worlds = solve()

    assert len(worlds) == 1
    world = worlds[0]
    assert world.holder("Imp") == "Anna"
    assert world.holder("Scarlet Woman") == "Tim"
    assert world.holder("Drunk") == "Oscar"
