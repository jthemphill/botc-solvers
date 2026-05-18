from importlib import import_module


solve = import_module("puzzles.03b_not_throwing_away_my_shot").solve


def test_not_throwing_away_my_shot_3b_has_two_minion_candidates():
    worlds = solve()

    assert len(worlds) == 1