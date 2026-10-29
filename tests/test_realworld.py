"""Real-world task oracles and Lean goal rendering; no Docker, network or model calls.

The documented outputs of the buggy releases must break exactly the requirements their issues
describe, and the outputs of the proved component must meet every requirement.

Run: python3 tests/test_realworld.py
"""
import pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "eval")]
import realworld, task as taskmod  # noqa: E402

T = {name: taskmod.load(ROOT / "realworld/tasks" / name)
     for name in ("rw-spliit-balances", "rw-gomoney-split", "rw-moneyphp-allocate")}


def ids(v):
    return sorted({rid for rid, _ in v})


def test_documented_outputs_break_the_reported_requirements():
    a = T["rw-spliit-balances"].oracle
    assert ids(a.violations(100, [1, 1, 1], [33, 33, 33])) == ["REQ-CONSERVATION"]          # Spliit #374
    m = T["rw-moneyphp-allocate"].oracle
    assert "REQ-ZERO-RATIO" in ids(m.violations(5, [0, 7, 3], [1, 3, 1]))                   # moneyphp #436
    assert ids(m.violations(1, [1, 1], None)) == ["REQ-VALID-SUCCEEDS"]                     # moneyphp #466
    assert ids(m.violations(9999, [75, 25], [7500, 2499])) == ["REQ-LARGEST-REMAINDER"]     # moneyphp #492
    g = T["rw-gomoney-split"].oracle
    assert ids(g.violations(-101, 4, None)) == ["REQ-VALID-SUCCEEDS"]                       # go-money #94
    assert ids(g.violations(-2, 3, [1, 1, 0])) == ["REQ-CONSERVATION", "REQ-SIGN", "REQ-WITHIN-ONE-UNIT"]  # #106


def test_proved_outputs_meet_every_requirement():
    a = T["rw-spliit-balances"].oracle
    for amount, ratios, shares in [(100, [1, 1, 1], [34, 33, 33]), (9999, [75, 25], [7499, 2500]),
                                   (5, [0, 7, 3], [0, 4, 1]), (1, [1, 1], [1, 0]), (-2, [1, 1, 1], [0, -1, -1])]:
        assert a.violations(amount, ratios, shares) == [], (amount, ratios, shares)
    assert a.violations(7, [], None) == [] and a.violations(7, [0, 0], None) == []
    g = T["rw-gomoney-split"].oracle
    assert g.violations(-2, 3, [-1, -1, 0]) == [] and g.violations(-101, 4, [-26, -25, -25, -25]) == []
    assert g.violations(5, 0, None) == []


def test_lean_goals_name_the_matching_predicate():
    a, g = T["rw-spliit-balances"], T["rw-gomoney-split"]
    assert realworld.goal(a, {"amount": 100, "ratios": [1, 1, 1]}, [33, 33, 33], "REQ-CONSERVATION") \
        == "¬ ConservesOn 100 [33, 33, 33]"
    assert realworld.goal(a, {"amount": 1, "ratios": [1, 1]}, None, "REQ-VALID-SUCCEEDS") == "Valid 1 [1, 1]"
    assert realworld.goal(g, {"amount": -2, "n": 3}, [1, 1, 0], "REQ-SIGN") == "¬ SignOn (-2) [1, 1, 0]"


def test_generators_stay_in_each_library_domain():
    import random
    rng = random.Random(0)
    for _ in range(500):
        s = realworld.spliit_case(rng)
        assert s["ratios"] and all(r >= 1 for r in s["ratios"])
        m = realworld.moneyphp_case(rng)
        assert m["ratios"] and sum(m["ratios"]) > 0 and all(r >= 0 for r in m["ratios"])
        assert realworld.gomoney_case(rng)["n"] >= 1
        r = realworld.rubymoney_case(rng)
        assert sum(r["ratios"]) > 0 and 0 <= r["scale"] <= 4


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
