"""rw-cetus-shlw: oracle, Move test rendering and parsing, Lean goal rendering; no Docker,
network, Sui CLI or model calls.

The documented outputs of the original checked_shlw and of the pull request 6 fix must break
exactly the requirements described in the task, and the outputs of the pull request 7 fix must
meet every requirement.

Run: python3 tests/test_cetus.py
"""
import pathlib, random, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "eval")]
import realworld_cetus as rc, task as taskmod  # noqa: E402

T = taskmod.load(ROOT / "realworld/tasks/rw-cetus-shlw")
O = T.oracle
A = rc.ATTACK
N_ATTACK = A["liquidity"] * (A["sqrt_price_1"] - A["sqrt_price_0"])


def shlw_original(n):
    return (0, True) if n > (2 ** 64 - 1) << 192 else ((n << 64) % 2 ** 256, False)


def shlw_pr6(n):
    return (0, True) if n > 1 << 192 else ((n << 64) % 2 ** 256, False)


def shlw_pr7(n):
    return (0, True) if n >= 1 << 192 else ((n << 64) % 2 ** 256, False)


def ids(v):
    return sorted({rid for rid, _ in v})


def test_attack_values():
    assert N_ATTACK.bit_length() == 193 and N_ATTACK - 2 ** 192 == 491983144293873864340816
    num = shlw_original(N_ATTACK)[0]
    den = A["sqrt_price_0"] * A["sqrt_price_1"]
    assert -(-num // den) == 1                                    # the attack pays 1 unit
    assert -(-(N_ATTACK << 64) // den) == 31572840708638430117170542


def test_documented_outputs_break_the_reported_requirements():
    assert ids(O.delta_a_violations(A["sqrt_price_0"], A["sqrt_price_1"], A["liquidity"], True, 1)) \
        == ["REQ-DELTA-A-COVERS"]
    assert ids(O.shlw_violations(N_ATTACK, *shlw_original(N_ATTACK))) == ["REQ-SHLW-EXACT"]
    assert ids(O.shlw_violations(2 ** 192, *shlw_pr6(2 ** 192))) == ["REQ-SHLW-EXACT"]
    assert O.shlw_violations(N_ATTACK, *shlw_pr6(N_ATTACK)) == []     # pull request 6 refuses the attack
    assert ids(O.shlw_violations(2 ** 191, 0, True)) == ["REQ-SHLW-COMPLETE"]


def test_fixed_outputs_meet_every_requirement():
    rng = random.Random(1)
    for _ in range(3000):
        c = O.gen_case(rng)
        if c["op"] == "shlw":
            assert O.shlw_violations(c["n"], *shlw_pr7(c["n"])) == [], c
    for n in O.SHLW_BOUNDARY:
        assert O.shlw_violations(n, *shlw_pr7(n)) == []
    assert O.delta_a_violations(A["sqrt_price_0"], A["sqrt_price_1"], 10 ** 18, True, 3045910951) == []
    assert O.delta_a_violations(A["sqrt_price_0"], A["sqrt_price_1"], 10 ** 18, False, 3045910950) == []
    assert O.delta_a_violations(A["sqrt_price_0"], A["sqrt_price_1"], A["liquidity"], True, None) == []


def test_generator_stays_in_the_move_types():
    rng = random.Random(0)
    for _ in range(2000):
        c = O.gen_case(rng)
        if c["op"] == "shlw":
            assert 0 <= c["n"] < 2 ** 256
        else:
            assert all(0 <= c[k] < 2 ** 128 for k in ("sqrt_price_0", "sqrt_price_1", "liquidity"))


def test_move_cases_and_parsing():
    src = rc.cases_module([{"op": "shlw", "n": 2 ** 192}, dict(op="delta_a", **A, round_up=True)])
    assert "math_u256::checked_shlw(6277101735386680763835789423207666416102355444464034512896u256)" in src
    assert "get_delta_a(60257519765924248467716150u128, 60863087478126617965993239u128, " \
           "10365647984364446732462244378333008u128, true)" in src
    log = "\n".join([
        "[debug] 0x0::cases::Shlw {", "  case: 0,", "  value: 0,", "  overflow: false", "}",
        "[ PASS    ] pf_cetus::cases::c000000",
        "[ FAIL    ] pf_cetus::cases::c000001",
        "┌── c000001 ──────", "│ error[EC11001]: test failure",
        "│ Test was not expected to error, but it aborted with code 2 originating in the module 0xa2::clmm_math rooted here",
        "└──────────────────"])
    import subprocess
    orig = rc.sh
    rc.sh = lambda cmd, **kw: subprocess.CompletedProcess(cmd, 1, log, "")
    try:
        outs, _, _ = rc.run_move(pathlib.Path("."), 2)
    finally:
        rc.sh = orig
    assert outs[0] == {"value": 0, "overflow": False}
    assert outs[1] == {"amount": None, "abort": "abort code 2 in 0xa2::clmm_math"}


def test_lean_goals_name_the_matching_predicate():
    g = rc.goal({"op": "shlw", "n": 2 ** 192}, {"value": 0, "overflow": False}, "REQ-SHLW-EXACT")
    assert g[0].endswith("= (0, false) → ¬ ShlwExact shlw")
    g = rc.goal(dict(op="delta_a", **A, round_up=True), {"amount": 1}, "REQ-DELTA-A-COVERS")
    assert g[0].endswith("true = some 1 → ¬ DeltaACovers shlw")


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
