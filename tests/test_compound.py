"""rw-compound-comp: oracle, case encoding and parsing, Lean goal rendering; no Docker, network,
forge or model calls.

Outputs computed with the Proposal 62 rule for an account with no recorded index must break the
reward bounds on the cSUSHI claim, and outputs computed with the specification's rule (the
Proposal 64 fix) must meet every requirement on generated cases.

Run: python3 tests/test_compound.py
"""
import contextlib, pathlib, random, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "eval")]
import realworld_compound as rc, task as taskmod  # noqa: E402

T = taskmod.load(ROOT / "realworld/tasks/rw-compound-comp")
O = T.oracle


def run(case):
    """Output of an implementation that meets the effects requirements, in the binary's format."""
    s = O.upgrade(case["legacy"])
    out = {"start": s, "steps": []}
    for op in case["ops"]:
        ok, s, _ = O.expected(s, op)
        out["steps"].append({"ok": ok, "state": s})
    return out


@contextlib.contextmanager
def proposal_62_rule():
    """`supplierIndex == 0 && supplyIndex > compInitialIndex`, as deployed by Proposal 62."""
    fixed = O.accrual_start
    O.accrual_start = lambda u, idx: (O.INIT if idx > O.INIT else 0) if u == 0 else u
    try:
        yield
    finally:
        O.accrual_start = fixed


def ids(v):
    return sorted({rid for rid, _ in v})


def test_cSUSHI_claim_breaks_the_bounds_under_the_proposal_62_rule():
    with proposal_62_rule():
        out = run(O.FLAGSHIP)
    last = out["steps"][-1]["state"]
    assert last["accts"][0]["wallet"] == 18977306140567618322762
    assert last["reserve"] == 300514463598935139440340 - 18977306140567618322762
    v = ids(O.check(O.FLAGSHIP, out))
    assert {"REQ-REWARDS-BOUNDED", "REQ-ACCOUNT-BOUNDED", "REQ-CLAIM"} <= set(v), v
    assert O.owed(O.FLAGSHIP["legacy"]) == 0


def test_specified_outputs_meet_every_requirement():
    rng = random.Random(3)
    for _ in range(1500):
        c = O.gen_case(rng)
        assert O.wellformed(c["legacy"])
        assert O.check(c, run(c)) == [], c


def test_honest_sequence_matches_sanity():
    case = {"legacy": {"blockNumber": 100, "compSpeed": 0, "supplyIndex": 0, "supplyBlock": 90, "borrowIndex": 0,
                       "borrowBlock": 90, "supplyStart": 0, "borrowStart": 0, "reserve": 1000,
                       "accts": [O.acct(supply=50), O.acct(borrow=20)]},
            "ops": [{"op": "setSpeeds", "supply": 3, "borrow": 2}, {"op": "advance", "blocks": 10},
                    {"op": "claim", "who": 0}, {"op": "claim", "who": 1}]}
    s = run(case)["steps"][-1]["state"]
    assert [a["wallet"] for a in s["accts"]] == [30, 20] and s["reserve"] == 950


def test_encoding_and_parsing_round_trip():
    rng = random.Random(5)
    c = O.gen_case(rng)
    words = bytes.fromhex(rc.encode(c)[2:])
    n = int.from_bytes(words[32:64], "big")
    w = [int.from_bytes(words[64 + 32 * i: 96 + 32 * i], "big") for i in range(n)]
    assert w[0] == len(c["legacy"]["accts"]) and w[1] == c["legacy"]["blockNumber"]
    assert w[8 + 6 * w[0]] == len(c["ops"])
    s = run(c)["start"]
    flat = rc.compact({"start": s, "steps": []})["start"]
    assert rc.parse_state(flat[:8] + [len(s["accts"])] + flat[8:]) == s


def test_lean_goals_for_the_cSUSHI_claim():
    with proposal_62_rule():
        out = run(O.FLAGSHIP)
    g, step = rc.lean_goal(O.FLAGSHIP, out, "REQ-REWARDS-BOUNDED", O)
    assert step == 2 and g.startswith("¬ (") and ".credited ≤ (upgrade" in g and "[Op.advance 139, Op.claim 0]" in g
    g, _ = rc.lean_goal(O.FLAGSHIP, out, "REQ-ACCOUNT-BOUNDED", O)
    assert ".creditedTo 0 ≤" in g


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print("ok", name)
