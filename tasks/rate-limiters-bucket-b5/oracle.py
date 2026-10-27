"""Independent Python model of spec/TokenBucket/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns
VERIFIED; it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out).
"""

FIELDS = ("capacity", "rate", "tokens", "last")

FLAGSHIP = {
    "state": {"capacity": 10, "rate": 2, "tokens": 6, "last": 100},
    "request": {"time": 104, "cost": 4},
}


def refilled(s, t):
    elapsed = max(0, t - s["last"])
    return min(s["capacity"], s["tokens"] + s["rate"] * elapsed)


def admissible(s, r):
    return s["last"] <= r["time"] and 0 < r["cost"] and r["cost"] <= refilled(s, r["time"])


def gen_case(rng):
    cap = rng.choice([1, rng.randint(1, 10), rng.randint(5, 40), rng.randint(40, 200)])
    if rng.random() < 0.03:
        cap = 0
    rate = rng.choice([1, rng.randint(1, 5), rng.randint(5, 20)])
    if rng.random() < 0.05:
        rate = 0
    tokens = rng.choice([0, cap, rng.randint(0, cap)])
    last = rng.randint(0, 200)
    if rng.random() < 0.08:
        time = last - rng.randint(1, 10)          # earlier than the last update
    else:
        time = last + rng.choice([0, 1, rng.randint(1, 5), rng.randint(5, 50)])
    s = {"capacity": cap, "rate": rate, "tokens": tokens, "last": last}
    level = refilled(s, max(time, last))
    raw = tokens + rate * max(0, time - last)
    c = rng.random()
    if c < 0.25:
        cost = level                              # exactly the available level
    elif c < 0.33:
        cost = level + 1                          # one more than available
    elif c < 0.41:
        cost = raw                                # the uncapped level
    elif c < 0.44:
        cost = 0
    elif c < 0.50:
        cost = rng.randint(0, raw + 3)
    else:
        cost = rng.randint(1, max(1, level))
    return {"state": s, "request": {"time": max(0, time), "cost": max(0, cost)}}


def describe(out):
    """Flagship summary: outcome and remaining tokens."""
    return f"{out['outcome']}:{out['state']['tokens']}"


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    s, r = case["state"], case["request"]
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    v = []
    ok = out["outcome"] == "ok"
    s2 = out["state"]
    if s2["last"] < s["last"]:
        v.append(("REQ-TIME-MONOTONE", f"last moved back from {s['last']} to {s2['last']}"))
    if s["tokens"] <= s["capacity"] and s2["tokens"] > s2["capacity"]:
        v.append(("REQ-CAPACITY", f"tokens {s2['tokens']} above capacity {s2['capacity']}"))
    timely = s["last"] <= r["time"] and r["cost"] > 0
    if timely and ok != (r["cost"] <= refilled(s, r["time"])):
        v.append(("REQ-ALLOW-IFF-SUFFICIENT",
                  f"outcome {out['outcome']} with cost {r['cost']} and level {refilled(s, r['time'])}"))
    if admissible(s, r):
        if not ok:
            return v + [("REQ-VALID-SUCCEEDS", "admissible request was rejected")]
        level = refilled(s, r["time"])
        if s2["last"] != r["time"]:
            v.append(("REQ-TIME-MONOTONE", f"last is {s2['last']}, expected {r['time']}"))
        if s2["tokens"] + r["cost"] != level:
            v.append(("REQ-REMAINING", f"tokens {s2['tokens']}, expected {level - r['cost']}"))
        if (s2["capacity"], s2["rate"]) != (s["capacity"], s["rate"]):
            v.append(("REQ-EFFECTS", "capacity or rate changed"))
        if s2["tokens"] != level - r["cost"] or s2["last"] != r["time"]:
            v.append(("REQ-EFFECTS", "next state differs from the specified state"))
    else:
        if ok:
            v.append(("REQ-INVALID-NOOP", "inadmissible request was accepted"))
        if any(s2[k] != s[k] for k in FIELDS):
            v.append(("REQ-INVALID-NOOP", "rejected request changed the state"))
    return v
