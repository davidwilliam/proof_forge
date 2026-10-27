"""Independent Python model of spec/FixedWindow/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns
VERIFIED; it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out).
"""

FLAGSHIP = {
    "state": {"window": 10, "limit": 3, "clients": [
        {"id": 1, "start": 0, "count": 3},
        {"id": 2, "start": 5, "count": 3},
        {"id": 3, "start": 12, "count": 1}]},
    "request": {"client": 2, "time": 15},
}


def lookup(clients, i):
    for c in clients:
        if c["id"] == i:
            return c
    return None


def expired(s, c, t):
    return c["start"] + s["window"] <= t


def window_start(s, c, t):
    return t if expired(s, c, t) else c["start"]


def window_count(s, c, t):
    return 0 if expired(s, c, t) else c["count"]


def advance(s, c, t):
    return {"id": c["id"], "start": window_start(s, c, t), "count": window_count(s, c, t) + 1}


def admissible(s, r):
    ids = [c["id"] for c in s["clients"]]
    if len(set(ids)) != len(ids):
        return False
    c = lookup(s["clients"], r["client"])
    return (c is not None and c["start"] <= r["time"]
            and window_count(s, c, r["time"]) < s["limit"])


def expected_lookup(s, r, i):
    c = lookup(s["clients"], i)
    if i == r["client"] and c is not None:
        return advance(s, c, r["time"])
    return c


def gen_case(rng):
    window = rng.choice([1, rng.randint(1, 5), rng.randint(5, 30)])
    if rng.random() < 0.03:
        window = 0
    limit = rng.choice([1, rng.randint(1, 4), rng.randint(4, 10)])
    if rng.random() < 0.03:
        limit = 0
    n = rng.randint(1, 6)
    ids = rng.sample(range(1, 40), n)
    clients = []
    for i in ids:
        start = rng.randint(0, 100)
        count = rng.choice([0, limit, max(0, limit - 1), rng.randint(0, limit)])
        clients.append({"id": i, "start": start, "count": count})
    if rng.random() < 0.04 and n > 1:
        clients[-1] = dict(clients[-1], id=clients[0]["id"])      # duplicate id
    target = rng.choice(clients)
    cid = target["id"]
    if rng.random() < 0.05:
        cid = rng.choice([0, 99])                                  # unregistered client
    m = rng.random()
    if m < 0.06:
        time = target["start"] - rng.randint(1, 5)                 # before the window start
    elif m < 0.26:
        time = target["start"] + window                            # exactly at the boundary
    elif m < 0.36:
        time = target["start"] + max(0, window - 1)                # last tick of the window
    elif m < 0.46:
        time = target["start"] + window + rng.randint(1, 30)       # well past the window
    else:
        time = target["start"] + rng.randint(0, max(0, window - 1))
    if time < 0:
        time = 0
    # Push other clients' windows into the past now and then, so expiry elsewhere is common.
    for c in clients:
        if c is not target and rng.random() < 0.3:
            c["start"] = max(0, time - window - rng.randint(0, 10))
    return {"state": {"window": window, "limit": limit, "clients": clients},
            "request": {"client": cid, "time": time}}


def describe(out):
    """Flagship summary: outcome and the requesting client's entry."""
    c = lookup(out["state"]["clients"], 2)
    return f"{out['outcome']}:{c['start']}/{c['count']}" if c else out["outcome"]


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    s, r = case["state"], case["request"]
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    v = []
    ok = out["outcome"] == "ok"
    s2 = out["state"]
    ids = {c["id"] for c in s["clients"]} | {c["id"] for c in s2["clients"]}
    for i in sorted(ids - {r["client"]}):
        if lookup(s2["clients"], i) != lookup(s["clients"], i):
            v.append(("REQ-ISOLATION", f"entry of client {i} changed"))
            break
    if all(c["count"] <= s["limit"] for c in s["clients"]):
        over = [c for c in s2["clients"] if c["count"] > s2["limit"]]
        if over:
            v.append(("REQ-WINDOW-BOUND", f"client {over[0]['id']} count {over[0]['count']} above limit {s2['limit']}"))
    if admissible(s, r):
        if not ok:
            return v + [("REQ-VALID-SUCCEEDS", "admissible request was rejected")]
        c = lookup(s["clients"], r["client"])
        c2 = lookup(s2["clients"], r["client"])
        exp = advance(s, c, r["time"])
        if c2 is None or (c2["start"], c2["count"]) != (exp["start"], exp["count"]):
            v.append(("REQ-RESET", f"entry {c2}, expected {exp}"))
        if (s2["window"], s2["limit"]) != (s["window"], s["limit"]):
            v.append(("REQ-EFFECTS", "window or limit changed"))
        if [x["id"] for x in s2["clients"]] != [x["id"] for x in s["clients"]]:
            v.append(("REQ-EFFECTS", "client ids or their order changed"))
        for i in sorted(ids):
            if lookup(s2["clients"], i) != expected_lookup(s, r, i):
                v.append(("REQ-EFFECTS", f"entry of client {i} differs from the specified entry"))
                break
    else:
        if ok:
            v.append(("REQ-INVALID-NOOP", "inadmissible request was accepted"))
        if s2 != s:
            v.append(("REQ-INVALID-NOOP", "rejected request changed the state"))
    return v
