"""Independent Python model of spec/WeightedPayout/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).
"""

FLAGSHIP = {
    "state": {"balances": [[1, 1000], [2, 0], [3, 0], [4, 0]], "auth": [[1, 1]], "applied": [3]},
    "request": {"txId": 7, "requester": 1, "source": 1, "recipients": [2, 3, 4],
                "weights": [1, 1, 1], "amount": 100},
}


def gen_weights(rng, n):
    kind = rng.random()
    if kind < 0.2:
        return [1] * n
    if kind < 0.4:
        return [rng.randint(1, 1000) for _ in range(n)]
    if kind < 0.5:
        return [rng.randint(50, 100)] + [1] * (n - 1)
    return [rng.randint(1, 10) for _ in range(n)]


def gen_case(rng):
    n_acc = rng.randint(2, 7)
    accts = rng.sample(range(1, 50), n_acc)
    balances = [[a, rng.choice([0, rng.randint(0, 50), rng.randint(0, 5000)])] for a in accts]
    auth = [[q, s] for q in accts for s in accts if rng.random() < 0.3]
    applied = rng.sample(range(1, 30), rng.randint(0, 4))
    src = rng.choice(accts)
    if rng.random() < 0.9:
        balances = [[a, rng.choice([1, rng.randint(1, 50), rng.randint(1, 5000)]) if a == src else v]
                    for a, v in balances]
    others = [a for a in accts if a != src]
    rec = rng.sample(others, rng.randint(1, len(others)))
    ws = gen_weights(rng, len(rec))
    bal = dict(balances)
    if bal[src] > 0:
        amount = rng.choice([rng.randint(1, bal[src]), bal[src], rng.randint(1, min(bal[src], 3 * len(rec)))])
    else:
        amount = rng.randint(1, 10)
    req = {"txId": rng.randint(30, 99), "requester": src, "source": src, "recipients": rec,
           "weights": ws, "amount": amount}
    auth.append([src, src])
    # Mutate into an invalid request about 30% of the time.
    m = rng.random()
    if m < 0.03: req["amount"] = 0
    elif m < 0.06: req["recipients"], req["weights"] = [], []
    elif m < 0.09: req["weights"] = ws[:-1] + [0]
    elif m < 0.12: req["weights"] = ws + [rng.randint(1, 5)]
    elif m < 0.14 and len(ws) > 1: req["weights"] = ws[:-1]
    elif m < 0.18: req["recipients"], req["weights"] = rec + [rec[0]], ws + [rng.randint(1, 10)]
    elif m < 0.21: req["recipients"], req["weights"] = rec + [src], ws + [rng.randint(1, 10)]
    elif m < 0.24: req["amount"] = bal[src] + rng.randint(1, 100)
    elif m < 0.27: req["requester"] = rng.choice(accts + [99])
    elif m < 0.30 and applied: req["txId"] = rng.choice(applied)
    return {"state": {"balances": balances, "auth": auth, "applied": applied}, "request": req}


def followup(case, out):
    """Resubmit a successful request against the resulting state. Returns the next case and
    the requirement any violation on it is attributed to, or None."""
    if out.get("outcome") == "ok":
        return {"state": out["state"], "request": case["request"]}, "REQ-IDEMPOTENCY"
    return None


def describe(out):
    """Flagship summary: the recipients' resulting balances."""
    return "+".join(str(v) for _, v in out["state"]["balances"][1:])


def valid(state, req):
    accts = [a for a, _ in state["balances"]]
    bal = dict(state["balances"])
    rec, ws = req["recipients"], req["weights"]
    auth = {tuple(p) for p in state["auth"]}
    return (
        len(set(accts)) == len(accts)
        and req["amount"] > 0
        and len(rec) > 0
        and len(ws) == len(rec)
        and all(w > 0 for w in ws)
        and len(set(rec)) == len(rec)
        and req["source"] not in rec
        and req["source"] in accts
        and all(x in accts for x in rec)
        and (req["requester"], req["source"]) in auth
        and req["amount"] <= bal.get(req["source"], 0)
        and req["txId"] not in state["applied"]
    )


def shares(amount, ws):
    """Floor shares amount * w // W, plus one cent for the first `leftover` positions."""
    total_w = sum(ws)
    floors = [amount * w // total_w for w in ws]
    left = amount - sum(floors)
    return [f + (1 if i < left else 0) for i, f in enumerate(floors)]


def expected_balances(state, req):
    bal = dict(state["balances"])
    out = dict(bal)
    out[req["source"]] -= req["amount"]
    for a, sh in zip(req["recipients"], shares(req["amount"], req["weights"])):
        out[a] += sh
    return out


def auth_in_universe(state):
    accts = [a for a, _ in state["balances"]]
    pairs = {tuple(p) for p in state["auth"]}
    return {(q, s) for q in accts for s in accts if (q, s) in pairs}


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    state, req = case["state"], case["request"]
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    v = []
    ok = out["outcome"] == "ok"
    s2 = out["state"]
    accts = [a for a, _ in state["balances"]]
    old = dict(state["balances"])
    got = dict(s2["balances"])
    if valid(state, req):
        if not ok:
            return [("REQ-VALID-SUCCEEDS", "valid payout was rejected")]
        if [a for a, _ in s2["balances"]] != accts:
            v.append(("REQ-EFFECTS", "account universe changed"))
        if {tuple(p) for p in s2["auth"]} != auth_in_universe(state):
            v.append(("REQ-EFFECTS", "authorization relation changed"))
        exp = expected_balances(state, req)
        total_w = sum(req["weights"])
        for a, w in zip(req["recipients"], req["weights"]):
            d = got.get(a, 0) - old[a]
            if not (d * total_w <= req["amount"] * w + total_w and req["amount"] * w < d * total_w + total_w):
                v.append(("REQ-ROUNDING-BOUND", f"account {a}: received {d}, exact share {req['amount'] * w}/{total_w}"))
        for a in accts:
            if got.get(a) != exp[a]:
                rid = "REQ-PRO-RATA-SHARES" if a in req["recipients"] else "REQ-EFFECTS"
                v.append((rid, f"account {a}: expected {exp[a]}, got {got.get(a)}"))
        before = sum(old.values())
        after = sum(got.get(a, 0) for a in accts)
        if after != before:
            v.append(("REQ-CONSERVATION", f"total changed by {after - before}"))
        if all(old[a] >= 0 for a in accts) and any(got.get(a, 0) < 0 for a in accts):
            v.append(("REQ-NONNEGATIVE", "a balance became negative"))
        if set(s2["applied"]) != set(state["applied"]) | {req["txId"]}:
            v.append(("REQ-IDEMPOTENCY", f"applied IDs {sorted(set(s2['applied']))} != "
                                         f"{sorted(set(state['applied']) | {req['txId']})}"))
    else:
        if ok:
            v.append(("REQ-INVALID-NOOP", "invalid payout succeeded"))
            if all(old[a] >= 0 for a in accts) and any(got.get(a, 0) < 0 for a in accts):
                v.append(("REQ-NONNEGATIVE", "a balance became negative"))
        if (got != old
                or [a for a, _ in s2["balances"]] != accts
                or {tuple(p) for p in s2["auth"]} != auth_in_universe(state)
                or s2["applied"] != state["applied"]):
            v.append(("REQ-INVALID-NOOP", "rejected payout changed the state"))
    return v
