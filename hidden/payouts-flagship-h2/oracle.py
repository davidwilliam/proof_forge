"""Independent Python model of spec/Payout/Spec.lean, used to test binaries.

Trusted test code: it must mirror the protected Lean definitions exactly. It never
assigns VERIFIED; it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).
"""

FLAGSHIP = {
    "state": {"balances": [[1, 1000], [2, 0], [3, 0], [4, 0]], "auth": [[1, 1]], "applied": [3]},
    "request": {"txId": 7, "requester": 1, "source": 1, "recipients": [2, 3, 4], "amount": 100},
}


def gen_case(rng):
    n_acc = rng.randint(2, 6)
    accts = rng.sample(range(1, 50), n_acc)
    balances = [[a, rng.choice([0, rng.randint(0, 50), rng.randint(0, 5000)])] for a in accts]
    auth = [[q, s] for q in accts for s in accts if rng.random() < 0.3]
    applied = rng.sample(range(1, 30), rng.randint(0, 4))
    src = rng.choice(accts)
    others = [a for a in accts if a != src]
    rec = rng.sample(others, rng.randint(1, len(others)))
    bal = dict(balances)
    amount = rng.randint(1, max(1, bal[src])) if bal[src] > 0 else rng.randint(1, 10)
    req = {"txId": rng.choice([rng.randint(30, 99)] * 3 + applied[:1]), "requester": src,
           "source": src, "recipients": rec, "amount": amount}
    if [src, src] not in auth and rng.random() < 0.8:
        auth.append([src, src])
    # Mutate into an invalid request about 30% of the time.
    m = rng.random()
    if m < 0.05: req["amount"] = 0
    elif m < 0.10: req["recipients"] = []
    elif m < 0.15 and rec: req["recipients"] = rec + [rec[0]]
    elif m < 0.20: req["recipients"] = rec + [src]
    elif m < 0.25: req["amount"] = bal[src] + rng.randint(1, 100)
    elif m < 0.30: req["requester"] = rng.choice(accts + [99])
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
    rec = req["recipients"]
    auth = {tuple(p) for p in state["auth"]}
    return (
        len(set(accts)) == len(accts)
        and req["amount"] > 0
        and len(rec) > 0
        and len(set(rec)) == len(rec)
        and req["source"] not in rec
        and req["source"] in accts
        and all(x in accts for x in rec)
        and (req["requester"], req["source"]) in auth
        and req["amount"] <= bal.get(req["source"], 0)
        and req["txId"] not in state["applied"]
    )


def fair_share(amount, n, i):
    return amount // n + (1 if i < amount % n else 0)


def expected_balance(state, req, a):
    bal = dict(state["balances"])
    rec = req["recipients"]
    share = fair_share(req["amount"], len(rec), rec.index(a)) if a in rec else 0
    debit = req["amount"] if a == req["source"] else 0
    return bal.get(a, 0) - debit + share


def auth_in_universe(state):
    accts = [a for a, _ in state["balances"]]
    pairs = {tuple(p) for p in state["auth"]}
    return {(q, s) for q in accts for s in accts if (q, s) in pairs}


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    state, req = case["state"], case["request"]
    v = []
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    ok = out["outcome"] == "ok"
    s2 = out["state"]
    accts = [a for a, _ in state["balances"]]
    if valid(state, req):
        if not ok:
            return [("REQ-VALID-SUCCEEDS", "valid payout was rejected")]
        if [a for a, _ in s2["balances"]] != accts:
            v.append(("REQ-EFFECTS", "account universe changed"))
        got = dict(s2["balances"])
        for a in accts:
            exp = expected_balance(state, req, a)
            if got.get(a) != exp:
                rid = "REQ-FAIR-SHARES" if a in req["recipients"] else "REQ-EFFECTS"
                v.append((rid, f"account {a}: expected {exp}, got {got.get(a)}"))
        if sum(got.get(a, 0) for a in accts) != sum(dict(state["balances"]).values()):
            v.append(("REQ-CONSERVATION", f"total changed by {sum(got.get(a, 0) for a in accts) - sum(dict(state['balances']).values())}"))
        if {tuple(p) for p in s2["auth"]} != auth_in_universe(state):
            v.append(("REQ-EFFECTS", "authorization relation changed"))
        if set(s2["applied"]) != set(state["applied"]) | {req["txId"]}:
            v.append(("REQ-IDEMPOTENCY", f"applied IDs {sorted(set(s2['applied']))} != {sorted(set(state['applied']) | {req['txId']})}"))
    else:
        if ok:
            v.append(("REQ-INVALID-NOOP", "invalid payout succeeded"))
        if (dict(s2["balances"]) != dict(state["balances"])
                or {tuple(p) for p in s2["auth"]} != auth_in_universe(state)
                or s2["applied"] != state["applied"]):
            v.append(("REQ-INVALID-NOOP", "rejected payout changed the state"))
    return v
