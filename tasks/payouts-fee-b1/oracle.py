"""Independent Python model of spec/FeePayout/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).
"""

BPS_SCALE = 10000

FLAGSHIP = {
    "state": {"balances": [[1, 1000], [2, 0], [3, 0], [4, 0], [9, 0]], "auth": [[1, 1]],
              "applied": [3], "feeAccount": 9, "feeBps": 250},
    "request": {"txId": 7, "requester": 1, "source": 1, "recipients": [2, 3, 4], "amount": 100},
}


def gen_case(rng):
    n_acc = rng.randint(3, 7)
    accts = rng.sample(range(1, 50), n_acc)
    balances = [[a, rng.choice([0, rng.randint(0, 50), rng.randint(0, 5000)])] for a in accts]
    auth = [[q, s] for q in accts for s in accts if rng.random() < 0.3]
    applied = rng.sample(range(1, 30), rng.randint(0, 4))
    fee_acc = rng.choice(accts)
    bps = rng.choice([0, 1, 30, 99, 250, 333, 1000, 2500, 5000, 9999, 10000,
                      rng.randint(0, 10000), rng.randint(0, 10000)])
    src = rng.choice([a for a in accts if a != fee_acc])
    if rng.random() < 0.9:
        balances = [[a, rng.choice([1, rng.randint(1, 50), rng.randint(1, 5000)]) if a == src else v]
                    for a, v in balances]
    others = [a for a in accts if a not in (src, fee_acc)]
    rec = rng.sample(others, rng.randint(1, len(others)))
    bal = dict(balances)
    if bal[src] > 0:
        amount = rng.choice([rng.randint(1, bal[src]), bal[src], rng.randint(1, min(bal[src], 2 * len(rec)))])
    else:
        amount = rng.randint(1, 10)
    req = {"txId": rng.randint(30, 99), "requester": src, "source": src, "recipients": rec,
           "amount": amount}
    auth.append([src, src])
    state = {"balances": balances, "auth": auth, "applied": applied,
             "feeAccount": fee_acc, "feeBps": bps}
    # Mutate into an invalid request about 30% of the time.
    m = rng.random()
    if m < 0.03: req["amount"] = 0
    elif m < 0.06: req["recipients"] = []
    elif m < 0.09: req["recipients"] = rec + [rec[0]]
    elif m < 0.12: req["recipients"] = rec + [src]
    elif m < 0.15: req["recipients"] = rec + [fee_acc]
    elif m < 0.17: state["feeAccount"] = src
    elif m < 0.19: state["feeAccount"] = rng.choice([0, 99])
    elif m < 0.21: state["feeBps"] = rng.choice([10001, 20000])
    elif m < 0.24:
        # Just above the balance, often still covered by the net amount.
        state["feeBps"] = max(bps, 500)
        b = max(bal[src], 100)
        state["balances"] = [[a, b if a == src else v] for a, v in balances]
        req["amount"] = b + rng.randint(1, max(1, b * state["feeBps"] // BPS_SCALE))
    elif m < 0.27: req["amount"] = bal[src] + rng.randint(1, 100)
    elif m < 0.30: req["requester"] = rng.choice(accts + [99])
    elif m < 0.33 and applied: req["txId"] = rng.choice(applied)
    return {"state": state, "request": req}


def followup(case, out):
    """Resubmit a successful request against the resulting state. Returns the next case and
    the requirement any violation on it is attributed to, or None."""
    if out.get("outcome") == "ok":
        return {"state": out["state"], "request": case["request"]}, "REQ-IDEMPOTENCY"
    return None


def describe(out):
    """Flagship summary: recipient balances, then the fee account balance."""
    vals = [v for _, v in out["state"]["balances"]]
    return "+".join(str(v) for v in vals[1:-1]) + f" fee {vals[-1]}"


def valid(state, req):
    accts = [a for a, _ in state["balances"]]
    bal = dict(state["balances"])
    rec = req["recipients"]
    auth = {tuple(p) for p in state["auth"]}
    fee_acc = state["feeAccount"]
    return (
        len(set(accts)) == len(accts)
        and state["feeBps"] <= BPS_SCALE
        and req["amount"] > 0
        and len(rec) > 0
        and len(set(rec)) == len(rec)
        and req["source"] not in rec
        and fee_acc not in rec
        and fee_acc != req["source"]
        and req["source"] in accts
        and fee_acc in accts
        and all(x in accts for x in rec)
        and (req["requester"], req["source"]) in auth
        and req["amount"] <= bal.get(req["source"], 0)
        and req["txId"] not in state["applied"]
    )


def split(bps, amount, n):
    """(fee, per-recipient share, fee account credit)."""
    fee = amount * bps // BPS_SCALE
    net = amount - fee
    return fee, net // n, fee + net % n


def expected_balance(state, req, a):
    bal = dict(state["balances"])
    _, share, credit = split(state["feeBps"], req["amount"], len(req["recipients"]))
    out = bal.get(a, 0)
    if a == req["source"]:
        out -= req["amount"]
    if a in req["recipients"]:
        out += share
    if a == state["feeAccount"]:
        out += credit
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
        if s2["feeAccount"] != state["feeAccount"] or s2["feeBps"] != state["feeBps"]:
            v.append(("REQ-EFFECTS", "fee configuration changed"))
        if {tuple(p) for p in s2["auth"]} != auth_in_universe(state):
            v.append(("REQ-EFFECTS", "authorization relation changed"))
        for a in accts:
            exp = expected_balance(state, req, a)
            if got.get(a) != exp:
                if a in req["recipients"]:
                    rid = "REQ-EQUAL-SHARES"
                elif a == state["feeAccount"]:
                    rid = "REQ-FEE-COLLECTED"
                else:
                    rid = "REQ-EFFECTS"
                v.append((rid, f"account {a}: expected {exp}, got {got.get(a)}"))
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
                or s2["applied"] != state["applied"]
                or s2["feeAccount"] != state["feeAccount"]
                or s2["feeBps"] != state["feeBps"]):
            v.append(("REQ-INVALID-NOOP", "rejected payout changed the state"))
    return v
