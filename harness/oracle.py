"""Independent Python model of formal/spec/Payout/Spec.lean, used to test binaries.

Trusted test code: it must mirror the protected Lean definitions exactly. It never
assigns VERIFIED; it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.
"""


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


def check(state, req, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
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
