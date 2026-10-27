"""Independent Python model of spec/Transfer/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).
"""

FLAGSHIP = {
    "state": {"balances": [[1, 100], [2, 0], [3, 40]], "limits": [[1, 50], [3, 10]],
              "auth": [[1, 1], [3, 1]], "applied": [5]},
    "request": {"txId": 8, "requester": 3, "source": 1, "target": 2, "amount": 150},
}


def lookup(pairs, a):
    """First-match lookup with default 0, as in app/Main.lean."""
    for k, v in pairs:
        if k == a:
            return v
    return 0


def gen_case(rng):
    n_acc = rng.randint(2, 6)
    accts = rng.sample(range(1, 50), n_acc)
    limits = []
    for a in accts:
        r = rng.random()
        if r < 0.25:
            continue
        limits.append([a, rng.choice([0, rng.randint(1, 50), rng.randint(100, 2000)])])
    balances = []
    for a in accts:
        lim = lookup(limits, a)
        b = rng.choice([0, rng.randint(1, 50), rng.randint(0, 5000), -rng.randint(0, lim)])
        balances.append([a, b])
    auth = [[q, s] for q in accts for s in accts if rng.random() < 0.25]
    applied = rng.sample(range(1, 30), rng.randint(0, 4))
    src = rng.choice(accts)
    tgt = rng.choice([a for a in accts if a != src])
    requester = src if rng.random() < 0.5 else rng.choice([a for a in accts if a != src])
    if [requester, src] not in auth:
        auth.append([requester, src])
    if lookup(balances, src) + lookup(limits, src) < 1 and rng.random() < 0.9:
        for p in balances:
            if p[0] == src:
                p[1] = rng.randint(1, 500)
    head = lookup(balances, src) + lookup(limits, src)
    if head >= 1:
        amount = rng.choice([head, head, head - 1, rng.randint(1, head), rng.randint(1, min(head, 20)),
                             lookup(balances, src)])
        amount = max(1, amount)
    else:
        amount = rng.randint(1, 10)
    req = {"txId": rng.choice([rng.randint(30, 99)] * 12 + applied[:1]), "requester": requester,
           "source": src, "target": tgt, "amount": amount}
    # Mutate into an invalid request about 30% of the time.
    m = rng.random()
    if m < 0.04:
        req["amount"] = 0
    elif m < 0.09:
        req["target"] = src
    elif m < 0.13:
        req["target"] = rng.choice([0, 77, 99])
    elif m < 0.16:
        req["source"] = rng.choice([0, 77, 99])
    elif m < 0.22:
        req["amount"] = max(1, head + 1)
    elif m < 0.27:
        auth.remove([requester, src])
    return {"state": {"balances": balances, "limits": limits, "auth": auth, "applied": applied},
            "request": req}


def followup(case, out):
    """Resubmit a successful request against the resulting state."""
    if out.get("outcome") == "ok":
        return {"state": out["state"], "request": case["request"]}, "REQ-IDEMPOTENCY"
    return None


def describe(out):
    """Flagship summary: outcome and resulting balances."""
    return out["outcome"] + " " + ",".join(f"{a}:{v}" for a, v in out["state"]["balances"])


def accounts(state):
    return [a for a, _ in state["balances"]]


def valid(state, req):
    accts = accounts(state)
    auth = {tuple(p) for p in state["auth"]}
    src, tgt, amt = req["source"], req["target"], req["amount"]
    return (
        len(set(accts)) == len(accts)
        and amt > 0
        and src != tgt
        and src in accts
        and tgt in accts
        and (req["requester"], src) in auth
        and -lookup(state["limits"], src) <= lookup(state["balances"], src) - amt
        and req["txId"] not in state["applied"]
    )


def expected_balance(state, req, a):
    b = lookup(state["balances"], a)
    if a == req["source"]:
        b -= req["amount"]
    if a == req["target"]:
        b += req["amount"]
    return b


def auth_in_universe(state):
    accts = accounts(state)
    pairs = {tuple(p) for p in state["auth"]}
    return {(q, s) for q in accts for s in accts if (q, s) in pairs}


def limits_view(state):
    return [[a, lookup(state["limits"], a)] for a in accounts(state)]


def within_limits(balances, limits, accts):
    return all(-lookup(limits, a) <= lookup(balances, a) for a in accts)


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    state, req = case["state"], case["request"]
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    v = []
    ok = out["outcome"] == "ok"
    s2 = out["state"]
    accts = accounts(state)
    if within_limits(state["balances"], state["limits"], accts) and not within_limits(
            s2["balances"], s2["limits"], accounts(s2)):
        v.append(("REQ-LIMIT", "an account ended below its overdraft limit"))
    if valid(state, req):
        if not ok:
            return v + [("REQ-VALID-SUCCEEDS", "valid transfer was rejected")]
        if accounts(s2) != accts:
            v.append(("REQ-EFFECTS", "account universe changed"))
        for a in accts:
            exp = expected_balance(state, req, a)
            got = lookup(s2["balances"], a)
            if got != exp:
                rid = "REQ-DEBIT-CREDIT" if a in (req["source"], req["target"]) else "REQ-EFFECTS"
                v.append((rid, f"account {a}: expected {exp}, got {got}"))
        before = sum(lookup(state["balances"], a) for a in accts)
        after = sum(lookup(s2["balances"], a) for a in accts)
        if before != after:
            v.append(("REQ-CONSERVATION", f"total changed by {after - before}"))
        if s2["limits"] != limits_view(state):
            v.append(("REQ-EFFECTS", "overdraft limits changed"))
        if {tuple(p) for p in s2["auth"]} != auth_in_universe(state):
            v.append(("REQ-EFFECTS", "authorization relation changed"))
        want = set(state["applied"]) | {req["txId"]}
        if set(s2["applied"]) != want:
            v.append(("REQ-IDEMPOTENCY", f"applied IDs {sorted(set(s2['applied']))} != {sorted(want)}"))
    else:
        if ok:
            v.append(("REQ-INVALID-NOOP", "invalid transfer succeeded"))
        if (accounts(s2) != accts
                or any(lookup(s2["balances"], a) != lookup(state["balances"], a) for a in accts)
                or s2["limits"] != limits_view(state)
                or {tuple(p) for p in s2["auth"]} != auth_in_universe(state)
                or s2["applied"] != state["applied"]):
            v.append(("REQ-INVALID-NOOP", "rejected transfer changed the state"))
    return v
