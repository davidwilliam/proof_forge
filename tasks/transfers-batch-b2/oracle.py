"""Independent Python model of spec/Batch/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).
"""

# Account 2 can pay account 3 only after it has received the first leg.
FLAGSHIP = {
    "state": {"balances": [[1, 100], [2, 0], [3, 0]], "limits": [[1, 20]], "applied": [4]},
    "request": {"batchId": 9, "legs": [{"source": 1, "target": 2, "amount": 120},
                                       {"source": 2, "target": 3, "amount": 70}]},
}


def lookup(pairs, a):
    """First-match lookup with default 0, as in app/Main.lean."""
    for k, v in pairs:
        if k == a:
            return v
    return 0


def accounts(state):
    return [a for a, _ in state["balances"]]


def shift(bal, leg):
    out = dict(bal)
    out[leg["source"]] = out.get(leg["source"], 0) - leg["amount"]
    out[leg["target"]] = out.get(leg["target"], 0) + leg["amount"]
    return out


def leg_ok(state, bal, leg):
    accts = accounts(state)
    return (leg["amount"] > 0
            and leg["source"] != leg["target"]
            and leg["source"] in accts
            and leg["target"] in accts
            and -lookup(state["limits"], leg["source"]) <= bal.get(leg["source"], 0) - leg["amount"])


def initial_bal(state):
    return {a: lookup(state["balances"], a) for a in accounts(state)}


def valid(state, req):
    accts = accounts(state)
    if len(set(accts)) != len(accts) or not req["legs"] or req["batchId"] in state["applied"]:
        return False
    bal = initial_bal(state)
    for leg in req["legs"]:
        if not leg_ok(state, bal, leg):
            return False
        bal = shift(bal, leg)
    return True


def final_balances(state, req):
    bal = initial_bal(state)
    for leg in req["legs"]:
        bal = shift(bal, leg)
    return bal


def gen_case(rng):
    n_acc = rng.randint(2, 6)
    accts = rng.sample(range(1, 50), n_acc)
    limits = []
    for a in accts:
        if rng.random() < 0.25:
            continue
        limits.append([a, rng.choice([0, rng.randint(1, 50), rng.randint(100, 2000)])])
    balances = []
    for a in accts:
        lim = lookup(limits, a)
        balances.append([a, rng.choice([0, rng.randint(1, 50), rng.randint(0, 5000), -rng.randint(0, lim)])])
    applied = rng.sample(range(1, 30), rng.randint(0, 4))
    state = {"balances": balances, "limits": limits, "applied": applied}
    bal = initial_bal(state)
    legs, targets = [], []
    for _ in range(rng.choice([1, 1, 2, 2, 3, 3, 4, 5])):
        cands = [a for a in accts if bal[a] + lookup(limits, a) >= 1]
        chain = [a for a in targets if a in cands]
        if chain and rng.random() < 0.5:
            src = rng.choice(chain)
        elif cands:
            src = rng.choice(cands)
        else:
            src = rng.choice(accts)
        tgt = rng.choice([a for a in accts if a != src])
        head = bal[src] + lookup(limits, src)
        if head >= 1:
            amount = max(1, rng.choice([head, head, head - 1, rng.randint(1, head),
                                        rng.randint(1, min(head, 20))]))
        else:
            amount = rng.randint(1, 10)
        leg = {"source": src, "target": tgt, "amount": amount}
        legs.append(leg)
        targets.append(tgt)
        bal = shift(bal, leg)
    req = {"batchId": rng.choice([rng.randint(30, 99)] * 12 + applied[:1]), "legs": legs}
    # Mutate one leg (or the batch) into an invalid request about 30% of the time.
    m = rng.random()
    i = rng.randrange(len(legs))
    if m < 0.03:
        legs[i]["amount"] = 0
    elif m < 0.07:
        legs[i]["target"] = legs[i]["source"]
    elif m < 0.11:
        legs[i]["target"] = rng.choice([0, 77, 99])
    elif m < 0.13:
        legs[i]["source"] = rng.choice([0, 77, 99])
    elif m < 0.19:
        run = initial_bal(state)
        for leg in legs[:i]:
            run = shift(run, leg)
        legs[i]["amount"] = max(1, run.get(legs[i]["source"], 0) + lookup(limits, legs[i]["source"]) + 1)
    elif m < 0.24 and legs:
        # A further debit from an account already used as a source.
        src = rng.choice([l["source"] for l in legs])
        run = final_balances(state, req)
        tgt = rng.choice([a for a in accts if a != src])
        legs.append({"source": src, "target": tgt,
                     "amount": max(1, run.get(src, 0) + lookup(limits, src) + rng.choice([0, 1, 1]))})
    elif m < 0.26:
        req["legs"] = []
    return {"state": state, "request": req}


def followup(case, out):
    """Resubmit a successful batch against the resulting state."""
    if out.get("outcome") == "ok":
        return {"state": out["state"], "request": case["request"]}, "REQ-IDEMPOTENCY"
    return None


def describe(out):
    """Flagship summary: outcome and resulting balances."""
    return out["outcome"] + " " + ",".join(f"{a}:{v}" for a, v in out["state"]["balances"])


def limits_view(state):
    return [[a, lookup(state["limits"], a)] for a in accounts(state)]


def within_limits(state):
    return all(-lookup(state["limits"], a) <= lookup(state["balances"], a) for a in accounts(state))


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    state, req = case["state"], case["request"]
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    v = []
    ok = out["outcome"] == "ok"
    s2 = out["state"]
    accts = accounts(state)
    if within_limits(state) and not within_limits(s2):
        v.append(("REQ-LIMIT-EVERY-STEP", "an account ended below its overdraft limit"))
    if valid(state, req):
        if not ok:
            return v + [("REQ-VALID-SUCCEEDS", "valid batch was rejected")]
        if accounts(s2) != accts:
            v.append(("REQ-EFFECTS", "account universe changed"))
        exp = final_balances(state, req)
        single = req["legs"][0] if len(req["legs"]) == 1 else None
        for a in accts:
            got = lookup(s2["balances"], a)
            if got != exp[a]:
                rid = ("REQ-SINGLE-LEG" if single and a in (single["source"], single["target"])
                       else "REQ-EFFECTS")
                v.append((rid, f"account {a}: expected {exp[a]}, got {got}"))
        before = sum(lookup(state["balances"], a) for a in accts)
        after = sum(lookup(s2["balances"], a) for a in accts)
        if before != after:
            v.append(("REQ-CONSERVATION", f"total changed by {after - before}"))
        if s2["limits"] != limits_view(state):
            v.append(("REQ-EFFECTS", "overdraft limits changed"))
        want = set(state["applied"]) | {req["batchId"]}
        if set(s2["applied"]) != want:
            v.append(("REQ-IDEMPOTENCY", f"applied IDs {sorted(set(s2['applied']))} != {sorted(want)}"))
    else:
        if ok:
            v.append(("REQ-ATOMICITY", "invalid batch succeeded"))
        if (accounts(s2) != accts
                or any(lookup(s2["balances"], a) != lookup(state["balances"], a) for a in accts)
                or s2["limits"] != limits_view(state)
                or s2["applied"] != state["applied"]):
            v.append(("REQ-ATOMICITY", "rejected batch changed the state"))
    return v
