"""Independent Python model of spec/EntryLog/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).
"""

FLAGSHIP = {
    "state": {"balances": [[1, 500], [2, 40]],
              "log": [{"id": 11, "account": 1, "amount": 700},
                      {"id": 12, "account": 2, "amount": 40},
                      {"id": 13, "account": 1, "amount": -200}]},
    "entry": {"id": 12, "account": 2, "amount": 400},
}


def log_sum(log, a):
    return sum(e["amount"] for e in log if e["account"] == a)


def gen_state(rng):
    accts = rng.sample(range(1, 40), rng.randint(1, 5))
    bal = {a: 0 for a in accts}
    log = []
    used = rng.sample(range(1, 31), rng.randint(0, 7))
    for i in used:
        a = rng.choice(accts)
        if bal[a] > 0 and rng.random() < 0.4:
            amt = -rng.randint(1, bal[a])
        else:
            amt = rng.choice([rng.randint(1, 50), rng.randint(1, 3000)])
        bal[a] += amt
        log.append({"id": i, "account": a, "amount": amt})
    if rng.random() < 0.1:
        # Occasionally a state whose cache disagrees with its log.
        bal = {a: rng.randint(0, 100) for a in accts}
    return accts, bal, log


def gen_case(rng):
    accts, bal, log = gen_state(rng)
    state = {"balances": [[a, bal[a]] for a in accts], "log": log}
    used = [e["id"] for e in log]
    m = rng.random()
    if log and m < 0.25:
        # Resubmission of an existing ID, with the same or a different payload.
        orig = rng.choice(log)
        entry = dict(orig)
        if rng.random() < 0.6:
            entry["account"] = rng.choice(accts + [99])
            entry["amount"] = rng.choice([orig["amount"] + 1, rng.randint(-50, 50), 0])
        return {"state": state, "entry": entry}
    new_id = rng.choice([i for i in range(1, 100) if i not in used])
    a = rng.choice(accts)
    r = rng.random()
    if r < 0.15 and bal[a] > 0:
        amt = -bal[a]                                     # withdraw to exactly zero
    elif r < 0.35 and bal[a] > 0:
        amt = -rng.randint(1, bal[a])
    else:
        amt = rng.choice([1, rng.randint(1, 60), rng.randint(1, 5000)])
    entry = {"id": new_id, "account": a, "amount": amt}
    # Mutate into an invalid entry about 30% of the time.
    k = rng.random()
    if k < 0.10:
        entry["amount"] = 0
    elif k < 0.20:
        entry["account"] = rng.choice([x for x in range(1, 50) if x not in accts])
    elif k < 0.30:
        entry["amount"] = -(bal[a] + rng.choice([1, rng.randint(1, 100)]))
    return {"state": state, "entry": entry}


def receipt_of(log, i):
    for n, e in enumerate(log):
        if e["id"] == i:
            return n
    return None


def valid(state, e):
    bal = dict((a, v) for a, v in state["balances"])
    return (e["account"] in bal and e["amount"] != 0
            and 0 <= bal[e["account"]] + e["amount"])


def same_state(s1, s2):
    return s1["balances"] == s2["balances"] and s1["log"] == s2["log"]


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    state, e = case["state"], case["entry"]
    s2 = out["state"]
    log, log2 = state["log"], s2["log"]
    v = []
    n = receipt_of(log, e["id"])
    if n is not None:
        if out["outcome"] != "ok" or out["receipt"] != n:
            v.append(("REQ-DUPLICATE", f"duplicate ID {e['id']}: expected receipt {n}, got {out['outcome']} {out['receipt']}"))
        if not same_state(state, s2):
            v.append(("REQ-DUPLICATE", "duplicate submission changed the state"))
    elif valid(state, e):
        if out["outcome"] != "ok" or out["receipt"] != len(log):
            return [("REQ-VALID-SUCCEEDS", f"valid entry: expected ok {len(log)}, got {out['outcome']} {out['receipt']}")]
        accts = [a for a, _ in state["balances"]]
        if [a for a, _ in s2["balances"]] != accts:
            v.append(("REQ-EFFECTS", "account universe changed"))
        if log2 != log + [e]:
            v.append(("REQ-EFFECTS", "log is not the old log with the entry appended"))
        bal, got = dict(state["balances"]), dict((a, x) for a, x in s2["balances"])
        for a in accts:
            exp = bal[a] + (e["amount"] if a == e["account"] else 0)
            if got.get(a) != exp:
                v.append(("REQ-EFFECTS", f"account {a}: expected {exp}, got {got.get(a)}"))
    else:
        if out["outcome"] != "rejected":
            v.append(("REQ-INVALID-NOOP", "invalid entry was accepted"))
        if not same_state(state, s2):
            v.append(("REQ-INVALID-NOOP", "rejected entry changed the state"))
    # Invariants that hold for every step.
    if log2[:len(log)] != log:
        v.append(("REQ-APPEND-ONLY", "existing log is not a prefix of the new log"))
    ids, ids2 = [x["id"] for x in log], [x["id"] for x in log2]
    if len(set(ids)) == len(ids) and len(set(ids2)) != len(ids2):
        v.append(("REQ-UNIQUE-IDS", "log IDs are no longer distinct"))
    if all(x >= 0 for _, x in state["balances"]) and any(x < 0 for _, x in s2["balances"]):
        v.append(("REQ-NONNEGATIVE", "a balance became negative"))
    if (all(x == log_sum(log, a) for a, x in state["balances"])
            and any(x != log_sum(log2, a) for a, x in s2["balances"])):
        v.append(("REQ-CONSISTENT", "a balance differs from the sum of its log entries"))
    return v


def followup(case, out):
    """Resubmit an accepted new entry against the resulting state, with a changed amount for
    odd IDs. Returns the next case and the requirement its violations count against."""
    if out.get("outcome") == "ok" and receipt_of(case["state"]["log"], case["entry"]["id"]) is None:
        e = dict(case["entry"])
        if e["id"] % 2 == 1:
            e["amount"] = e["amount"] + 7
        return {"state": out["state"], "entry": e}, "REQ-DUPLICATE"
    return None


def describe(out):
    """Flagship summary: the receipt, balances and log length after the resubmission."""
    bal = ",".join(f"{a}:{x}" for a, x in out["state"]["balances"])
    return f"{out['outcome']} receipt={out['receipt']} balances={bal} log={len(out['state']['log'])}"
