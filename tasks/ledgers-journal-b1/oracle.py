"""Independent Python model of spec/Journal/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).
"""

FLAGSHIP = {
    "state": {"balances": [[1, 1000], [2, 0], [3, 50]], "posted": [4]},
    "entry": {"id": 9, "lines": [[1, -500], [2, 300], [1, -200], [3, 400]]},
}


def gen_lines(rng, accts):
    n = rng.randint(2, 5)
    used, lines = [], []
    for _ in range(n - 1):
        if used and rng.random() < 0.35:
            a = rng.choice(used)
        else:
            a = rng.choice(accts)
        used.append(a)
        amt = rng.choice([rng.randint(1, 20), rng.randint(1, 2000)]) * rng.choice([1, -1])
        lines.append([a, amt])
    last = -sum(x for _, x in lines)
    if last == 0:
        lines[0][1] += 1
        last = -1
    a = rng.choice(used) if rng.random() < 0.3 else rng.choice(accts)
    lines.append([a, last])
    rng.shuffle(lines)
    return lines


def gen_case(rng):
    accts = rng.sample(range(1, 40), rng.randint(2, 6))
    balances = [[a, rng.choice([0, rng.randint(0, 100), rng.randint(-500, 5000)])] for a in accts]
    posted = rng.sample(range(1, 30), rng.randint(0, 4))
    entry = {"id": rng.choice([i for i in range(1, 60) if i not in posted]),
             "lines": gen_lines(rng, accts)}
    # Mutate into an invalid entry about 30% of the time.
    m = rng.random()
    if m < 0.04:
        entry["lines"] = []
    elif m < 0.10:
        i = rng.randrange(len(entry["lines"]))
        entry["lines"][i][1] += rng.choice([1, -1, 100])
        if entry["lines"][i][1] == 0:
            entry["lines"][i][1] = 7
    elif m < 0.14:
        entry["lines"].insert(rng.randrange(len(entry["lines"]) + 1), [rng.choice(accts), 0])
    elif m < 0.22:
        i = rng.randrange(len(entry["lines"]))
        entry["lines"][i][0] = rng.choice([x for x in range(1, 50) if x not in accts])
    elif m < 0.27 and posted:
        entry["id"] = rng.choice(posted)
    elif m < 0.30:
        balances.append([balances[0][0], rng.randint(0, 100)])
    return {"state": {"balances": balances, "posted": posted}, "entry": entry}


def line_sum(lines):
    return sum(x for _, x in lines)


def net_of(lines, a):
    return sum(x for b, x in lines if b == a)


def valid(state, e):
    accts = [a for a, _ in state["balances"]]
    return (len(set(accts)) == len(accts)
            and len(e["lines"]) > 0
            and all(a in accts for a, _ in e["lines"])
            and all(x != 0 for _, x in e["lines"])
            and line_sum(e["lines"]) == 0
            and e["id"] not in state["posted"])


def first_bal(balances):
    """Balance lookup as the wrapper performs it: the first pair for an account wins."""
    d = {}
    for a, x in balances:
        d.setdefault(a, x)
    return d


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    state, e = case["state"], case["entry"]
    s2 = out["state"]
    accts = [a for a, _ in state["balances"]]
    bal = first_bal(state["balances"])
    ok = out["outcome"] == "ok"
    v = []
    if ok:
        if any(a not in accts for a, _ in e["lines"]):
            v.append(("REQ-KNOWN-ACCOUNTS", "posted an entry that touches an unknown account"))
        if line_sum(e["lines"]) != 0:
            v.append(("REQ-BALANCED", f"posted an entry whose lines sum to {line_sum(e['lines'])}"))
    if valid(state, e):
        if not ok:
            return [("REQ-VALID-SUCCEEDS", "valid entry was rejected")]
        if [a for a, _ in s2["balances"]] != accts:
            v.append(("REQ-EFFECTS", f"account universe changed to {[a for a, _ in s2['balances']]}"))
        got = first_bal(s2["balances"])
        for a in accts:
            exp = bal[a] + net_of(e["lines"], a)
            if got.get(a) != exp:
                v.append(("REQ-EFFECTS", f"account {a}: expected {exp}, got {got.get(a)}"))
        if sorted(set(s2["posted"])) != sorted(set(state["posted"]) | {e["id"]}):
            v.append(("REQ-IDEMPOTENCY", f"posted IDs {sorted(set(s2['posted']))}"))
        if sum(got.get(a, 0) for a in accts) != sum(bal[a] for a in accts):
            v.append(("REQ-TRIAL-BALANCE", "sum of balances changed by "
                      f"{sum(got.get(a, 0) for a in accts) - sum(bal[a] for a in accts)}"))
    else:
        if ok:
            v.append(("REQ-INVALID-NOOP", "invalid entry was posted"))
        shown = [[a, bal[a]] for a in accts]
        if s2["balances"] != shown or s2["posted"] != state["posted"]:
            v.append(("REQ-INVALID-NOOP", "rejected entry changed the state"))
    return v


def followup(case, out):
    """Post an accepted entry again against the resulting state. Returns the next case and
    the requirement its violations count against, or None."""
    if out.get("outcome") == "ok":
        return {"state": out["state"], "entry": case["entry"]}, "REQ-IDEMPOTENCY"
    return None


def describe(out):
    """Flagship summary: the resulting balances."""
    return ",".join(f"{a}:{x}" for a, x in out["state"]["balances"])
