"""Independent Python model of spec/Reversal/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).

A follow-up case may carry an extra key, "before", with the balances that a round trip must
restore; the wrapper ignores it.
"""

FLAGSHIP = {
    "state": {"balances": [[1, 700], [2, 300], [3, 0]], "opening": [[1, 1000], [2, 0], [3, 0]],
              "journal": [{"id": 5, "lines": [[1, -300], [2, 300]]},
                          {"id": 6, "lines": [[1, -200], [3, 200]]}],
              "reversed": [6]},
    "command": {"kind": "reverse", "id": 5, "lines": []},
}


def gen_lines(rng, accts):
    n = rng.randint(2, 4)
    used, lines = [], []
    for _ in range(n - 1):
        a = rng.choice(used) if used and rng.random() < 0.3 else rng.choice(accts)
        used.append(a)
        amt = rng.choice([rng.randint(1, 20), rng.randint(1, 2000)]) * rng.choice([1, -1])
        lines.append([a, amt])
    last = -sum(x for _, x in lines)
    if last == 0:
        lines[0][1] += 1
        last = -1
    lines.append([rng.choice(accts), last])
    rng.shuffle(lines)
    return lines


def net_of(lines, a):
    return sum(x for b, x in lines if b == a)


def line_sum(lines):
    return sum(x for _, x in lines)


def active_net(state, a):
    return sum(net_of(e["lines"], a) for e in state["journal"] if e["id"] not in state["reversed"])


def gen_case(rng):
    accts = rng.sample(range(1, 40), rng.randint(2, 5))
    opening = {a: rng.choice([0, rng.randint(0, 100), rng.randint(-200, 3000)]) for a in accts}
    jids = rng.sample(range(1, 30), rng.randint(0, 5))
    journal = [{"id": i, "lines": gen_lines(rng, accts)} for i in jids]
    reversed_ = [i for i in jids if rng.random() < 0.35]
    rng.shuffle(reversed_)
    state = {"balances": [], "opening": [[a, opening[a]] for a in accts],
             "journal": journal, "reversed": reversed_}
    state["balances"] = [[a, opening[a] + active_net(state, a)] for a in accts]
    if rng.random() < 0.08:
        # Occasionally a state whose balances disagree with its journal.
        i = rng.randrange(len(accts))
        state["balances"][i][1] += rng.choice([1, -5, 100])
    active = [i for i in jids if i not in reversed_]
    if rng.random() < 0.5:
        cmd = {"kind": "post", "id": rng.choice([i for i in range(1, 60) if i not in jids]),
               "lines": gen_lines(rng, accts)}
        # Mutate into an invalid posting about 30% of the time.
        m = rng.random()
        if m < 0.04:
            cmd["lines"] = []
        elif m < 0.10:
            k = rng.randrange(len(cmd["lines"]))
            cmd["lines"][k][1] += rng.choice([1, -1, 50])
            if cmd["lines"][k][1] == 0:
                cmd["lines"][k][1] = 3
        elif m < 0.14:
            cmd["lines"].append([rng.choice(accts), 0])
        elif m < 0.22:
            k = rng.randrange(len(cmd["lines"]))
            cmd["lines"][k][0] = rng.choice([x for x in range(1, 50) if x not in accts])
        elif m < 0.30 and jids:
            cmd["id"] = rng.choice(jids)
    else:
        r = rng.random()
        if active and r < 0.70:
            i = rng.choice(active)
        elif reversed_ and r < 0.88:
            i = rng.choice(reversed_)
        else:
            i = rng.choice([x for x in range(1, 60) if x not in jids])
        cmd = {"kind": "reverse", "id": i, "lines": []}
    return {"state": state, "command": cmd}


def find_entry(journal, i):
    for e in journal:
        if e["id"] == i:
            return e
    return None


def first(pairs):
    d = {}
    for a, x in pairs:
        d.setdefault(a, x)
    return d


def valid(state, cmd):
    accts = [a for a, _ in state["balances"]]
    jids = [e["id"] for e in state["journal"]]
    if cmd["kind"] == "post":
        ls = cmd["lines"]
        return (len(ls) > 0 and all(a in accts for a, _ in ls) and all(x != 0 for _, x in ls)
                and line_sum(ls) == 0 and cmd["id"] not in jids
                and cmd["id"] not in state["reversed"])
    return cmd["id"] in jids and cmd["id"] not in state["reversed"]


def well_formed(state):
    accts = [a for a, _ in state["balances"]]
    jids = [e["id"] for e in state["journal"]]
    return (len(set(accts)) == len(accts) and len(set(jids)) == len(jids)
            and all(i in jids for i in state["reversed"])
            and all(all(a in accts for a, _ in e["lines"]) and line_sum(e["lines"]) == 0
                    for e in state["journal"]))


def consistent(state):
    op = first(state["opening"])
    return all(x == op.get(a, 0) + active_net(state, a) for a, x in state["balances"])


def shown(state):
    """The input state as the wrapper reports it back."""
    accts = [a for a, _ in state["balances"]]
    bal, op = first(state["balances"]), first(state["opening"])
    return {"balances": [[a, bal[a]] for a in accts], "opening": [[a, op.get(a, 0)] for a in accts],
            "journal": state["journal"], "reversed": state["reversed"]}


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    state, cmd = case["state"], case["command"]
    s2 = out["state"]
    s0 = shown(state)
    ok = out["outcome"] == "ok"
    accts = [a for a, _ in state["balances"]]
    bal, got = first(state["balances"]), first(s2["balances"])
    v = []
    if valid(state, cmd):
        if not ok:
            rid = "REQ-POST-SUCCEEDS" if cmd["kind"] == "post" else "REQ-REVERSE-SUCCEEDS"
            return [(rid, f"valid {cmd['kind']} was rejected")]
        rid = "REQ-POST-EFFECTS" if cmd["kind"] == "post" else "REQ-REVERSE-EFFECTS"
        if [a for a, _ in s2["balances"]] != accts:
            v.append((rid, "account universe changed"))
        if s2["opening"] != s0["opening"]:
            v.append((rid, "opening balances changed"))
        if cmd["kind"] == "post":
            e = {"id": cmd["id"], "lines": cmd["lines"]}
            if s2["journal"] != state["journal"] + [e]:
                v.append((rid, "journal is not the old journal with the entry appended"))
            if s2["reversed"] != state["reversed"]:
                v.append((rid, "reversed IDs changed"))
            delta = lambda a: net_of(cmd["lines"], a)
        else:
            e = find_entry(state["journal"], cmd["id"])
            if s2["journal"] != state["journal"]:
                v.append((rid, "journal changed"))
            if set(s2["reversed"]) != set(state["reversed"]) | {cmd["id"]}:
                v.append((rid, f"reversed IDs {sorted(set(s2['reversed']))}"))
            delta = lambda a: -net_of(e["lines"], a)
        for a in accts:
            if got.get(a) != bal[a] + delta(a):
                v.append((rid, f"account {a}: expected {bal[a] + delta(a)}, got {got.get(a)}"))
    else:
        if ok:
            v.append(("REQ-INVALID-NOOP", f"invalid {cmd['kind']} succeeded"))
        if s2 != s0:
            v.append(("REQ-INVALID-NOOP", "rejected command changed the state"))
    if well_formed(state):
        if ok and sum(got.get(a, 0) for a in accts) != sum(bal[a] for a in accts):
            v.append(("REQ-TRIAL-BALANCE", "sum of balances changed"))
        if not well_formed(s2):
            v.append(("REQ-WELL-FORMED", "state is no longer well-formed"))
        if consistent(state) and not consistent(s2):
            v.append(("REQ-CONSISTENT", "a balance differs from opening plus active entries"))
    if "before" in case and (not ok or s2["balances"] != case["before"]):
        v.append(("REQ-ROUNDTRIP", f"reversal after posting gave {out['outcome']} {s2['balances']}"))
    return v


def followup(case, out):
    """After a successful posting, reverse it and expect the earlier balances back; after a
    successful reversal, reverse again and expect a rejection."""
    if out.get("outcome") != "ok" or "before" in case:
        return None
    cmd = case["command"]
    nxt = {"state": out["state"], "command": {"kind": "reverse", "id": cmd["id"], "lines": []}}
    if cmd["kind"] == "post":
        nxt["before"] = shown(case["state"])["balances"]
        return nxt, "REQ-ROUNDTRIP"
    return nxt, "REQ-REVERSE-ONCE"


def describe(out):
    """Flagship summary: the balances and reversed IDs after the reversal."""
    bal = ",".join(f"{a}:{x}" for a, x in out["state"]["balances"])
    return f"{out['outcome']} balances={bal} reversed={sorted(out['state']['reversed'])}"
