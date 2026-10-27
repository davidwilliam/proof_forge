"""Independent Python model of spec/Acl/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).
"""

FLAGSHIP = {
    "state": {"users": [1, 2],
              "entries": [["allow", 0, [7]], ["deny", 0, [7, 2]], ["allow", 1, [7, 2, 5]]],
              "log": []},
    "request": {"user": 1, "path": [7, 2, 5, 1]},
}


def rand_path(rng, depth):
    return [rng.randint(1, 3) for _ in range(depth)]


def gen_case(rng):
    users = rng.sample(range(1, 12), rng.randint(1, 5))
    if rng.random() < 0.05:
        users.append(0)
    x = rng.random()
    if x < 0.18:
        user = rng.choice([u for u in range(1, 15) if u not in users])
    elif x < 0.28:
        user = 0
    else:
        user = rng.choice([u for u in users if u != 0] or [1])
    path = rand_path(rng, rng.randint(0, 4))
    others = [u for u in users if u not in (0, user)] or [99]
    entries = []
    for _ in range(rng.randint(0, 7)):
        y = rng.random()
        subject = 0 if y < 0.35 else (user if y < 0.8 else rng.choice(others))
        if rng.random() < 0.8:
            p = path[:rng.randint(0, len(path))]          # a prefix: the entry can match
        else:
            p = rand_path(rng, rng.randint(0, 3))         # usually unrelated
        entries.append([rng.choice(["allow", "deny"]), subject, p])
    if entries and rng.random() < 0.3:
        # An opposing entry at the same depth as an existing one.
        e = rng.choice(entries)
        entries.insert(rng.randrange(len(entries) + 1),
                       ["deny" if e[0] == "allow" else "allow", rng.choice([0, user]), list(e[2])])
    log = [[rng.choice(users or [1]), rand_path(rng, rng.randint(0, 2)), rng.random() < 0.5]
           for _ in range(rng.randint(0, 3))]
    return {"state": {"users": users, "entries": entries, "log": log},
            "request": {"user": user, "path": path}}


def matches(e, req):
    p = e[2]
    return (e[1] == 0 or e[1] == req["user"]) and req["path"][:len(p)] == p


def valid(state, req):
    return req["user"] in state["users"] and req["user"] != 0


def has_allow(entries, req):
    return any(matches(a, req) and a[0] == "allow" for a in entries)


def overridden(entries, req):
    allows = [len(a[2]) for a in entries if matches(a, req) and a[0] == "allow"]
    return any(matches(d, req) and d[0] == "deny" and all(k <= len(d[2]) for k in allows)
               for d in entries)


def permitted(entries, req):
    denies = [len(d[2]) for d in entries if matches(d, req) and d[0] == "deny"]
    return any(matches(a, req) and a[0] == "allow" and all(k < len(a[2]) for k in denies)
               for a in entries)


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    if "prior_outcome" in case:
        if out["outcome"] != case["prior_outcome"]:
            return [("REQ-ORDER-INDEPENDENT",
                     f"reversed entries give {out['outcome']}, original order gave {case['prior_outcome']}")]
        return []
    state, req = case["state"], case["request"]
    v = []
    o = out["outcome"]
    s2 = out["state"]
    ents = state["entries"]
    if valid(state, req):
        if o == "rejected":
            return [("REQ-VALID-ANSWERED", "valid check was rejected")]
        exp = "granted" if permitted(ents, req) else "denied"
        if o != exp:
            if exp == "granted":
                v.append(("REQ-SPECIFIC-ALLOW", "a strictly more specific allow entry matches, but access was denied"))
                v.append(("REQ-DENIAL-EXPLAINED", "denied without a covering deny entry"))
            else:
                v.append(("REQ-GRANT-JUSTIFIED", "granted without a strictly more specific allow entry"))
                if not has_allow(ents, req):
                    v.append(("REQ-DEFAULT-DENY", "granted without any matching allow entry"))
                if overridden(ents, req):
                    v.append(("REQ-DENY-OVERRIDES", "granted although a deny entry is at least as specific as every allow"))
        if s2["users"] != state["users"] or s2["entries"] != ents:
            v.append(("REQ-EFFECTS", "users or access list changed"))
        want_log = state["log"] + [[req["user"], req["path"], o == "granted"]]
        if s2["log"] != want_log:
            v.append(("REQ-EFFECTS", f"log {s2['log']} != {want_log}"))
    else:
        if o != "rejected":
            v.append(("REQ-INVALID-NOOP", f"invalid check answered {o}"))
        if s2 != state:
            v.append(("REQ-INVALID-NOOP", "rejected check changed the state"))
    return v


def followup(case, out):
    """Re-run an answered check with the access list reversed; the outcome must not change."""
    if out.get("outcome") in ("granted", "denied") and len(case["state"]["entries"]) > 1:
        st = dict(case["state"])
        st["entries"] = list(reversed(st["entries"]))
        return ({"state": st, "request": case["request"], "prior_outcome": out["outcome"]},
                "REQ-ORDER-INDEPENDENT")
    return None


def describe(out):
    """Flagship summary: the outcome and the last log record."""
    log = out["state"]["log"]
    return f"{out['outcome']} last={log[-1] if log else None}"
