"""Independent Python model of spec/Grants/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
followup(case, out), describe(out).
"""

ROLES = ["admin", "editor", "viewer"]

FLAGSHIP = {
    "state": {"users": [1, 2, 3], "grants": [[1, "admin"], [2, "admin"], [2, "editor"], [3, "viewer"]]},
    "request": {"op": "revoke", "actor": 1, "target": 2, "role": "admin"},
}


def gen_case(rng):
    n = rng.randint(2, 6)
    users = rng.sample(range(1, 40), n)
    grants = set()
    for u in users:
        for q, p in (("admin", 0.25), ("editor", 0.4), ("viewer", 0.4)):
            if rng.random() < p:
                grants.add((u, q))
    admins = [u for u in users if (u, "admin") in grants]
    if not admins and rng.random() < 0.95:
        a = rng.choice(users)
        grants.add((a, "admin"))
        admins = [a]
    if len(admins) > 1 and rng.random() < 0.35:
        # Reduce to a single admin to exercise the last-admin rule.
        for u in admins[1:]:
            grants.discard((u, "admin"))
        admins = admins[:1]
    if rng.random() < 0.1:
        grants.add((99, "admin"))   # a grant outside the universe
    non_admins = [u for u in users if u not in admins]

    def pick_actor():
        x = rng.random()
        if admins and x < 0.9:
            return rng.choice(admins)
        if x < 0.97 and non_admins:
            return rng.choice(non_admins)
        return rng.choice([99, 0])

    op = "grant" if rng.random() < 0.5 else "revoke"
    actor = pick_actor()
    if op == "grant":
        free = sorted((u, q) for u in users for q in ROLES if (u, q) not in grants and u != actor)
        x = rng.random()
        if x < 0.1:
            target, role = actor, rng.choice(ROLES)
        elif x < 0.9 and free:
            target, role = rng.choice(free)
        else:
            target, role = rng.choice(users + [77]), rng.choice(ROLES)
    else:
        held = sorted((u, q) for (u, q) in grants if u in users)
        x = rng.random()
        if x < 0.12 and admins:
            # An admin steps down, often as the only admin.
            target, role = actor, "admin"
        elif x < 0.92 and held:
            target, role = rng.choice(held)
        else:
            target, role = rng.choice(users), rng.choice(ROLES)
    gl = sorted([list(g) for g in grants])
    rng.shuffle(gl)
    return {"state": {"users": users, "grants": gl},
            "request": {"op": op, "actor": actor, "target": target, "role": role}}


def has(state, u, q):
    return any(g[0] == u and g[1] == q for g in state["grants"])


def other_admin(state, u):
    return any(v != u and has(state, v, "admin") for v in state["users"])


def valid(state, req):
    users = state["users"]
    a, t, q = req["actor"], req["target"], req["role"]
    if not (a in users and t in users and has(state, a, "admin")):
        return False
    if req["op"] == "grant":
        return a != t and not has(state, t, q)
    return has(state, t, q) and (q != "admin" or other_admin(state, t))


def universe_grants(state):
    users = state["users"]
    return {(g[0], g[1]) for g in state["grants"] if g[0] in users}


def expected_grants(state, req):
    g = universe_grants(state)
    pair = (req["target"], req["role"])
    if req["op"] == "grant":
        return g | {pair}
    return g - {pair}


def any_admin(state):
    return any(has(state, u, "admin") for u in state["users"])


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    state, req = case["state"], case["request"]
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    v = []
    ok = out["outcome"] == "ok"
    s2 = out["state"]
    got = {(g[0], g[1]) for g in s2["grants"]}
    if any_admin(state) and not any(u in s2["users"] and (u, "admin") in got for u in s2["users"]):
        v.append(("REQ-LAST-ADMIN", "no admin remains"))
    if valid(state, req):
        if not ok:
            return v + [("REQ-VALID-SUCCEEDS", "valid command was rejected")]
        if s2["users"] != state["users"]:
            v.append(("REQ-EFFECTS", "user universe changed"))
        exp = expected_grants(state, req)
        pair = (req["target"], req["role"])
        if (pair in got) != (pair in exp):
            v.append(("REQ-EFFECTS", f"grant {pair} is {pair in got}, expected {pair in exp}"))
        other = (got ^ exp) - {pair}
        if other:
            v.append(("REQ-OTHERS-UNCHANGED", f"unrelated grants changed: {sorted(other)}"))
    else:
        if ok:
            v.append(("REQ-INVALID-NOOP", "invalid command succeeded"))
            if not (req["actor"] in state["users"] and has(state, req["actor"], "admin")):
                v.append(("REQ-AUTHORIZATION", f"non-admin {req['actor']} issued a command"))
            if req["op"] == "grant" and req["actor"] == req["target"]:
                v.append(("REQ-NO-SELF-GRANT", "actor granted a role to itself"))
        if s2["users"] != state["users"] or got != universe_grants(state):
            v.append(("REQ-INVALID-NOOP", "rejected command changed the state"))
    return v


def followup(case, out):
    """Resubmit a successful command against the resulting state."""
    if out.get("outcome") == "ok":
        return {"state": out["state"], "request": case["request"]}, "REQ-IDEMPOTENCY"
    return None


def describe(out):
    """Flagship summary: the outcome and the remaining admins."""
    admins = [g[0] for g in out["state"]["grants"] if g[1] == "admin"]
    return f"{out['outcome']} admins={admins}"
