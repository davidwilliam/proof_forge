"""Independent Python model of spec/Workflow/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out).
"""

STATUSES = ["draft", "review", "approved", "published", "archived"]
ROLES = ["guest", "author", "reviewer", "publisher"]

# The transition table: (role, src, dst).
EDGES = {
    ("author", "draft", "review"), ("author", "draft", "archived"), ("author", "review", "draft"),
    ("reviewer", "review", "approved"), ("reviewer", "review", "draft"),
    ("publisher", "approved", "published"), ("publisher", "approved", "draft"),
    ("publisher", "published", "archived"),
}

FLAGSHIP = {
    "state": {"docs": [[1, "approved", 10], [2, "draft", 20]],
              "users": [[5, "author"], [6, "reviewer"], [7, "publisher"]],
              "audit": [[1, 5, "draft", "review"], [1, 6, "review", "approved"]]},
    "request": {"actor": 7, "doc": 1, "kind": "move", "dst": "published", "body": 0},
}


def gen_case(rng):
    docs = rng.sample(range(1, 30), rng.randint(1, 5))
    uids = rng.sample(range(1, 20), rng.randint(2, 5))
    roles = {u: rng.choice(ROLES[1:] if rng.random() < 0.9 else ROLES) for u in uids}
    for q in ("author", "reviewer", "publisher"):
        free = [u for u in uids if list(roles.values()).count(roles[u]) > 1 or roles[u] == "guest"]
        if q not in roles.values() and rng.random() < 0.9:
            roles[rng.choice(free or uids)] = q
    status = {d: "draft" for d in docs}
    content = {d: rng.choice([0, rng.randint(0, 9), rng.randint(0, 1000)]) for d in docs}
    audit = []
    # Build a consistent history of valid moves, mostly forward along the workflow.
    forward = {"review", "approved", "published"}
    for _ in range(rng.randint(0, 12)):
        d = rng.choice(docs)
        opts = [(u, dst) for u in uids for (q, src, dst) in EDGES if q == roles[u] and src == status[d]]
        fwd = [o for o in opts if o[1] in forward]
        if not opts:
            continue
        back = [o for o in opts if o[1] != "archived" or rng.random() < 0.15]
        u, dst = rng.choice(fwd if fwd and rng.random() < 0.85 else (back or opts))
        audit.append([d, u, status[d], dst])
        status[d] = dst
    if rng.random() < 0.3:
        # Walk one document all the way to published.
        d = rng.choice(docs)
        by = {q: [u for u in uids if roles[u] == q] or uids for q in ("author", "reviewer", "publisher")}
        path = {"draft": [("author", "review"), ("reviewer", "approved"), ("publisher", "published")],
                "review": [("reviewer", "approved"), ("publisher", "published")],
                "approved": [("publisher", "published")]}.get(status[d], [])
        for q, dst in path:
            audit.append([d, rng.choice(by[q]), status[d], dst])
            status[d] = dst
    x = rng.random()
    if x < 0.08 and audit:
        audit.pop(rng.randrange(len(audit)))      # an inconsistent audit
    elif x < 0.12:
        d = rng.choice(docs)
        status[d] = rng.choice(STATUSES)          # a status not explained by the audit

    moves = [(d, u, dst) for d in docs for u in uids for (q, src, dst) in EDGES
             if q == roles[u] and src == status[d]]
    edits = [(d, u) for d in docs for u in uids if roles[u] == "author" and status[d] == "draft"]
    pubs = [u for u in uids if roles[u] == "publisher"]
    frozen = [d for d in docs if status[d] in ("published", "archived")]
    authors = [u for u in uids if roles[u] == "author"]
    unfit = [d for d in docs if status[d] != "draft"]
    req = {"actor": rng.choice(uids), "doc": rng.choice(docs), "kind": "move",
           "dst": rng.choice(STATUSES), "body": rng.randint(0, 1000)}
    x = rng.random()
    if 0.78 <= x < 0.87 and pubs and frozen:
        # A publisher acting on a published or archived document.
        dst = "draft" if rng.random() < 0.5 else rng.choice(STATUSES)
        pd = [d for d in frozen if status[d] == "published"]
        d = rng.choice(pd) if pd and rng.random() < 0.8 else rng.choice(frozen)
        req.update(actor=rng.choice(pubs), doc=d, dst=dst)
    elif 0.87 <= x < 0.94 and authors and unfit:
        # An author editing a document that is not a draft.
        rev = [d for d in unfit if status[d] == "review"]
        d = rng.choice(rev) if rev and rng.random() < 0.6 else rng.choice(unfit)
        req.update(kind="edit", actor=rng.choice(authors), doc=d)
    elif x >= 0.94:
        req["kind"] = rng.choice(["move", "edit"])
    elif edits and (rng.random() < 0.35 or not moves):
        d, u = rng.choice(edits)
        req.update(kind="edit", actor=u, doc=d)
    elif moves:
        req["doc"], req["actor"], req["dst"] = rng.choice(moves)
    if rng.random() < 0.02:
        req["doc"] = 99
    if rng.random() < 0.02:
        req["actor"] = 98
    return {"state": {"docs": [[d, status[d], content[d]] for d in docs],
                      "users": [[u, roles[u]] for u in uids], "audit": audit},
            "request": req}


def role_of(state, u):
    for x, q in state["users"]:
        if x == u:
            return q
    return "guest"


def doc_map(state):
    m = {}
    for d, st, c in state["docs"]:
        m.setdefault(d, (st, c))
    return m


def status_of(state, d):
    return doc_map(state).get(d, ("draft", 0))[0]


def valid(state, req):
    if req["doc"] not in [d for d, _, _ in state["docs"]]:
        return False
    if req["actor"] not in [u for u, _ in state["users"]]:
        return False
    q, st = role_of(state, req["actor"]), status_of(state, req["doc"])
    if req["kind"] == "move":
        return (q, st, req["dst"]) in EDGES
    return q == "author" and st == "draft"


def authorized(state, req):
    q, st = role_of(state, req["actor"]), status_of(state, req["doc"])
    if req["kind"] == "move":
        return (q, st, req["dst"]) in EDGES
    return q == "author" and st == "draft"


def replay(audit, d):
    st = "draft"
    for e in audit:
        if e[0] == d:
            st = e[3]
    return st


def consistent(state):
    return all(replay(state["audit"], d) == st for d, st, _ in state["docs"])


def expected(state, req):
    docs = []
    for d, st, c in state["docs"]:
        if d == req["doc"]:
            if req["kind"] == "move":
                st = req["dst"]
            else:
                c = req["body"]
        docs.append([d, st, c])
    audit = [list(e) for e in state["audit"]]
    if req["kind"] == "move":
        audit.append([req["doc"], req["actor"], status_of(state, req["doc"]), req["dst"]])
    return {"docs": docs, "users": [list(u) for u in state["users"]], "audit": audit}


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    state, req = case["state"], case["request"]
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    v = []
    ok = out["outcome"] == "ok"
    s2 = out["state"]
    before, after = doc_map(state), doc_map(s2)
    for d, (st, c) in before.items():
        st2, c2 = after.get(d, (None, None))
        if st in ("published", "archived") and c2 != c:
            v.append(("REQ-PUBLISHED-IMMUTABLE", f"content of {st} doc {d} changed from {c} to {c2}"))
        if st == "published" and st2 not in ("published", "archived"):
            v.append(("REQ-NO-UNPUBLISH", f"published doc {d} moved to {st2}"))
        if st == "archived" and st2 != "archived":
            v.append(("REQ-NO-UNPUBLISH", f"archived doc {d} moved to {st2}"))
    old_audit = [list(e) for e in state["audit"]]
    if s2["audit"][:len(old_audit)] != old_audit:
        v.append(("REQ-AUDIT-APPEND-ONLY", "old audit entries were changed"))
    if consistent(state) and [d for d, _, _ in s2["docs"]] == [d for d, _, _ in state["docs"]] and not consistent(s2):
        v.append(("REQ-AUDIT-CONSISTENT", "audit no longer replays to the document statuses"))
    if valid(state, req):
        if not ok:
            return v + [("REQ-VALID-SUCCEEDS", "valid request was rejected")]
        exp = expected(state, req)
        if [d for d, _, _ in s2["docs"]] != [d for d, _, _ in exp["docs"]]:
            v.append(("REQ-EFFECTS", "document universe changed"))
        for got_d, exp_d in zip(s2["docs"], exp["docs"]):
            if got_d != exp_d:
                rid = "REQ-EFFECTS" if exp_d[0] == req["doc"] else "REQ-SINGLE-DOC"
                v.append((rid, f"doc {exp_d[0]}: expected {exp_d[1:]}, got {got_d[1:]}"))
        if s2["users"] != exp["users"]:
            v.append(("REQ-EFFECTS", "users or roles changed"))
        if s2["audit"] != exp["audit"]:
            v.append(("REQ-EFFECTS", f"audit {s2['audit'][len(old_audit):]} appended, expected {exp['audit'][len(old_audit):]}"))
    else:
        if ok:
            v.append(("REQ-INVALID-NOOP", "invalid request succeeded"))
            if not authorized(state, req):
                v.append(("REQ-AUTHORIZATION", f"{req['kind']} by {role_of(state, req['actor'])} on a {status_of(state, req['doc'])} doc"))
        exp = {"docs": [list(d) for d in state["docs"]], "users": [list(u) for u in state["users"]],
               "audit": old_audit}
        if s2 != exp:
            v.append(("REQ-INVALID-NOOP", "rejected request changed the state"))
    return v


def describe(out):
    """Flagship summary: the outcome, the statuses and the last audit entry."""
    st = ",".join(f"{d}:{s}" for d, s, _ in out["state"]["docs"])
    last = out["state"]["audit"][-1] if out["state"]["audit"] else None
    return f"{out['outcome']} {st} last={last}"
