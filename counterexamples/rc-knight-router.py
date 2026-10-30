"""Counterexample adapter for rc-knight-router (harness/counterexample.py).

A case is a code version and an event sequence. Every requirement quantifies over the code
version, an event sequence and parent or event values only, and the quantities it compares are
computed by the specification from the events and the router's own child orders, so each
instance is a prefix of the case's events: the adapter replays the oracle's walk to find the
event at which the requirement first fails and the parent order it fails for, and the kernel
runs the candidate's router over that prefix.
"""
from counterexample import boolean, lst, nat

BUILD = {"rlp": ".rlp", "legacy": ".legacy"}


def event_term(e):
    k = e["kind"]
    if k == "parent":
        return f"(Event.parent {nat(e['qty'])} {boolean(e['flag'])})"
    if k == "route":
        return f"(Event.route {nat(e['id'])} {nat(e['liq'])})"
    if k == "ack":
        return f"(Event.ack {nat(e['child'])})"
    return f"(Event.fill {nat(e['child'])} {nat(e['qty'])})"


def events(evs):
    return lst([event_term(e) for e in evs], "Event")


def first_failure(o, case, out, requirement):
    """(n, parent) for the first event at which the oracle's walk flags the requirement."""
    t = o.Truth()
    for n, (e, st) in enumerate(zip(case["events"], out["steps"])):
        kids = o._children(st)
        if requirement == "REQ-ROUTES-AVAILABLE" and e["kind"] == "route" and kids != t.expected_route(e["id"], e["liq"]):
            return n, e["id"]
        if requirement == "REQ-STOP-WHEN-FILLED":
            for c in kids:
                if t.executed(c["parent"]) == t.qty_of(c["parent"]):
                    return n, c["parent"]
        t.observe(e)
        t.record(kids)
        for p in sorted({k[0] for k in t.kids} | set(range(len(t.qty)))):
            if requirement == "REQ-NEVER-OVERROUTE" and t.sent(p) > t.qty_of(p):
                return n, p
            if requirement == "REQ-NO-EXCESS-EXECUTION" and t.executed(p) > t.qty_of(p):
                return n, p
        if requirement == "REQ-FILL-ACCOUNTING":
            cum = st.get("cum", [])
            for p in range(len(t.qty)):
                if p >= len(cum) or cum[p] != t.executed(p):
                    return n, p
    return None


def instance(task, requirement, case, out):
    o = task.oracle
    if "steps" not in (out or {}) or case.get("build") not in BUILD:
        return None
    B = BUILD[case["build"]]
    evs = case["events"]
    if requirement == "REQ-NORMAL-ORDER-ROUTED":
        flag = next((f for f in (True, False) if evs == o.normal_order(f)), None)
        if flag is None:
            return None
        return {"args": [B, boolean(flag)], "note": f"the normal order with flag {flag} on the {case['build']} build"}
    hit = first_failure(o, case, out, requirement)
    if hit is None:
        return None
    n, p = hit
    note = f"the first {n + 1} events on the {case['build']} build, parent {p}"
    if requirement == "REQ-ROUTES-AVAILABLE":
        e = evs[n]
        # ∀ b evs id liq: the routing opportunity after the first n events
        return {"args": [B, events(evs[:n]), nat(e["id"]), nat(e["liq"])], "note": note}
    if requirement == "REQ-STOP-WHEN-FILLED":
        # ∀ b evs e id: event n after the first n events
        return {"args": [B, events(evs[:n]), event_term(evs[n]), nat(p)], "note": note}
    # ∀ b evs id: after the first n + 1 events
    return {"args": [B, events(evs[:n + 1]), nat(p)], "note": note}
