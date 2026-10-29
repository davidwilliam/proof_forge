"""Independent Python model of spec/OrderRouter/Spec.lean, used to test binaries.

The model reconstructs from the SEC findings in Release No. 34-70694 (not from Knight's
code) what happened in a run: parent orders and their quantities, and every child order the
router sent with the shares executed at the venue. Each case is one server's code version
and one event sequence; the binary reports, per event, the child orders sent and the
router's cumulative executed quantity per parent order.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out).
"""


def normal_order(flag):
    return [{"kind": "parent", "qty": 300, "flag": flag},
            {"kind": "route", "id": 0, "liq": 100}, {"kind": "fill", "child": 0, "qty": 100},
            {"kind": "route", "id": 0, "liq": 100}, {"kind": "fill", "child": 1, "qty": 100},
            {"kind": "route", "id": 0, "liq": 100}, {"kind": "fill", "child": 2, "qty": 100},
            {"kind": "route", "id": 0, "liq": 100}]


FLAGSHIP = {"build": "legacy", "events": normal_order(True)}


class Truth:
    """What happened at the venues: Truth.observe and Truth.record in Spec.lean."""

    def __init__(self):
        self.qty = []      # quantity per parent order
        self.kids = []     # [parent, qty, done] per child order, in the order sent

    def qty_of(self, i):
        return self.qty[i] if 0 <= i < len(self.qty) else 0

    def sent(self, i):
        return sum(k[1] for k in self.kids if k[0] == i)

    def executed(self, i):
        return sum(k[2] for k in self.kids if k[0] == i)

    def expected_route(self, i, liq):
        m = min(liq, max(self.qty_of(i) - self.sent(i), 0))
        return [{"parent": i, "qty": m}] if i < len(self.qty) and m > 0 else []

    def observe(self, e):
        if e["kind"] == "parent":
            self.qty.append(e["qty"])
        elif e["kind"] == "fill" and 0 <= e["child"] < len(self.kids):
            k = self.kids[e["child"]]
            k[2] += min(e["qty"], max(k[1] - k[2], 0))

    def record(self, out):
        for c in out:
            self.kids.append([c["parent"], c["qty"], 0])


def _children(out_step):
    return [{"parent": c.get("parent"), "qty": c.get("qty")} for c in out_step.get("children", [])]


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out or not isinstance(out.get("steps"), list):
        return [("WRAPPER", "binary could not parse input")]
    evs, steps = case["events"], out["steps"]
    if len(steps) != len(evs):
        return [("WRAPPER", f"{len(steps)} steps for {len(evs)} events")]
    t, v, seen = Truth(), [], set()

    def flag(rid, msg):
        if rid not in seen:
            seen.add(rid)
            v.append((rid, msg))

    for n, (e, st) in enumerate(zip(evs, steps)):
        kids = _children(st)
        if e["kind"] == "route":
            exp = t.expected_route(e["id"], e["liq"])
            if kids != exp:
                flag("REQ-ROUTES-AVAILABLE", f"event {n} route {e['id']} liq {e['liq']}: sent {kids}, expected {exp}")
        for c in kids:
            p = c["parent"]
            if t.executed(p) == t.qty_of(p):
                flag("REQ-STOP-WHEN-FILLED", f"event {n}: child order of {c['qty']} shares for parent {p}, "
                                             f"which was already executed in full ({t.executed(p)} of {t.qty_of(p)})")
        t.observe(e)
        t.record(kids)
        for p in sorted({k[0] for k in t.kids} | set(range(len(t.qty)))):
            if t.sent(p) > t.qty_of(p):
                flag("REQ-NEVER-OVERROUTE", f"after event {n}: {t.sent(p)} shares sent in "
                                            f"{sum(1 for k in t.kids if k[0] == p)} child orders for parent {p} "
                                            f"of {t.qty_of(p)} shares")
            if t.executed(p) > t.qty_of(p):
                flag("REQ-NO-EXCESS-EXECUTION", f"after event {n}: {t.executed(p)} shares executed for parent "
                                                f"{p} of {t.qty_of(p)} shares")
        cum = st.get("cum", [])
        exp_cum = [t.executed(p) for p in range(len(t.qty))]
        if cum != exp_cum:
            flag("REQ-FILL-ACCOUNTING", f"after event {n}: router cumulative quantity {cum}, executed {exp_cum}")
    if evs in (normal_order(True), normal_order(False)):
        if t.kids != [[0, 100, 100]] * 3 or t.executed(0) != 300:
            flag("REQ-NORMAL-ORDER-ROUTED", f"normal 300-share order: child orders {[k[:2] for k in t.kids]}, "
                                            f"{t.executed(0)} shares executed")
    return v


def _qty(rng):
    return rng.choice([0, 1, 100, 300, rng.randint(1, 1000), rng.randint(1, 1000)])


def gen_case(rng):
    """One server and one event sequence. About a third of the cases are flagged orders with
    repeated routing opportunities and execution reports, as in the order; the rest are
    random interleavings with unknown child orders, oversized reports and acknowledgements."""
    build = rng.choice(["rlp", "legacy"])
    r = rng.random()
    if r < 0.12:
        return {"build": build, "events": normal_order(rng.random() < 0.5)}
    t = Truth()   # a correct router's run, to aim reports at child orders that exist
    evs = []

    def emit(e):
        out = t.expected_route(e["id"], e["liq"]) if e["kind"] == "route" else []
        t.observe(e)
        t.record(out)
        evs.append(e)

    if r < 0.40:
        q = rng.choice([1, 100, 100, 300, rng.randint(1, 1000)])
        emit({"kind": "parent", "qty": q, "flag": rng.random() < 0.7})
        for _ in range(rng.randint(1, 8)):
            emit({"kind": "route", "id": 0, "liq": rng.choice([q, max(q // 2, 1), rng.randint(1, 1000)])})
            if rng.random() < 0.8:
                emit({"kind": "fill", "child": max(len(t.kids) - 1, 0), "qty": rng.choice([q, rng.randint(1, 1000)])})
        return {"build": build, "events": evs}
    for _ in range(rng.randint(1, 3)):
        emit({"kind": "parent", "qty": _qty(rng), "flag": rng.random() < 0.5})
    for _ in range(rng.randint(1, 30)):
        k = rng.random()
        if k < 0.08:
            emit({"kind": "parent", "qty": _qty(rng), "flag": rng.random() < 0.5})
        elif k < 0.50:
            i = rng.randint(0, len(t.qty)) if rng.random() < 0.1 else rng.randrange(len(t.qty))
            emit({"kind": "route", "id": i, "liq": rng.choice([0, 1, 100, rng.randint(0, 1000)])})
        elif k < 0.90:
            c = rng.randint(0, len(t.kids) + 1) if (not t.kids or rng.random() < 0.1) else rng.randrange(len(t.kids))
            emit({"kind": "fill", "child": c, "qty": rng.choice([1, 100, rng.randint(0, 1000), 10**6])})
        else:
            emit({"kind": "ack", "child": rng.randint(0, len(t.kids) + 1)})
    return {"build": build, "events": evs}


def describe(out):
    """Flagship summary: child orders sent and the router's cumulative quantity at the end."""
    steps = out.get("steps", [])
    kids = [c for s in steps for c in s.get("children", [])]
    cum = steps[-1].get("cum") if steps else None
    return f"{len(kids)} child orders, {sum(c.get('qty', 0) for c in kids)} shares sent, cumulative quantity {cum}"
