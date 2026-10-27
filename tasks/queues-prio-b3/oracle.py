"""Independent Python model of spec/PrioQueue/Spec.lean, used to test binaries.

Entries are [prio, value] pairs. Interface used by harness/binary_check.py: FLAGSHIP,
gen_case(rng), check(case, out), describe(out).
"""

FLAGSHIP = {
    "state": {"capacity": 5, "items": [[1, 10], [2, 20], [2, 21], [3, 30]]},
    "op": {"kind": "insert", "prio": 2, "value": 22},
}


def gen_case(rng):
    cap = 0 if rng.random() < 0.03 else rng.choice([1, 2, 3, 4, 5, 6])
    r = rng.random()
    if r < 0.15:
        n = cap
    elif r < 0.35:
        n = max(cap - 1, 0)
    elif r < 0.41:
        n = 0
    elif r < 0.43:
        n = cap + 1
    else:
        n = rng.randint(0, cap)
    prios = sorted(rng.randint(0, 3) for _ in range(n))
    vals = rng.sample(range(10, 100), n + 1)
    items = [[p, v] for p, v in zip(prios, vals)]
    if n >= 2 and rng.random() < 0.08:
        i = rng.randrange(n - 1)
        if items[i][0] != items[-1][0]:
            items[i], items[-1] = items[-1], items[i]
    if rng.random() < 0.55:
        op = {"kind": "insert", "prio": rng.randint(0, 3), "value": vals[-1]}
    else:
        op = {"kind": "pop"}
    return {"state": {"capacity": cap, "items": items}, "op": op}


def is_sorted(items):
    return all(items[i][0] <= items[i + 1][0] for i in range(len(items) - 1))


def valid(s, op):
    if op["kind"] == "insert":
        return is_sorted(s["items"]) and len(s["items"]) < s["capacity"]
    return is_sorted(s["items"]) and len(s["items"]) > 0


def class_of(p, items):
    return [e for e in items if e[0] == p]


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    s, op = case["state"], case["op"]
    s2 = out["state"]
    outcome = out["outcome"]
    items, items2 = s["items"], s2["items"]
    v = []
    if valid(s, op):
        if outcome == "rejected":
            v.append(("REQ-VALID-SUCCEEDS", "valid operation was rejected"))
        elif op["kind"] == "insert":
            e = [op["prio"], op["value"]]
            k = 0
            while k < len(items) and items[k][0] <= e[0]:
                k += 1
            exp = {"capacity": s["capacity"], "items": items[:k] + [e] + items[k:]}
            if outcome != "ok":
                v.append(("REQ-INSERT-EFFECTS", f"insert outcome {outcome}, expected ok"))
            if s2 != exp:
                v.append(("REQ-INSERT-EFFECTS", f"state {s2}, expected {exp}"))
        else:
            k = min(range(len(items)), key=lambda i: (items[i][0], i))
            e = items[k]
            exp = {"capacity": s["capacity"], "items": items[:k] + items[k + 1:]}
            if outcome != "got" or out.get("entry") != e:
                v.append(("REQ-POP-EFFECTS", f"pop returned {outcome} {out.get('entry')}, expected got {e}"))
            if s2 != exp:
                v.append(("REQ-POP-EFFECTS", f"state {s2}, expected {exp}"))
    else:
        if outcome != "rejected":
            v.append(("REQ-INVALID-NOOP", f"invalid operation returned {outcome}"))
        if s2 != s:
            v.append(("REQ-INVALID-NOOP", f"rejected operation changed the state to {s2}"))
    if outcome == "got" and op["kind"] == "pop":
        got = out.get("entry")
        if got is None or any(got[0] > x[0] for x in items2):
            v.append(("REQ-POP-MIN", f"popped {got} but {items2} remain"))
    if len(items) <= s["capacity"] and len(items2) > s2["capacity"]:
        v.append(("REQ-CAPACITY", f"{len(items2)} entries exceed capacity {s2['capacity']}"))
    if is_sorted(items) and not is_sorted(items2):
        v.append(("REQ-SORTED", f"{items2} is not in service order"))
    inflow = [[op["prio"], op["value"]]] if op["kind"] == "insert" and outcome == "ok" else []
    outflow = [out.get("entry")] if outcome == "got" else []
    for p in sorted({e[0] for e in items + items2 + inflow + outflow if e}):
        if class_of(p, items) + class_of(p, inflow) != class_of(p, outflow) + class_of(p, items2):
            v.append(("REQ-FIFO-TIES", f"priority {p}: {class_of(p, items)} + {class_of(p, inflow)} != {class_of(p, outflow)} + {class_of(p, items2)}"))
    return v


def describe(out):
    """Flagship summary: the resulting service order."""
    return " ".join(f"{p}:{x}" for p, x in out["state"]["items"])
