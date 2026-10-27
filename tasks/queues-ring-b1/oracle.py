"""Independent Python model of spec/RingBuffer/Spec.lean, used to test binaries.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out).
"""

FLAGSHIP = {
    "state": {"capacity": 4, "slots": [5, 6, 7, 8], "head": 3, "count": 2},
    "op": {"kind": "dequeue"},
}


def gen_case(rng):
    cap = 0 if rng.random() < 0.03 else rng.choice([1, 2, 3, 3, 4, 5, 7])
    r = rng.random()
    if r < 0.35:
        head = max(cap - 1, 0)
    elif r < 0.50:
        head = 0
    elif r < 0.53:
        head = cap + rng.randint(0, 1)
    else:
        head = rng.randint(0, max(cap - 1, 0))
    r = rng.random()
    if r < 0.12:
        count = cap
    elif r < 0.32:
        count = max(cap - 1, 0)
    elif r < 0.38:
        count = 0
    elif r < 0.40:
        count = cap + 1
    else:
        count = rng.randint(0, cap)
    slots = [rng.randint(0, 9) for _ in range(cap)]
    if rng.random() < 0.5:
        op = {"kind": "enqueue", "value": rng.randint(10, 99)}
    else:
        op = {"kind": "dequeue"}
    return {"state": {"capacity": cap, "slots": slots, "head": head, "count": count}, "op": op}


def mod(a, c):
    """Lean's Nat modulo: a % 0 = a."""
    return a if c == 0 else a % c


def get(slots, i):
    return slots[i] if 0 <= i < len(slots) else 0


def well_formed(s):
    return 0 < s["capacity"] and s["head"] < s["capacity"] and s["count"] <= s["capacity"]


def valid(s, op):
    if op["kind"] == "enqueue":
        return well_formed(s) and s["count"] < s["capacity"]
    return well_formed(s) and 0 < s["count"]


def contents(s):
    return [get(s["slots"], mod(s["head"] + i, s["capacity"])) for i in range(s["count"])]


def normalize(s):
    """The observable state: slots 0 to capacity - 1, missing slots read as 0."""
    return {"capacity": s["capacity"], "slots": [get(s["slots"], i) for i in range(s["capacity"])],
            "head": s["head"], "count": s["count"]}


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    s, op = case["state"], case["op"]
    s2 = out["state"]
    outcome = out["outcome"]
    v = []
    if valid(s, op):
        if outcome == "rejected":
            v.append(("REQ-VALID-SUCCEEDS", "valid operation was rejected"))
        elif op["kind"] == "enqueue":
            exp = normalize(s)
            exp["slots"][mod(s["head"] + s["count"], s["capacity"])] = op["value"]
            exp["count"] += 1
            if outcome != "ok":
                v.append(("REQ-ENQUEUE-EFFECTS", f"enqueue outcome {outcome}, expected ok"))
            if s2 != exp:
                v.append(("REQ-ENQUEUE-EFFECTS", f"state {s2}, expected {exp}"))
            if contents(s2) != contents(s) + [op["value"]]:
                v.append(("REQ-ENQUEUE-CONTENTS", f"contents {contents(s2)}, expected {contents(s) + [op['value']]}"))
        else:
            front = get(s["slots"], s["head"])
            exp = normalize(s)
            exp["head"] = mod(s["head"] + 1, s["capacity"])
            exp["count"] -= 1
            if outcome != "got" or out.get("value") != front:
                v.append(("REQ-DEQUEUE-EFFECTS", f"dequeue returned {outcome} {out.get('value')}, expected got {front}"))
            if s2 != exp:
                v.append(("REQ-DEQUEUE-EFFECTS", f"state {s2}, expected {exp}"))
            if outcome != "got" or contents(s) != [out.get("value")] + contents(s2):
                v.append(("REQ-DEQUEUE-CONTENTS", f"{contents(s)} is not {out.get('value')} followed by {contents(s2)}"))
    else:
        if outcome != "rejected":
            v.append(("REQ-INVALID-NOOP", f"invalid operation returned {outcome}"))
        if s2 != normalize(s):
            v.append(("REQ-INVALID-NOOP", f"rejected operation changed the state to {s2}"))
    if well_formed(s) and not well_formed(s2):
        v.append(("REQ-WELL-FORMED", f"state {s2} is not well formed"))
    inflow = [op["value"]] if op["kind"] == "enqueue" and outcome == "ok" else []
    outflow = [out.get("value")] if outcome == "got" else []
    if contents(s) + inflow != outflow + contents(s2):
        v.append(("REQ-FIFO", f"{contents(s)} + {inflow} != {outflow} + {contents(s2)}"))
    return v


def describe(out):
    """Flagship summary: the delivered value and the resulting head and count."""
    st = out["state"]
    return f"{out['outcome']} {out.get('value')} head={st['head']} count={st['count']}"
