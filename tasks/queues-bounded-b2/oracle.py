"""Independent Python model of spec/BoundedQueue/Spec.lean, used to test binaries.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out).
"""

FLAGSHIP = {
    "state": {"capacity": 3, "items": [4, 7, 9], "served": 2},
    "op": {"kind": "enqueue", "value": 5},
}


def gen_case(rng):
    cap = 0 if rng.random() < 0.03 else rng.choice([1, 1, 2, 2, 3, 3, 4, 5, 6, 8])
    r = rng.random()
    if r < 0.18:
        n = cap
    elif r < 0.33:
        n = max(cap - 1, 0)
    elif r < 0.39:
        n = 0
    elif r < 0.42:
        n = cap + 1
    else:
        n = rng.randint(0, cap)
    items = [rng.randint(0, 9) for _ in range(n)]
    served = rng.choice([0, rng.randint(0, 20)])
    if rng.random() < 0.55:
        op = {"kind": "enqueue", "value": rng.randint(0, 9)}
    else:
        op = {"kind": "dequeue"}
    return {"state": {"capacity": cap, "items": items, "served": served}, "op": op}


def valid(state, op):
    if op["kind"] == "enqueue":
        return len(state["items"]) < state["capacity"]
    return len(state["items"]) > 0


def flows(op, out):
    inflow = [op["value"]] if op["kind"] == "enqueue" and out.get("outcome") == "ok" else []
    outflow = [out.get("value")] if out.get("outcome") == "got" else []
    return inflow, outflow


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    state, op = case["state"], case["op"]
    s2 = out["state"]
    outcome = out["outcome"]
    v = []
    if valid(state, op):
        if outcome == "rejected":
            v.append(("REQ-VALID-SUCCEEDS", "valid operation was rejected"))
        elif op["kind"] == "enqueue":
            exp = {"capacity": state["capacity"], "items": state["items"] + [op["value"]],
                   "served": state["served"]}
            if outcome != "ok":
                v.append(("REQ-ENQUEUE-EFFECTS", f"enqueue outcome {outcome}, expected ok"))
            if s2 != exp:
                v.append(("REQ-ENQUEUE-EFFECTS", f"state {s2}, expected {exp}"))
        else:
            front = state["items"][0]
            exp = {"capacity": state["capacity"], "items": state["items"][1:],
                   "served": state["served"] + 1}
            if outcome != "got" or out.get("value") != front:
                v.append(("REQ-DEQUEUE-EFFECTS", f"dequeue returned {outcome} {out.get('value')}, expected got {front}"))
            if s2 != exp:
                v.append(("REQ-DEQUEUE-EFFECTS", f"state {s2}, expected {exp}"))
    else:
        if outcome != "rejected":
            v.append(("REQ-INVALID-NOOP", f"invalid operation returned {outcome}"))
        if s2 != state:
            v.append(("REQ-INVALID-NOOP", f"rejected operation changed the state to {s2}"))
    if len(state["items"]) <= state["capacity"] and len(s2["items"]) > s2["capacity"]:
        v.append(("REQ-CAPACITY", f"{len(s2['items'])} items exceed capacity {s2['capacity']}"))
    inflow, outflow = flows(op, out)
    if state["items"] + inflow != outflow + s2["items"]:
        v.append(("REQ-FIFO", f"{state['items']} + {inflow} != {outflow} + {s2['items']}"))
    return v


def describe(out):
    """Flagship summary: the outcome and the resulting contents."""
    return f"{out['outcome']} {out['state']['items']}"
