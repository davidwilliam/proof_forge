"""Counterexample adapter for the queues-ring tasks (harness/counterexample.py).

A case is one state and one operation. The state's slots are a function `buf : Nat → Nat`, so
two states cannot be compared by `decide`; the requirements that equate whole states
(REQ-INVALID-NOOP, REQ-ENQUEUE-EFFECTS, REQ-DEQUEUE-EFFECTS) are refuted on what the executable
reports of a state: capacity, head, count and slots 0 to capacity - 1. REQ-DEQUEUE-CONTENTS is
existential; the proof reads the dequeued value off the outcome the kernel computes.
"""
from counterexample import lst, nat, struct

OBSERVE = [
    "fun p : Outcome × State => p.1",
    "fun p : Outcome × State => p.2.capacity",
    "fun p : Outcome × State => p.2.head",
    "fun p : Outcome × State => p.2.count",
    "fun p : Outcome × State => (List.range p.2.capacity).map p.2.buf",
]


def instance(task, requirement, case, out, origin=None):
    s, op = case["state"], case["op"]
    S = struct({"capacity": nat(s["capacity"]), "buf": f"(fun i => {lst([nat(x) for x in s['slots']])}.getD i 0)",
                "head": nat(s["head"]), "count": nat(s["count"])}, "State")
    OP = f"(Op.enqueue {nat(op['value'])})" if op["kind"] == "enqueue" else "Op.dequeue"
    note = f"the case's state and {op['kind']}"
    if requirement in ("REQ-VALID-SUCCEEDS", "REQ-WELL-FORMED"):
        return {"args": [S, OP], "note": note}
    if requirement == "REQ-INVALID-NOOP":
        return {"args": [S, OP, "?"], "observe": OBSERVE, "note": note}
    if requirement == "REQ-FIFO":
        return {"args": [S, f"[{OP}]"], "note": note}
    if requirement == "REQ-ENQUEUE-CONTENTS" and op["kind"] == "enqueue":
        return {"args": [S, nat(op["value"])], "note": note}
    if requirement == "REQ-ENQUEUE-EFFECTS" and op["kind"] == "enqueue":
        return {"args": [S, nat(op["value"]), "?"], "observe": OBSERVE, "note": note}
    if requirement == "REQ-DEQUEUE-EFFECTS" and op["kind"] == "dequeue":
        return {"args": [S, "?"], "observe": OBSERVE, "note": note}
    if requirement == "REQ-DEQUEUE-CONTENTS" and op["kind"] == "dequeue":
        return {"note": note, "proof": f"""intro h
obtain ⟨x, h1, h2⟩ := h {S} (by decide)
have e := congrArg (fun o : Outcome => match o with | .got y => y | _ => 0) h1
dsimp only at e
subst e
revert h1 h2
first | decide | decide +kernel"""}
    return None
