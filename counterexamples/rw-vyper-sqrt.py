"""Counterexample adapter for rw-vyper-sqrt (harness/counterexample.py).

Cases are `{"op": "sqrt", "x": x}` with `x` a raw decimal. The instance is `x`; the result is left
to the kernel (`_`, pinned by the `?` hypothesis `sqrt x = some r`), and `IsDecimal x` is a `?`
hypothesis decided by evaluation.
"""
from counterexample import int_

BOUNDS = {"REQ-SQRT-NOT-ABOVE", "REQ-SQRT-NOT-BELOW"}


def instance(task, requirement, case, out):
    if case.get("op") != "sqrt":
        return None
    x = int_(case["x"])
    if requirement in BOUNDS:
        # ∀ x r : Int, IsDecimal x → sqrt x = some r → ...
        return {"args": [x, "_", "?", "?"], "note": f"sqrt at x = {case['x']} / 10^10"}
    if requirement == "REQ-SQRT-TOTAL":
        # ∀ x : Int, IsDecimal x → 0 ≤ x → (sqrt x).isSome
        return {"args": [x, "?", "?"], "note": f"sqrt at x = {case['x']} / 10^10"}
    if requirement == "REQ-SQRT-NEG-REVERTS":
        # ∀ x : Int, x < 0 → sqrt x = none
        return {"args": [x, "?"], "note": f"sqrt at x = {case['x']} / 10^10"}
    return None
