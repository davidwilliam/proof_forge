"""Counterexample adapter for rw-moneyphp-allocate and rw-spliit-balances, which share the
allocation specification (harness/counterexample.py).

A case is an amount and a list of ratios. The requirements quantify over those and over the
returned shares; the shares are left to the kernel (`_`, pinned by `allocate amount ratios =
some shares`), so the refutation does not rely on the executable's output.
"""
from counterexample import int_, lst, nat


def instance(task, requirement, case, out, origin=None):
    A, X = int_(case["amount"]), lst([nat(r) for r in case["ratios"]], "Nat")
    note = f"amount {case['amount']}, ratios {case['ratios']}"
    if requirement in ("REQ-VALID-SUCCEEDS", "REQ-INVALID-FAILS"):
        return {"args": [A, X], "note": note}
    return {"args": [A, X, "_", "?"], "note": note}
