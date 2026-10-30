"""Counterexample adapter for rw-gomoney-split (harness/counterexample.py).

A case is an amount and a number of parties. The requirements quantify over those and over the
returned shares; the shares are left to the kernel (`_`, pinned by `split amount n = some
shares`), so the refutation does not rely on the executable's output.
"""
from counterexample import int_, nat


def instance(task, requirement, case, out, origin=None):
    A, N = int_(case["amount"]), nat(case["n"])
    note = f"amount {case['amount']} among {case['n']} parties"
    if requirement == "REQ-VALID-SUCCEEDS":
        return {"args": [A, N], "note": note}
    if requirement == "REQ-INVALID-FAILS":
        return {"args": [A], "note": note} if case["n"] == 0 else None
    return {"args": [A, N, "_", "?"], "note": note}
