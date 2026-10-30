"""Counterexample adapter for the rate-limiters-bucket tasks (harness/counterexample.py).

A case is one state and one request; every requirement is `∀ s r, ...` over them, and the state
has decidable equality, so the instance is the case itself.
"""
from counterexample import nat, struct


def instance(task, requirement, case, out, origin=None):
    s, r = case["state"], case["request"]
    S = struct({k: nat(s[k]) for k in ("capacity", "rate", "tokens", "last")}, "State")
    R = struct({k: nat(r[k]) for k in ("time", "cost")}, "Request")
    return {"args": [S, R], "note": "the case's state and request"}
