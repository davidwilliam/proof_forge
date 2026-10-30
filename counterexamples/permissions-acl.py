"""Counterexample adapter for the permissions-acl tasks (harness/counterexample.py).

A case is one state (users, access list, log) and one check. Every part of the state is a list,
so every requirement is decidable once instantiated at the case. REQ-ORDER-INDEPENDENT is found
on the follow-up case, which reverses the access list; it is instantiated at that state with the
list reversed back (the original order) as the permutation.
"""
from counterexample import boolean, lst, nat, struct

EFFECT = {"allow": ".allow", "deny": ".deny"}


def path(p):
    return lst([nat(x) for x in p], "Nat")


def entry(e):
    return f"⟨{EFFECT[e[0]]}, {nat(e[1])}, {path(e[2])}⟩"


def state_term(s):
    return struct({"users": lst([nat(u) for u in s["users"]], "Nat"),
                   "entries": lst([entry(e) for e in s["entries"]], "Entry"),
                   "log": lst([f"⟨{nat(x[0])}, {path(x[1])}, {boolean(x[2])}⟩" for x in s["log"]], "Record")},
                  "State")


def instance(task, requirement, case, out, origin=None):
    s, r = case["state"], case["request"]
    S = state_term(s)
    R = struct({"user": nat(r["user"]), "path": path(r["path"])}, "Request")
    if requirement == "REQ-ORDER-INDEPENDENT":
        L = lst([entry(e) for e in reversed(s["entries"])], "Entry")
        return {"args": [S, R, L], "note": "the follow-up case's state, with the access list reversed back"}
    return {"args": [S, R], "note": "the case's state and check"}
