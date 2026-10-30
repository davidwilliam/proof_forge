"""Counterexample adapter for the payout flagship (`formal/`, and the payouts-flagship tasks,
which share its specification; harness/counterexample.py).

A case is one state and one payout request. The state is written out as the wrapper builds it
(`toState` in app/Main.lean): balances looked up in the case's list, authorization as membership
in the case's pairs. Balances and authorization are functions, so whole states are compared on
what the executable reports of them (accounts, their balances, authorization between them, the
applied IDs), and the frame conditions over every account (REQ-EFFECTS, REQ-IDEMPOTENCY) are
refuted at one account, pair or ID, tried in turn.
"""
from counterexample import int_, lst, nat, struct

OBSERVE = ("fun p : Outcome × State => (p.1, p.2.accounts, p.2.accounts.map p.2.balance, "
           "p.2.accounts.flatMap (fun a => p.2.accounts.map (fun b => p.2.auth a b)), p.2.applied)")


def state_term(s):
    bal = lst([f"({nat(a)}, {int_(v)})" for a, v in s["balances"]], "(Nat × Int)")
    auth = lst([f"({nat(a)}, {nat(b)})" for a, b in s["auth"]], "(Nat × Nat)")
    return struct({"accounts": lst([nat(a) for a, _ in s["balances"]], "Nat"),
                   "balance": f"(fun a => ({bal}.lookup a).getD 0)",
                   "auth": f"(fun req src => {auth}.any (fun p => p.1 == req && p.2 == src))",
                   "applied": lst([nat(x) for x in s["applied"]], "Nat")}, "State")


def request_term(r):
    return struct({"txId": nat(r["txId"]), "requester": nat(r["requester"]), "source": nat(r["source"]),
                   "recipients": lst([nat(x) for x in r["recipients"]], "Nat"), "amount": nat(r["amount"])}, "Request")


def first(alts):
    return "first\n" + "\n".join(f"  | {a}" for a in alts)


def instance(task, requirement, case, out, origin=None):
    s, r = case["state"], case["request"]
    S, R = state_term(s), request_term(r)
    note = "the case's state and request"
    if requirement in ("REQ-VALID-SUCCEEDS", "REQ-FAIR-SHARES", "REQ-CONSERVATION", "REQ-NONNEGATIVE",
                       "REQ-AUTHORIZATION"):
        return {"args": [S, R], "note": note}
    if requirement == "REQ-INVALID-NOOP":
        return {"args": [S, R, "?"], "observe": OBSERVE, "note": note}
    accts = sorted({a for a, _ in s["balances"]} | {r["source"], r["requester"], *r["recipients"]})
    if requirement == "REQ-EFFECTS":
        alts = ["exact absurd hx.1 (by decide)"]
        alts += [f"exact absurd (hx.2.2 {nat(a)}) (by decide)" for a in accts]
        alts += [f"exact absurd (congrFun (congrFun hx.2.1 {nat(a)}) {nat(b)}) (by decide)" for a in accts for b in accts]
        return {"note": note, "proof": f"intro h\nhave hx := h {S} {R} (by decide)\n" + first(alts)}
    if requirement == "REQ-IDEMPOTENCY":
        if origin:
            # The follow-up case resubmits the request to the state the first submission produced.
            S0 = state_term(origin["input"]["state"])
            return {"note": "the resubmission of the case's request after it succeeded",
                    "proof": f"intro h\nhave hx := congrArg ({OBSERVE}) (h {S0} {R} (by decide)).2\nrevert hx\ndecide"}
        ids = sorted({r["txId"], *s["applied"], *((out or {}).get("state") or {}).get("applied", [])})
        alts = [f"exact absurd ((hx.1 {nat(x)}).mp) (by decide)" for x in ids]
        alts += [f"exact absurd ((hx.1 {nat(x)}).mpr) (by decide)" for x in ids]
        alts += [f"(have hy := congrArg ({OBSERVE}) hx.2; revert hy; decide)"]
        return {"note": note, "proof": f"intro h\nhave hx := h {S} {R} (by decide)\n" + first(alts)}
    return None
