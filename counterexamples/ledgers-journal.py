"""Counterexample adapter for the ledgers-journal tasks (harness/counterexample.py).

A case is one state and one journal entry. The state is written out as the wrapper builds it
(`toState` in app/Main.lean). Balances are a function, so whole states are compared on what the
executable reports of them (accounts, their balances, posted IDs), and the frame conditions over
every account or ID (REQ-EFFECTS, REQ-IDEMPOTENCY) are refuted at one of them, tried in turn. A
REQ-IDEMPOTENCY witness found on the repeated posting is refuted at the state before the first
posting (the witness's origin).
"""
from counterexample import int_, lst, nat, struct

OBSERVE = "fun p : Outcome × State => (p.1, p.2.accounts, p.2.accounts.map p.2.balance, p.2.posted)"


def state_term(s):
    bal = lst([f"({nat(a)}, {int_(v)})" for a, v in s["balances"]], "(Nat × Int)")
    return struct({"accounts": lst([nat(a) for a, _ in s["balances"]], "Nat"),
                   "balance": f"(fun a => ({bal}.lookup a).getD 0)",
                   "posted": lst([nat(x) for x in s["posted"]], "Nat")}, "State")


def entry_term(e):
    return struct({"id": nat(e["id"]), "lines": lst([f"({nat(a)}, {int_(v)})" for a, v in e["lines"]], "(Nat × Int)")},
                  "Entry")


def first(alts):
    return "first\n" + "\n".join(f"  | {a}" for a in alts)


def instance(task, requirement, case, out, origin=None):
    s, e = case["state"], case["entry"]
    S, E = state_term(s), entry_term(e)
    note = "the case's state and entry"
    if requirement in ("REQ-VALID-SUCCEEDS", "REQ-KNOWN-ACCOUNTS", "REQ-BALANCED", "REQ-TRIAL-BALANCE"):
        return {"args": [S, E], "note": note}
    if requirement == "REQ-INVALID-NOOP":
        return {"args": [S, E, "?"], "observe": OBSERVE, "note": note}
    accts = sorted({a for a, _ in s["balances"]} | {a for a, _ in e["lines"]})
    if requirement == "REQ-EFFECTS":
        alts = ["exact absurd hx.1 (by decide)"] + [f"exact absurd (hx.2 {nat(a)}) (by decide)" for a in accts]
        return {"note": note, "proof": f"intro h\nhave hx := h {S} {E} (by decide)\n" + first(alts)}
    if requirement == "REQ-IDEMPOTENCY":
        if origin:
            S0 = state_term(origin["input"]["state"])
            return {"note": "the repeated posting of the case's entry after it succeeded",
                    "proof": f"intro h\nhave hx := congrArg ({OBSERVE}) (h {S0} {E} (by decide)).2\nrevert hx\ndecide"}
        ids = sorted({e["id"], *s["posted"], *((out or {}).get("state") or {}).get("posted", [])})
        alts = [f"exact absurd ((hx.1 {nat(x)}).mp) (by decide)" for x in ids]
        alts += [f"exact absurd ((hx.1 {nat(x)}).mpr) (by decide)" for x in ids]
        alts += [f"(have hy := congrArg ({OBSERVE}) hx.2; revert hy; decide)"]
        return {"note": note, "proof": f"intro h\nhave hx := h {S} {E} (by decide)\n" + first(alts)}
    return None
