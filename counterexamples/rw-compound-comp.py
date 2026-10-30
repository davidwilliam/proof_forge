"""Counterexample adapter for rw-compound-comp (harness/counterexample.py).

A case is a pre-upgrade state `legacy` and a sequence of operations run from `upgrade legacy`.
Every state is computed by the kernel from the case (`run comptroller (upgrade L) ops`), never
taken from the executable's report; the adapter only uses the report, through the task oracle,
to find the step and the account at which the requirement fails.

* REQ-REWARDS-BOUNDED, REQ-ACCOUNT-BOUNDED, REQ-NO-BACKDATED-REWARDS: instantiated at `L` and
  the operations up to the failing step (and the account, and for the last one the history
  after which the account holds no position).
* REQ-SUPPLY-HOOK, REQ-BORROW-HOOK, REQ-SET-SPEEDS, REQ-CALLS-SUCCEED: instantiated at the state
  before the failing step and the call that step makes. The state after the call is left to the
  kernel. For a transfer, whose second supply hook runs on the state after the first, both hooks
  are tried.
* REQ-CLAIM: `Claimed` is existential; the proof takes the two intermediate states from the
  equations that `BorrowDistributed` and `SupplyDistributed` end with and decides the rest.
"""
from counterexample import lst, nat, struct

INSTANCES = """instance cexDecSupplyDistributed (s : St) (who : Account) (s' : St) :
    Decidable (SupplyDistributed s who s') := by
  unfold SupplyDistributed; infer_instance

instance cexDecBorrowDistributed (s : St) (who : Account) (s' : St) :
    Decidable (BorrowDistributed s who s') := by
  unfold BorrowDistributed; infer_instance

instance cexDecSpeedsSet (s : St) (a b : Nat) (s' : St) : Decidable (SpeedsSet s a b s') := by
  unfold SpeedsSet; infer_instance"""

HINTS = ["by unfold Consistent; decide", "by unfold NoPosition; decide"]


def acct_term(a):
    return "⟨" + ", ".join(nat(a[f]) for f in ("supply", "borrow", "supplierIndex", "borrowerIndex",
                                                "accrued", "wallet")) + "⟩"


def legacy_term(L):
    fields = {k: nat(L[k]) for k in ("blockNumber", "compSpeed", "supplyIndex", "supplyBlock", "borrowIndex",
                                     "borrowBlock", "supplyStart", "borrowStart", "reserve")}
    fields["accts"] = lst([acct_term(a) for a in L["accts"]], "Acct")
    return struct(fields, "Legacy")


def op_term(op):
    k = op["op"]
    args = {"mint": ("who", "amount"), "redeem": ("who", "amount"), "borrow": ("who", "amount"),
            "repay": ("who", "amount"), "transfer": ("src", "dst", "amount"), "claim": ("who",),
            "setSpeeds": ("supply", "borrow"), "advance": ("blocks",), "drip": ("amount",)}[k]
    return f"(Op.{k} {' '.join(nat(op[a]) for a in args)})"


def ops_term(ops):
    return lst([op_term(op) for op in ops], "Op")


def calls(op):
    """The implementation calls an operation makes, as Lean terms."""
    k = op["op"]
    if k in ("mint", "redeem"):
        return [f"(Call.supplyHook {nat(op['who'])})"]
    if k in ("borrow", "repay"):
        return [f"(Call.borrowHook {nat(op['who'])})"]
    if k == "transfer":
        return [f"(Call.supplyHook {nat(op['src'])})", f"(Call.supplyHook {nat(op['dst'])})"]
    if k == "claim":
        return [f"(Call.claim {nat(op['who'])})"]
    if k == "setSpeeds":
        return [f"(Call.setSpeeds {nat(op['supply'])} {nat(op['borrow'])})"]
    return []


def failing_step(o, case, start, steps, requirement):
    states = [start] + [st["state"] for st in steps]
    for i, op in enumerate(case["ops"]):
        p, q, ok = states[i], states[i + 1], steps[i]["ok"]
        ok_e, exp, rid = o.expected(p, op)
        if requirement == "REQ-CALLS-SUCCEED":
            if not ok and ok_e and o.consistent(p) and rid != "WRAPPER":
                return i
        elif rid == requirement and ok and (not ok_e or q != exp):
            return i
    return None


def instance(task, requirement, case, out):
    o = task.oracle
    start, steps = (out or {}).get("start"), (out or {}).get("steps")
    if start is None or steps is None or len(steps) != len(case["ops"]):
        return None
    L, ops = case["legacy"], case["ops"]
    LT = legacy_term(L)
    states = [start] + [st["state"] for st in steps]
    if requirement in ("REQ-REWARDS-BOUNDED", "REQ-ACCOUNT-BOUNDED", "REQ-NO-BACKDATED-REWARDS") and not o.wellformed(L):
        return None
    if requirement == "REQ-REWARDS-BOUNDED":
        cum, base, ow = o.emitted_steps(L, ops), o.credited(start), o.owed(L)
        j = next((j for j, s in enumerate(states) if o.credited(s) > base + ow + cum[j]), None)
        if j is None:
            return None
        return {"args": [LT, ops_term(ops[:j])], "note": f"the first {j} operations"}
    if requirement == "REQ-ACCOUNT-BOUNDED":
        cum = o.emitted_steps(L, ops)
        for w in range(max(len(s["accts"]) for s in states)):
            bound = o.credited_to(start, w) + o.owed_to(L, w)
            for j, s in enumerate(states):
                if o.credited_to(s, w) > bound + cum[j]:
                    return {"args": [LT, ops_term(ops[:j]), nat(w)], "note": f"account {w} after the first {j} operations"}
        return None
    if requirement == "REQ-NO-BACKDATED-REWARDS":
        cum = o.emitted_steps(L, ops)
        for w in range(max(len(s["accts"]) for s in states)):
            for i, s in enumerate(states):
                a = o.get(s, w)
                if a["supply"] or a["borrow"]:
                    continue
                for j in range(i + 1, len(states)):
                    if o.credited_to(states[j], w) > o.credited_to(s, w) + cum[j] - cum[i]:
                        return {"args": [LT, ops_term(ops[:i]), ops_term(ops[i:j]), nat(w), "?", "?"],
                                "hints": HINTS,
                                "note": f"account {w}, no position after the first {i} operations, the next {j - i}"}
        return None
    i = failing_step(o, case, start, steps, requirement)
    if i is None or not calls(ops[i]):
        return None
    S = f"(run comptroller (upgrade {LT}) {ops_term(ops[:i])})"
    cs = calls(ops[i])
    note = f"step {i} ({ops[i]['op']}), from the state the kernel computes for the first {i} operations"
    if requirement == "REQ-CALLS-SUCCEED":
        return {"preamble": INSTANCES, "args": [S, cs[0], "?"], "hints": HINTS, "note": note}
    if requirement == "REQ-CLAIM":
        if ops[i]["op"] != "claim":
            return None
        return {"preamble": INSTANCES, "note": note, "proof": f"""intro h
obtain ⟨m₁, m₂, h1, h2, h3⟩ := h {S} {nat(ops[i]['who'])} _ (Option.some_get (by decide)).symm
have e1 := h1.2.2
have e2 := h2.2.2
subst e1
subst e2
revert h1 h2 h3
first | decide | decide +kernel"""}
    who = {"REQ-SUPPLY-HOOK": "supplyHook", "REQ-BORROW-HOOK": "borrowHook"}
    if requirement in who:
        # ∀ s who s', comptroller s (.hook who) = some s' → Distributed s who s'
        targets = [(S, c) for c in cs if who[requirement] in c]
        if ops[i]["op"] == "transfer":
            targets = [(S, cs[0]), (f"((comptroller {S} {cs[0]}).getD {S})", cs[1])]
        alts = [f"(have hx := h {s} {c.split()[1].rstrip(')')} _ (Option.some_get (by decide)).symm\n"
                f"     revert hx\n     first | decide | decide +kernel)" for s, c in targets]
        return {"preamble": INSTANCES, "note": note,
                "proof": "intro h\nfirst\n" + "\n".join(f"  | {a}" for a in alts)}
    if requirement == "REQ-SET-SPEEDS" and ops[i]["op"] == "setSpeeds":
        return {"preamble": INSTANCES, "args": [S, nat(ops[i]["supply"]), nat(ops[i]["borrow"]), "_", "?"],
                "note": note}
    return None
