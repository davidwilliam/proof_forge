"""Counterexample adapter for rw-hundred-vault (harness/counterexample.py).

A case is a sequence of operations from the empty vault, or from a given start state. The
adapter replays the task oracle to find the failing step.

* REQ-SHARE-VALUE quantifies over a history from the empty vault and a further sequence: the
  instance is the operations up to the first state of a stretch with shares outstanding and the
  operations up to the later state whose share is worth less (a start state that the oracle
  accepts as reachable is a donation to the empty vault and is written as one).
* REQ-DEPOSIT-SUCCEEDS, REQ-REDEEM-SUCCEEDS, REQ-WITHDRAW-SUCCEEDS hold for every state and are
  instantiated at the reported state before the refused call.
* The effects and rounding requirements take `Minted` or `Burned` as a hypothesis, which
  includes a frame condition over every actor (`∀ b, b ≠ who → ...`); proving it for the
  candidate's output is a proof about the candidate's code, not a kernel evaluation, so the
  adapter reports them as unsupported.
"""
from counterexample import lst, nat, struct

FRAMED = {"REQ-DEPOSIT-EFFECTS", "REQ-REDEEM-EFFECTS", "REQ-WITHDRAW-EFFECTS", "REQ-DEPOSIT-ROUNDS-DOWN",
          "REQ-REDEEM-ROUNDS-DOWN", "REQ-WITHDRAW-ROUNDS-UP"}


def op_term(op):
    k = op["op"]
    if k == "donate":
        return f"(Op.donate {nat(op['amount'])})"
    arg = op["shares"] if k == "redeem" else op["amount"]
    return f"(Op.call (Call.{k} {nat(op['who'])} {nat(arg)}))"


def vault_term(s):
    return struct({"assets": nat(s["assets"]), "supply": nat(s["supply"]),
                   "balance": f"(fun b => {lst([nat(x) for x in s['balances']], 'Nat')}.getD b 0)"}, "Vault")


def instance(task, requirement, case, out, origin=None):
    o = task.oracle
    steps = (out or {}).get("steps")
    ops = case["ops"]
    if steps is None or len(steps) != len(ops):
        return None
    states = [o._state(case.get("start"))] + steps
    if requirement == "REQ-SHARE-VALUE":
        if not o.reachable_start(case):
            return None
        pre = [{"op": "donate", "amount": case["start"]["assets"]}] if case.get("start") else []
        seg = []
        for k, s in enumerate(states + [None]):
            if s is not None and s["supply"] > 0:
                seg.append(k)
                continue
            for i in seg:
                for j in seg:
                    a, c = states[i], states[j]
                    if i < j and a["assets"] * c["supply"] > c["assets"] * a["supply"]:
                        H = lst([op_term(x) for x in pre + ops[:i]], "Op")
                        T = lst([op_term(x) for x in ops[i:j]], "Op")
                        return {"args": [H, T],
                                "note": f"after {i} operations a share is worth {a['assets']}/{a['supply']}, "
                                        f"after {j} it is worth {c['assets']}/{c['supply']}"}
            seg = []
        return None
    calls = {"REQ-DEPOSIT-SUCCEEDS": ("deposit", "amount"), "REQ-REDEEM-SUCCEEDS": ("redeem", "shares"),
             "REQ-WITHDRAW-SUCCEEDS": ("withdraw", "amount")}
    if requirement in calls:
        kind, key = calls[requirement]
        for i, op in enumerate(ops):
            if op["op"] == kind and requirement in [rid for rid, _ in o.step_violations(op, states[i], steps[i]["ok"], states[i + 1])]:
                return {"args": [vault_term(states[i]), nat(op["who"]), nat(op[key])],
                        "note": f"step {i}, {op}, from the reported state before it"}
        return None
    if requirement in FRAMED:
        return {"unsupported": "the requirement's hypothesis Minted or Burned includes a frame condition over every "
                               "actor, which needs a proof about the candidate's code rather than an evaluation"}
    return None
