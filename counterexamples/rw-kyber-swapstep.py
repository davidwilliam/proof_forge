"""Counterexample adapter for rw-kyber-swapstep (harness/counterexample.py).

Cases are steps `{"op": "step", "L", "c", "t", "F", "spec", "exact_input"}` and iterations of the
loop of `Pool.swap` `{"op": "loop", "L", "p", "tick", "limit", "F", "spec", "exact_input"}`. The
instance is the case's numbers in binder order and the step the executable returned, as a `Step`
term: the hypothesis `step ... = some s` (or `loopStep ... = some (s, crossed)`) is then decided by
kernel evaluation of the candidate's definitions, so a wrong output makes the check fail, it cannot
make a false refutation pass. Requirements that are conjunctions of a token1-in and a token1-out
statement are instantiated through `.1` or `.2`.
"""
from counterexample import boolean, discharger, int_, nat, prop_defs

SINGLE = {"REQ-IN-WITHIN-TARGET": (True, 2), "REQ-OUT-WITHIN-TARGET": (False, 2),
          "REQ-IN-FEE-LIQUIDITY": (True, 3), "REQ-OUT-FEE-LIQUIDITY": (False, 3)}
# requirement -> number of hypotheses after the step, for the token1-in and token1-out parts
PAIRED = {"REQ-STEP-REACH": (3, 3), "REQ-STEP-PAID": (3, 2)}


def step_term(out):
    return ("({ usedAmount := " + int_(out["used"]) + ", returnedAmount := " + int_(out["returned"])
            + ", deltaL := " + nat(out["deltaL"]) + ", nextSqrtP := " + nat(out["next"]) + " } : Step)")


def proof(task, sel, args):
    disch = discharger([], ", ".join(prop_defs(task)))
    rendered = " ".join(disch if a == "?" else f"({a})" for a in args)
    return "\n".join([
        "intro h",
        f"have hx := h{sel} {rendered}",
        "first",
        "  | (revert hx; decide)",
        "  | (revert hx; decide +kernel)",
    ])


def instance(task, requirement, case, out, origin=None):
    if not isinstance(out, dict) or out.get("revert") or "next" not in out:
        return None
    ei = case.get("exact_input")
    if case.get("op") == "step":
        nums = [nat(case["L"]), nat(case["c"]), nat(case["t"]), nat(case["F"]), int_(case["spec"])]
        s = step_term(out)
        note = f"{'exact-input' if ei else 'exact-output'} step L={case['L']} c={case['c']} t={case['t']} F={case['F']} spec={case['spec']}"
        if requirement in SINGLE:
            want, hyps = SINGLE[requirement]
            if want != ei:
                return None
            return {"args": [], "proof": proof(task, "", nums + [s] + ["?"] * hyps), "note": note}
        if requirement in PAIRED:
            hin, hout = PAIRED[requirement]
            sel, hyps = (".1", hin) if ei else (".2", hout)
            return {"args": [], "proof": proof(task, sel, nums + [s] + ["?"] * hyps), "note": note}
        return None
    if case.get("op") == "loop" and requirement == "REQ-POOL-CROSSES":
        nums = [nat(case["L"]), nat(case["p"]), nat(case["tick"]), nat(case["limit"]), nat(case["F"]),
                int_(case["spec"])]
        sel = ".1" if ei else ".2"
        args = nums + [step_term(out), boolean(out["crossed"])] + ["?"] * 8
        note = f"loop iteration L={case['L']} p={case['p']} tick={case['tick']} limit={case['limit']} F={case['F']} spec={case['spec']}"
        return {"args": [], "proof": proof(task, sel, args), "note": note}
    return None
