"""Counterexample adapter for rw-cetus-shlw (harness/counterexample.py).

Cases are `{"op": "shlw", "n": n}` and `{"op": "delta_a", "sqrt_price_0", "sqrt_price_1",
"liquidity", "round_up"}`. The instance is the case's numbers in binder order. The amount a
deposit is charged is left to the kernel (`_`, pinned by the `?` hypothesis
`getDeltaA ... = some amount`), so the refutation does not rely on the executable's output.
"""
from counterexample import nat

SHLW = {"REQ-SHLW-EXACT", "REQ-SHLW-COMPLETE"}
DELTA = {"REQ-DELTA-A-COVERS": True, "REQ-DELTA-A-TIGHT": True, "REQ-DELTA-A-FLOOR": False}


def instance(task, requirement, case, out):
    if requirement in SHLW and case.get("op") == "shlw":
        # ∀ n : BitVec 256, ...
        return {"args": [nat(case["n"])], "note": f"checkedShlw at n = {case['n']}"}
    if requirement in DELTA and case.get("op") == "delta_a" and case.get("round_up") is DELTA[requirement]:
        # ∀ sp0 sp1 liquidity : BitVec 128, ∀ amount : BitVec 64, getDeltaA ... = some amount → ...
        return {"args": [nat(case["sqrt_price_0"]), nat(case["sqrt_price_1"]), nat(case["liquidity"]), "_", "?"],
                "note": f"getDeltaA rounding {'up' if DELTA[requirement] else 'down'} at sqrt prices "
                        f"{case['sqrt_price_0']} and {case['sqrt_price_1']}, liquidity {case['liquidity']}"}
    return None
