"""Counterexample adapter for rw-oz-sqrt (harness/counterexample.py).

Cases are `{"op": "sqrt" | "sqrt_up", "a": n}` and `{"op": "first_mint", "amount0", "amount1"}`.
The instance is the case's numbers in binder order. Outputs (the liquidity minted) are left to
the kernel (`_`, pinned by the `?` hypothesis `firstMint ... = some liquidity`), so the refutation
does not rely on the executable's output.
"""
from counterexample import nat

ROOT = {"REQ-SQRT-NOT-ABOVE": "sqrt", "REQ-SQRT-NOT-BELOW": "sqrt", "REQ-SQRT-UP-COVERS": "sqrt_up"}


def instance(task, requirement, case, out):
    op = case.get("op")
    if requirement in ROOT and op == ROOT[requirement]:
        # ∀ a : U256, ...
        return {"args": [nat(case["a"])], "note": f"{op} at a = {case['a']}"}
    if requirement == "REQ-SQRT-UP-TIGHT" and op == "sqrt_up":
        # ∀ a : U256, 0 < (sqrtUp sqrt a).toNat → ...
        return {"args": [nat(case["a"]), "?"], "note": f"sqrt_up at a = {case['a']}"}
    if op != "first_mint":
        return None
    a0, a1 = nat(case["amount0"]), nat(case["amount1"])
    note = f"first deposit of {case['amount0']} and {case['amount1']}"
    if requirement in ("REQ-MINT-BACKED", "REQ-MINT-FULL"):
        # ∀ amount0 amount1 liquidity, firstMint sqrt amount0 amount1 = some liquidity → ...
        return {"args": [a0, a1, "_", "?"], "note": note}
    if requirement == "REQ-MINT-LIVE":
        # ∀ amount0 amount1, product < 2^256 → 1001 * 1001 ≤ product → isSome
        return {"args": [a0, a1, "?", "?"], "note": note}
    return None
