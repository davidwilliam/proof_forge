"""Counterexample adapter for rw-balancer-upscale (harness/counterexample.py).

A case is a batch of swaps against a two-token pool with the constant-product math, which the
oracle checks and `BalancerSwap.Sanity` proves well behaved (`constantProduct_wellBehaved`)
and price-monotone (`constantProduct_priceMonotone`); those lemmas discharge the requirements'
hypotheses on the math. The per-swap requirements are instantiated at the pool before the first
failing swap, written out from the reported balances; REQ-BATCH-KEEPS-VALUE at the starting pool
and the whole batch. Amounts and pools after a swap are left to the kernel.
"""
from counterexample import lst, nat, struct

KIND = {"in": ".givenIn", "out": ".givenOut"}
PER_SWAP = {
    # requirement: hypotheses before the amount or the pool after the swap; negative: the
    # number of hypotheses of a success requirement, which has no such binder
    "REQ-GIVEN-IN-SUCCEEDS": -5, "REQ-GIVEN-OUT-SUCCEEDS": -6,
    "REQ-GIVEN-IN-PAYS-AT-MOST": 3, "REQ-GIVEN-IN-PAYS-AT-LEAST": 3,
    "REQ-GIVEN-OUT-CHARGES-AT-LEAST": 3, "REQ-GIVEN-OUT-CHARGES-AT-MOST": 3,
    "REQ-SWAP-KEEPS-VALUE": 1,
}
HINTS = ["constantProduct_wellBehaved", "constantProduct_priceMonotone"]


def pool_term(bal, rates, fee):
    return struct({"n": nat(len(bal)), "balance": f"(fun k => {lst([nat(b) for b in bal])}.getD k 0)",
                   "rate": f"(fun k => {lst([nat(r) for r in rates])}.getD k 0)", "fee": nat(fee)}, "Pool")


def swap_term(s):
    return struct({"kind": KIND[s["kind"]], "tokenIn": nat(s["in"]), "tokenOut": nat(s["out"]),
                   "amount": nat(s["amount"])}, "Swap")


def instance(task, requirement, case, out):
    o = task.oracle
    if case.get("math") != "product" or len(case["pool"]["balances"]) != 2 or "steps" not in (out or {}):
        return None
    pool, swaps, steps = case["pool"], case["swaps"], out["steps"]
    rates, fee = pool["rates"], pool["fee"]
    base = {"imports": ["BalancerSwap.Sanity"], "hints": HINTS}
    if requirement == "REQ-BATCH-KEEPS-VALUE":
        P = pool_term(pool["balances"], rates, fee)
        ss = lst([swap_term(s) for s in swaps], "Swap")
        # ∀ m p ss p', WellBehaved m p.n → run impl m p ss = some p' → value m p ≤ value m p'
        return {**base, "args": ["constantProduct", P, ss, "_", "?", "?"],
                "note": f"the batch of {len(swaps)} swaps from the starting pool"}
    if requirement not in PER_SWAP:
        return None
    bal = list(pool["balances"])
    for k, (s, st) in enumerate(zip(swaps, steps)):
        if requirement in [rid for rid, _ in o.swap_violations(bal, rates, fee, s, st)]:
            P, S = pool_term(bal, rates, fee), swap_term(s)
            n = PER_SWAP[requirement]
            # ∀ m p s, hypotheses → (step impl m p s).isSome, or
            # ∀ m p s y, hypotheses → impl m p s = some y → ...  (y left to the kernel)
            args = ["constantProduct", P, S] + (["?"] * -n if n < 0 else ["_"] + ["?"] * (n + 1))
            return {**base, "args": args, "note": f"swap {k} of the batch, from the reported balances {bal}"}
        if not st.get("ok"):
            break
        bal = st.get("balances") or bal
    return None
