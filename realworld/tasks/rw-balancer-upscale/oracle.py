"""Independent Python model of spec/BalancerSwap/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean requirements on the batches the binary
reports, with the constant-product math of Spec.lean (`constantProduct`, proved well behaved and
price-monotone for two tokens in Sanity.lean). It never assigns VERIFIED; it can only produce
witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). `violations(case, out)` is also used by the real-code evaluator.
"""

ONE = 10**18
OSETH_RATE = 1058132408689971699   # osETH scaling factor during the November 2025 attack
FEE = 10**14                        # the attacked pool's swap fee, 0.01%


def scale_down(a, r):
    return a * r // ONE


def scale_up(a, r):
    return (a * r + (ONE - 1)) // ONE


def tsub(a, b):
    """Natural-number subtraction, truncated at zero, as in Lean."""
    return a - b if a > b else 0


def cp_out_given_in(b, i, j, x):
    d = b[i] + x
    return b[j] * x // d if d else 0


def cp_in_given_out(b, i, j, x):
    return (b[i] * x + tsub(tsub(b[j], x), 1)) // (b[j] - x) if x < b[j] else b[i] * x


def cp_invariant(b):
    return b[0] * b[1]


def scaled(bal, rates):
    return [scale_down(bal[k], rates[k]) for k in range(len(bal))]


def value(bal, rates):
    return cp_invariant(scaled(bal, rates))


# The first four rounds of the November 2025 attack's shape on the osETH/WETH pool, from the
# pool's state after the transaction's 22 BPT-for-token swaps (67,000 wei of WETH and osETH):
# osETH out down to 18 wei, 17 wei of osETH out, WETH out paid with osETH
# (witnesses/attack_batch.lean).
ATTACK_POOL = {"balances": [67000, 67000], "rates": [ONE, OSETH_RATE], "fee": FEE}
ATTACK_SWAPS = [
    {"kind": "out", "in": 0, "out": 1, "amount": 66982}, {"kind": "out", "in": 0, "out": 1, "amount": 17},
    {"kind": "out", "in": 1, "out": 0, "amount": 2375365494},
    {"kind": "out", "in": 0, "out": 1, "amount": 66982}, {"kind": "out", "in": 0, "out": 1, "amount": 17},
    {"kind": "out", "in": 1, "out": 0, "amount": 1188037286},
    {"kind": "out", "in": 0, "out": 1, "amount": 66982}, {"kind": "out", "in": 0, "out": 1, "amount": 17},
    {"kind": "out", "in": 1, "out": 0, "amount": 594195912},
    {"kind": "out", "in": 0, "out": 1, "amount": 66978}, {"kind": "out", "in": 0, "out": 1, "amount": 17},
    {"kind": "out", "in": 1, "out": 0, "amount": 297187558},
]
FLAGSHIP = {"math": "product", "pool": ATTACK_POOL, "swaps": ATTACK_SWAPS}

RATES = [ONE, ONE, OSETH_RATE, 1100000000000000000, 1000000000000000001, 10**12 * ONE,
         10**12 * 1058132408689971699, 3 * ONE // 2, 1999999999999999999]
FEES = [0, 10**12, FEE, 10**16, 5 * 10**16, 10**17]


def _amount(rng, hi):
    k = rng.random()
    if k < 0.3:
        return rng.randint(0, 40)
    if k < 0.6:
        return rng.randint(0, max(1, hi))
    if k < 0.85:
        return rng.randint(0, 10**6)
    return rng.randint(0, 10**22)


def _pool(rng, small):
    hi = 10**5 if small else 10**24
    bal = [rng.choice([rng.randint(0, 50), rng.randint(0, hi), rng.randint(0, hi)]) for _ in range(2)]
    rates = [rng.choice(RATES) for _ in range(2)]
    if rng.random() < 0.5:
        rates[rng.randrange(2)] = rng.randint(ONE, 2 * ONE)
    fee = rng.choice(FEES)
    if rng.random() < 0.05:
        fee = rng.choice([ONE, ONE + 1])
    if rng.random() < 0.03:
        rates[rng.randrange(2)] = 0
    return {"balances": bal, "rates": rates, "fee": fee}


def _attack(rng):
    """Small balances, then rounds of: token j out down to a few wei, a small amount of j out,
    then token i out paid with j."""
    j = rng.randrange(2)
    i = 1 - j
    rates = [ONE, ONE]
    rates[j] = rng.choice([OSETH_RATE, 1100000000000000000, rng.randint(ONE + 1, 2 * ONE)])
    if rng.random() < 0.3:
        rates[i] = rng.choice([OSETH_RATE, rng.randint(ONE, 2 * ONE)])
    start = rng.choice([67000, 1000, 10**6, rng.randint(20, 10**7)])
    bal = [start, start]
    swaps = []
    for _ in range(rng.randint(1, 4)):
        left = rng.randint(2, 30)
        swaps.append({"kind": "out", "in": i, "out": j, "amount": max(0, bal[j] - left)})
        swaps.append({"kind": "out", "in": i, "out": j, "amount": rng.randint(1, left)})
        swaps.append({"kind": "out", "in": j, "out": i, "amount": rng.randint(1, max(1, start // 2))})
    return {"math": "product", "pool": {"balances": bal, "rates": rates, "fee": rng.choice([0, FEE, 10**12])},
            "swaps": swaps}


def _walk(rng):
    small = rng.random() < 0.4
    pool = _pool(rng, small)
    swaps = []
    for _ in range(rng.randint(1, 6)):
        i = rng.randrange(2)
        j = 1 - i
        if rng.random() < 0.08:
            j = i if rng.random() < 0.5 else 2
        hi = pool["balances"][j] if j < 2 else 100
        swaps.append({"kind": rng.choice(["in", "out"]), "in": i, "out": j, "amount": _amount(rng, hi)})
    return {"math": "product", "pool": pool, "swaps": swaps}


def gen_case(rng):
    return _attack(rng) if rng.random() < 0.3 else _walk(rng)


def describe(out):
    if "error" in out:
        return "bad input"
    return (f"{len(out.get('steps', []))} steps, ok {out.get('ok')}, value {out.get('value_before')} -> "
            f"{out.get('value_after')}, balances {out.get('balances_after')}")


def valid(bal, s):
    return s["in"] != s["out"] and s["in"] < len(bal) and s["out"] < len(bal)


def settle(bal, s, q):
    a_in, a_out = (s["amount"], q) if s["kind"] == "in" else (q, s["amount"])
    if a_out > bal[s["out"]]:
        return None
    nb = list(bal)
    nb[s["in"]] = bal[s["in"]] + a_in
    nb[s["out"]] = bal[s["out"]] - a_out
    return nb


def swap_violations(bal, rates, fee, s, step):
    """(requirement_id, message) for one swap from balances `bal`, as Spec.lean states them."""
    v = []
    q, ok = step.get("quote"), step.get("ok")
    i, j, a = s["in"], s["out"], s["amount"]
    if not valid(bal, s):
        if ok:
            v.append(("WRAPPER", "invalid swap went through"))
        return v
    b = scaled(bal, rates)
    if not ok:
        if s["kind"] == "in" and rates[j] > 0 and fee < ONE:
            v.append(("REQ-GIVEN-IN-SUCCEEDS", f"given-in swap of {a} refused (balances {bal}, rates {rates}, fee {fee})"))
        if s["kind"] == "out" and rates[i] > 0 and fee < ONE and scale_up(a, rates[j]) < b[j]:
            v.append(("REQ-GIVEN-OUT-SUCCEEDS", f"given-out swap of {a} refused (balances {bal}, rates {rates}, fee {fee})"))
    if q is not None:
        if s["kind"] == "in":
            net = a * tsub(ONE, fee) * rates[i] // (ONE * ONE)
            net1 = tsub(a * tsub(ONE, fee), ONE) * rates[i] // (ONE * ONE)
            if not q * rates[j] <= ONE * cp_out_given_in(b, i, j, net):
                v.append(("REQ-GIVEN-IN-PAYS-AT-MOST", f"{a} in paid {q} out; the net amount in prices at {cp_out_given_in(b, i, j, net)} scaled units"))
            if not ONE * cp_out_given_in(b, i, j, net1) < (q + 1) * rates[j]:
                v.append(("REQ-GIVEN-IN-PAYS-AT-LEAST", f"{a} in paid {q} out; one unit less in prices at {cp_out_given_in(b, i, j, net1)} scaled units"))
        else:
            price = cp_in_given_out(b, i, j, scale_up(a, rates[j]))
            if not ONE * ONE * price <= q * tsub(ONE, fee) * rates[i]:
                v.append(("REQ-GIVEN-OUT-CHARGES-AT-LEAST", f"{a} out charged {q} in; the exact amount out, rounded up to {scale_up(a, rates[j])} scaled units, prices at {price}"))
            if not tsub(q, 1) * tsub(ONE, fee) * rates[i] < ONE * (ONE * price + rates[i]):
                v.append(("REQ-GIVEN-OUT-CHARGES-AT-MOST", f"{a} out charged {q} in; the price is {price} scaled units"))
    if ok:
        nb = settle(bal, s, q) if q is not None else None
        if nb is None or nb != step.get("balances"):
            v.append(("WRAPPER", f"balances after the swap are {step.get('balances')}, expected {nb}"))
        elif value(nb, rates) < value(bal, rates):
            v.append(("REQ-SWAP-KEEPS-VALUE", f"swap of {a} lowered the pool's value from {value(bal, rates)} to {value(nb, rates)}"))
    return v


def violations(case, out):
    """Every requirement the reported batch breaks, as in Spec.lean."""
    if out is None or "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    pool, swaps, steps = case["pool"], case["swaps"], out.get("steps") or []
    bal, rates, fee = list(pool["balances"]), pool["rates"], pool["fee"]
    if len(bal) != 2 or case.get("math") != "product":
        return [("WRAPPER", "the oracle checks two-token constant-product batches only")]
    v = []
    fails = [k for k, st in enumerate(steps) if not st.get("ok")]
    if (len(steps) > len(swaps) or (fails and fails[0] != len(steps) - 1)
            or (not fails and len(steps) != len(swaps)) or bool(out.get("ok")) == bool(fails)):
        v.append(("WRAPPER", f"{len(steps)} steps reported for {len(swaps)} swaps"))
    for s, st in zip(swaps, steps):
        v += swap_violations(bal, rates, fee, s, st)
        if not st.get("ok"):
            break
        bal = st.get("balances") or bal
    if out.get("value_before") != value(pool["balances"], rates):
        v.append(("WRAPPER", "value_before differs from the model"))
    if out.get("ok"):
        if out.get("balances_after") != bal:
            v.append(("WRAPPER", "balances_after differs from the last step"))
        if value(bal, rates) < value(pool["balances"], rates):
            v.append(("REQ-BATCH-KEEPS-VALUE", f"batch of {len(swaps)} swaps lowered the pool's value from {value(pool['balances'], rates)} to {value(bal, rates)}"))
    elif out.get("balances_after") != pool["balances"]:
        v.append(("WRAPPER", "a failed batch did not revert"))
    seen, res = set(), []
    for rid, msg in v:
        if rid not in seen:
            seen.add(rid)
            res.append((rid, msg))
    return res


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    return violations(case, out)
