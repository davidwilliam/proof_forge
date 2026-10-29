"""Independent Python model of spec/ClmmMath/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). `shlw_violations` and `delta_a_violations` are also used by
eval/realworld_cetus.py to check the real Move code's outputs against the same requirements.
"""

U64, U128, U256 = 2 ** 64, 2 ** 128, 2 ** 256
TWO_192 = 2 ** 192
MASK_ORIGINAL = (2 ** 64 - 1) << 192
# Cetus tick_math bounds on sqrt prices (Q64.64), for realistic generated deposits.
MIN_SQRT_PRICE, MAX_SQRT_PRICE = 4295048016, 79226673515401279992447579055

# The attack deposit (Dedaub): tick range [300000, 300200], liquidity about 2^113, round up.
ATTACK = {"op": "delta_a", "sqrt_price_0": 60257519765924248467716150,
          "sqrt_price_1": 60863087478126617965993239,
          "liquidity": 10365647984364446732462244378333008, "round_up": True}
FLAGSHIP = ATTACK

SHLW_BOUNDARY = [0, 1, TWO_192 - 1, TWO_192, TWO_192 + 1, 2 * TWO_192, MASK_ORIGINAL - 1,
                 MASK_ORIGINAL, MASK_ORIGINAL + 1, U256 - 1, ATTACK["liquidity"] * (ATTACK["sqrt_price_1"] - ATTACK["sqrt_price_0"])]


def exact_numerator(sp0, sp1, liquidity):
    return liquidity * abs(sp1 - sp0) * U64


def shlw_violations(n, value, overflow):
    """(requirement_id, message) for every shift requirement the output breaks."""
    v = []
    if not overflow and value != n * U64:
        v.append(("REQ-SHLW-EXACT", f"no overflow reported for n = {n}, but the result {value} is not n * 2^64"))
    if overflow and n * U64 < U256:
        v.append(("REQ-SHLW-COMPLETE", f"overflow reported for n = {n}, although n * 2^64 fits in 256 bits"))
    return v


def delta_a_violations(sp0, sp1, liquidity, round_up, amount):
    """(requirement_id, message) for every token-A requirement the output breaks; `amount` is
    None when the routine aborted (no requirement is broken by an abort)."""
    if amount is None:
        return []
    v = []
    if not 0 <= amount < U64:
        return [("REQ-DELTA-A-COVERS" if round_up else "REQ-DELTA-A-FLOOR", f"amount {amount} is not a u64")]
    ex, den = exact_numerator(sp0, sp1, liquidity), sp0 * sp1
    if round_up:
        if amount * den < ex:
            v.append(("REQ-DELTA-A-COVERS", f"charged {amount} {'unit' if amount == 1 else 'units'} of token A; the exact amount owed for the liquidity, "
                                            f"rounded up, is {-(-ex // den) if den else ex} units"))
        if amount > 0 and (amount - 1) * den >= ex:
            v.append(("REQ-DELTA-A-TIGHT", f"charged {amount} units, a unit or more above the exact amount"))
    elif amount * den > ex:
        v.append(("REQ-DELTA-A-FLOOR", f"paid out {amount} units, more than the exact amount"))
    return v


def _log_uniform(rng, lo, hi):
    """An integer in [lo, hi) with a uniformly drawn bit length."""
    bits = rng.randint(max(1, lo.bit_length()), hi.bit_length())
    x = rng.getrandbits(bits) | (1 << (bits - 1))
    return min(max(x, lo), hi - 1)


def gen_case(rng):
    k = rng.random()
    if k < 0.5:
        j = rng.random()
        if j < 0.25:
            n = rng.choice(SHLW_BOUNDARY)
        elif j < 0.5:
            n = rng.getrandbits(256)
        elif j < 0.75:
            n = _log_uniform(rng, 1, TWO_192)
        else:
            n = TWO_192 + rng.getrandbits(rng.randint(1, 191))
        return {"op": "shlw", "n": n}
    j = rng.random()
    if j < 0.05:
        return dict(ATTACK, round_up=rng.random() < 0.5)
    sp0 = _log_uniform(rng, MIN_SQRT_PRICE, MAX_SQRT_PRICE + 1)
    sp1 = _log_uniform(rng, MIN_SQRT_PRICE, MAX_SQRT_PRICE + 1) if j < 0.5 else \
        min(MAX_SQRT_PRICE, sp0 + _log_uniform(rng, 1, max(2, sp0 // 50)))
    if j < 0.1:
        sp1 = sp0
    liquidity = 0 if j < 0.15 else _log_uniform(rng, 1, U128)
    if rng.random() < 0.5:
        sp0, sp1 = sp1, sp0
    return {"op": "delta_a", "sqrt_price_0": sp0, "sqrt_price_1": sp1, "liquidity": liquidity,
            "round_up": rng.random() < 0.7}


def describe(out):
    if "amount" in out:
        return "abort" if out["amount"] is None else f"{out['amount']} units of token A"
    return f"{out.get('value')} (overflow {out.get('overflow')})"


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    if case["op"] == "shlw":
        if not isinstance(out.get("value"), int) or not isinstance(out.get("overflow"), bool):
            return [("WRAPPER", "malformed shift output")]
        return shlw_violations(case["n"], out["value"], out["overflow"])
    if "amount" not in out:
        return [("WRAPPER", "malformed amount output")]
    return delta_a_violations(case["sqrt_price_0"], case["sqrt_price_1"], case["liquidity"],
                              case["round_up"], out["amount"])
