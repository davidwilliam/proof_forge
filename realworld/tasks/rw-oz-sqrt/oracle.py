"""Independent Python model of spec/OzSqrt/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). `sqrt_violations`, `sqrt_up_violations` and `mint_violations` check one output
against the requirements.
"""
import math

U256 = 2 ** 256
MINIMUM_LIQUIDITY = 1000

# A first deposit whose product is 2^204 - 1: the floor of its root is 2^102 - 1, so the
# depositor is owed 2^102 - 1001 units of liquidity.
FLAGSHIP = {"op": "first_mint", "amount0": 2 ** 102 + 1, "amount1": 2 ** 102 - 1}

ROOTS = [1, 2, 3, 4, 10, 1000, 1001, 2 ** 32, 2 ** 64 - 1, 2 ** 64, 2 ** 100, 2 ** 102 - 1, 2 ** 127,
         2 ** 128 - 1]


def ceil_sqrt(a):
    """The square root of `a` rounded up."""
    return math.isqrt(a - 1) + 1 if a else 0


def sqrt_violations(a, r):
    """(requirement_id, message) for every requirement on the floor root that `r` breaks."""
    v = []
    if r * r > a:
        v.append(("REQ-SQRT-NOT-ABOVE", f"sqrt({a}) returned {r}, whose square exceeds the input; the floor of the root is {math.isqrt(a)}"))
    if a >= (r + 1) * (r + 1):
        v.append(("REQ-SQRT-NOT-BELOW", f"sqrt({a}) returned {r}, more than one unit below the root; the floor of the root is {math.isqrt(a)}"))
    return v


def sqrt_up_violations(a, r):
    """Requirements on the root rounded up."""
    v = []
    if r * r < a:
        v.append(("REQ-SQRT-UP-COVERS", f"sqrt({a}, Up) returned {r}, whose square is below the input; the root rounded up is {ceil_sqrt(a)}"))
    if r > 0 and (r - 1) * (r - 1) >= a:
        v.append(("REQ-SQRT-UP-TIGHT", f"sqrt({a}, Up) returned {r}, one unit or more above the root rounded up"))
    return v


def mint_violations(a0, a1, liquidity):
    """Requirements on the first deposit; `liquidity` is None when the deposit reverted."""
    p = a0 * a1
    if liquidity is None:
        if p < U256 and p >= 1001 * 1001:
            return [("REQ-MINT-LIVE", f"the first deposit of {a0} and {a1} reverted; it should mint {math.isqrt(p) - MINIMUM_LIQUIDITY} units")]
        return []
    v = []
    if (liquidity + MINIMUM_LIQUIDITY) ** 2 > p:
        v.append(("REQ-MINT-BACKED", f"the first deposit of {a0} and {a1} minted {liquidity} units plus the locked {MINIMUM_LIQUIDITY}, "
                                     f"more than the geometric mean {math.isqrt(p)} of the amounts"))
    if p >= (liquidity + MINIMUM_LIQUIDITY + 1) ** 2:
        v.append(("REQ-MINT-FULL", f"the first deposit of {a0} and {a1} minted {liquidity} units; "
                                   f"the depositor is owed {math.isqrt(p) - MINIMUM_LIQUIDITY}"))
    return v


def _number(rng):
    """A uint256 with a uniformly drawn bit length, or a value next to a square."""
    k = rng.random()
    if k < 0.45:
        bits = rng.randint(0, 256)
        return rng.getrandbits(bits) if bits else 0
    if k < 0.6:
        return rng.choice([0, 1, 2, 3, 15, 16, 2 ** 204 - 1, U256 - 1, 2 ** 255, 2 ** 254 - 1])
    s = rng.choice(ROOTS) if rng.random() < 0.3 else rng.getrandbits(rng.randint(1, 128))
    s = min(s, 2 ** 128 - 1)
    a = rng.choice([s * s - 1, s * s, s * s + 1, s * s + s, s * s + 2 * s])
    return min(max(a, 0), U256 - 1)


def gen_case(rng):
    k = rng.random()
    if k < 0.45:
        return {"op": "sqrt", "a": _number(rng)}
    if k < 0.65:
        return {"op": "sqrt_up", "a": _number(rng)}
    j = rng.random()
    if j < 0.1:
        return dict(FLAGSHIP)
    if j < 0.4:
        # amounts whose product is next to 2^(2k) - 1, where the root is 2^k - 1
        e = rng.randint(10, 127)
        return {"op": "first_mint", "amount0": 2 ** e + 1, "amount1": 2 ** e - 1}
    if j < 0.5:
        # products that overflow 256 bits (the Solidity multiplication reverts)
        return {"op": "first_mint", "amount0": rng.getrandbits(256) | 2 ** 200, "amount1": rng.getrandbits(100) | 2 ** 60}
    b0 = rng.randint(0, 128)
    b1 = rng.randint(0, 256 - b0)
    return {"op": "first_mint", "amount0": rng.getrandbits(b0) if b0 else 0, "amount1": rng.getrandbits(b1) if b1 else 0}


def describe(out):
    if "liquidity" in out:
        return "revert" if out["liquidity"] is None else f"{out['liquidity']} units of liquidity"
    return f"{out.get('result')}"


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    if case["op"] in ("sqrt", "sqrt_up"):
        r = out.get("result")
        if not isinstance(r, int) or not 0 <= r < U256:
            return [("WRAPPER", "malformed result")]
        return (sqrt_violations if case["op"] == "sqrt" else sqrt_up_violations)(case["a"], r)
    if "liquidity" not in out:
        return [("WRAPPER", "malformed first-deposit output")]
    l = out["liquidity"]
    if l is not None and (not isinstance(l, int) or not 0 <= l < U256):
        return [("WRAPPER", "malformed liquidity")]
    return mint_violations(case["amount0"], case["amount1"], l)
