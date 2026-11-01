"""Independent Python model of spec/VyperSqrt/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). `violations` checks one output against the requirements.
"""
import math

DIVISOR = 10 ** 10
MAX_DECIMAL = 2 ** 167 - 1
MIN_DECIMAL = -2 ** 167

# GHSA-2p94-8669-xg86 (CVE-2025-26622): sqrt(0.9999999998) returned 0.9999999999 before Vyper
# 0.4.1; the root rounded down is 0.9999999998.
FLAGSHIP = {"op": "sqrt", "x": 9999999998}
ADVISORY = [9999999998, 9999999997, 11000000000]

# The square roots of 1 modulo 10^10. For `t` congruent to one of them, `t^2 - 1` is a multiple
# of 10^10, so `x = (t^2 - 1) / 10^10` is a decimal with `x * 10^10 + 1` a square: the iterates of
# the loop alternate between the root and the root plus one.
ONE_ROOTS = [1, 9999999999, 6425781249, 3574218751]


def violations(x, r):
    """(requirement_id, message) for every requirement the output `r` (None: revert) breaks."""
    if r is None:
        if 0 <= x:
            return [("REQ-SQRT-TOTAL", f"sqrt({x} / 10^10) reverted on a non-negative decimal")]
        return []
    if x < 0:
        return [("REQ-SQRT-NEG-REVERTS", f"sqrt({x} / 10^10) returned {r} instead of reverting")]
    n = x * DIVISOR
    v = []
    if r * r > n:
        v.append(("REQ-SQRT-NOT-ABOVE", f"sqrt({x} / 10^10) returned {r} / 10^10, above the root; rounded down it is {math.isqrt(n)} / 10^10"))
    if n >= (r + 1) * (r + 1):
        v.append(("REQ-SQRT-NOT-BELOW", f"sqrt({x} / 10^10) returned {r} / 10^10, more than 10^-10 below the root; rounded down it is {math.isqrt(n)} / 10^10"))
    return v


def _oscillating(rng):
    """A decimal `x` with `x * 10^10 + 1` a perfect square."""
    while True:
        u = rng.getrandbits(rng.randint(0, 90))
        t = u * DIVISOR + rng.choice(ONE_ROOTS)
        x = (t * t - 1) // DIVISOR
        if 0 < x <= MAX_DECIMAL:
            return x


def gen_case(rng):
    k = rng.random()
    if k < 0.3:
        x = _oscillating(rng)
    elif k < 0.4:
        x = rng.choice(ADVISORY + [0, 1, 2, DIVISOR - 1, DIVISOR, DIVISOR + 1, MAX_DECIMAL, MAX_DECIMAL - 1])
    elif k < 0.5:
        x = -rng.getrandbits(rng.randint(1, 167)) or -1
    elif k < 0.65:
        s = rng.getrandbits(rng.randint(1, 100))
        x = min(max((s * s) // DIVISOR + rng.randint(-2, 2), 0), MAX_DECIMAL)
    else:
        bits = rng.randint(1, 167)
        x = rng.getrandbits(bits)
    return {"op": "sqrt", "x": max(MIN_DECIMAL, min(x, MAX_DECIMAL))}


def describe(out):
    r = out.get("result")
    return "revert" if r is None else f"{r} / 10^10"


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    if "result" not in out:
        return [("WRAPPER", "malformed output")]
    r = out["result"]
    if r is not None and not isinstance(r, int):
        return [("WRAPPER", "malformed result")]
    return violations(case["x"], r)
