"""Independent Python model of spec/EqualSplit/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). `violations(amount, n, shares)` is also used by eval/realworld.py to check the
real library's outputs against the same requirements.
"""

FLAGSHIP = {"amount": -101, "n": 4}


def gen_case(rng):
    k = rng.random()
    if k < 0.4:
        amount = rng.randint(-300, 300)
    elif k < 0.7:
        amount = rng.randint(-1_000_000, 1_000_000)
    elif k < 0.9:
        amount = rng.randint(-10**12, 10**12)
    else:
        amount = rng.choice([0, 1, -1, -2, 99, 100, 101, -100, -101])
    n = rng.choice([0, 1, 2, 3, 3, 4, 5, 6, 7, 8, 9, 12, 25])
    return {"amount": amount, "n": n}


def describe(out):
    shares = out.get("shares")
    return "refused" if shares is None else " + ".join(str(x) for x in shares)


def violations(amount, n, shares):
    """(requirement_id, message) for every requirement the output breaks, as in Spec.lean."""
    if shares is None:
        return [("REQ-VALID-SUCCEEDS", f"splitting among {n} parties failed")] if n > 0 else []
    v = []
    if n == 0:
        v.append(("REQ-INVALID-FAILS", "splitting among zero parties returned shares"))
    if len(shares) != n:
        v.append(("REQ-ONE-SHARE-EACH", f"{len(shares)} shares for {n} parties"))
    if sum(shares) != amount:
        v.append(("REQ-CONSERVATION", f"shares add up to {sum(shares)}, amount is {amount}"))
    for x in shares:
        if not (-n < x * n - amount < n):
            v.append(("REQ-WITHIN-ONE-UNIT", f"share {x} is a unit or more away from {amount}/{n}"))
            break
    for x in shares:
        if (amount >= 0 and x < 0) or (amount <= 0 and x > 0):
            v.append(("REQ-SIGN", f"share {x} has the wrong sign for amount {amount}"))
            break
    return v


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    return violations(case["amount"], case["n"], out.get("shares"))
