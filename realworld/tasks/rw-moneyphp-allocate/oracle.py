"""Independent Python model of spec/Allocation/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). `violations(amount, ratios, shares)` is also used by eval/realworld.py to check
the real libraries' outputs against the same requirements.
"""

FLAGSHIP = {"amount": 5, "ratios": [0, 7, 3]}


def gen_amount(rng):
    k = rng.random()
    if k < 0.4:
        return rng.randint(-300, 300)
    if k < 0.7:
        return rng.randint(-1_000_000, 1_000_000)
    if k < 0.9:
        return rng.randint(-10**12, 10**12)
    return rng.choice([0, 1, -1, 99, 100, 101, -100])


def gen_ratios(rng):
    n = rng.choice([0, 1, 2, 2, 3, 3, 3, 4, 5, 6, 7, 8, 12])
    k = rng.random()
    if k < 0.2:
        rs = [1] * n
    elif k < 0.45:
        rs = [rng.randint(0, 10) for _ in range(n)]
    elif k < 0.7:
        rs = [rng.randint(1, 1000) for _ in range(n)]
    elif k < 0.85:
        rs = [rng.choice([0, 0, 1, 2, 3, 25, 75, 100]) for _ in range(n)]
    else:
        rs = [rng.randint(0, 10**6) for _ in range(n)]
    if rs and rng.random() < 0.04:
        rs = [0] * n
    return rs


def gen_case(rng):
    return {"amount": gen_amount(rng), "ratios": gen_ratios(rng)}


def describe(out):
    shares = out.get("shares")
    return "refused" if shares is None else " + ".join(str(x) for x in shares)


def valid(amount, ratios):
    return len(ratios) > 0 and sum(ratios) > 0


def excess(amount, total, x, r):
    return x * total - amount * r


def violations(amount, ratios, shares):
    """(requirement_id, message) for every requirement the output breaks, as in Spec.lean."""
    if shares is None:
        return [("REQ-VALID-SUCCEEDS", "valid input was refused")] if valid(amount, ratios) else []
    v = []
    if not valid(amount, ratios):
        v.append(("REQ-INVALID-FAILS", "invalid input was allocated"))
    if len(shares) != len(ratios):
        v.append(("REQ-ONE-SHARE-EACH", f"{len(shares)} shares for {len(ratios)} ratios"))
    if sum(shares) != amount:
        v.append(("REQ-CONSERVATION", f"shares add up to {sum(shares)}, amount is {amount}"))
    S = sum(ratios)
    m = min(len(shares), len(ratios))
    ex = [excess(amount, S, shares[i], ratios[i]) for i in range(m)]
    for i in range(m):
        if not (-S < ex[i] < S):
            v.append(("REQ-WITHIN-ONE-UNIT", f"share {i} is {shares[i]}, exact share is {amount * ratios[i]}/{S}"))
            break
    for i in range(m):
        if ratios[i] == 0 and shares[i] != 0:
            v.append(("REQ-ZERO-RATIO", f"share {i} has ratio 0 and receives {shares[i]}"))
            break
    for x in shares:
        if (amount >= 0 and x < 0) or (amount <= 0 and x > 0):
            v.append(("REQ-SIGN", f"share {x} has the wrong sign for amount {amount}"))
            break
    done = False
    for i in range(m):
        for j in range(m):
            if ex[i] > 0 and ex[j] < 0 and ex[i] - ex[j] > S:
                v.append(("REQ-LARGEST-REMAINDER",
                          f"share {i} was rounded up and share {j} rounded down, but share {j} has the larger remainder"))
                done = True
                break
        if done:
            break
    return v


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    return violations(case["amount"], case["ratios"], out.get("shares"))
