"""Independent Python model of spec/KyberSwapStep/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions of the requirements. It never assigns
VERIFIED; it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). Cases are steps (`op = "step"`) and iterations of the loop of `Pool.swap`
(`op = "loop"`). `reach_amount` is the reach amount of the code at commit 4ab08c0
(`calcReachAmount`, both divisions rounded down); it only steers case generation towards the
amounts where a step stops just before its target.
"""
import math

U256 = 2 ** 256
Q = 2 ** 96
FU = 100000
TFU = 200000
MIN_SQRT_RATIO = 4295128739
MAX_SQRT_RATIO = 1461446703485210103287273052203988822378723970342

# The exploit pattern: an exact-input step (token1 in) with an amount one unit below the amount
# that reaches the target. The code at 4ab08c0 returns the next price
# 27180014754675749645719300096015422, above the target.
FLAGSHIP = {"op": "step", "L": 529700652, "c": 26908681593376338809905220921561871,
            "t": 27180014754403994732126507336932861, "F": 300, "spec": 1816821696332, "exact_input": True}

# Further steps on which the code at 4ab08c0 passes the target: exact input, then exact output
# (the smaller root of estimateIncrementalLiquidity computed with the square root rounded down).
KNOWN = [
    {"op": "step", "L": 89726482958, "c": 757010609088826194439260883268872,
     "t": 768451593221406515535192182487174, "F": 8, "spec": 12957525706365, "exact_input": True},
    {"op": "step", "L": 485266825643, "c": 1159620850770068133088129815410561757,
     "t": 1173663187681242302173445811106519090, "F": 40, "spec": 86025722166463537, "exact_input": True},
    {"op": "step", "L": 3391575, "c": 316297169264893702192209790286789,
     "t": 312702479284222327139907330712089, "F": 10, "spec": -153872678, "exact_input": False},
    {"op": "step", "L": 412000555572, "c": 19203146777897484351571248901051,
     "t": 19198676379874755604052383994049, "F": 10, "spec": -23245703492, "exact_input": False},
    {"op": "step", "L": 488099447615, "c": 12702106732281905876958584314416,
     "t": 12689701559484189505314970178876, "F": 8, "spec": -76421257163, "exact_input": False},
]

FEES = [1, 8, 10, 40, 300, 1000, 5000, 20000, 99999]


def in_window(p, q):
    lo, hi = min(p, q), max(p, q)
    return MIN_SQRT_RATIO <= lo and hi < MAX_SQRT_RATIO and 100 * hi * hi < 105 * lo * lo


def in_range(L, c, t, F):
    return 0 < L < 2 ** 129 and F < FU and in_window(c, t)


def exact_in(L, c, t, F, spec):
    return in_range(L, c, t, F) and c < t and 0 < spec < 2 ** 255


def exact_out(L, c, t, F, spec):
    return in_range(L, c, t, F) and t < c and -2 ** 255 <= spec < 0


def reach_amount(L, c, t, F, exact_input):
    """calcReachAmount at commit 4ab08c0 (token1 branches), or None when it reverts."""
    if exact_input:
        den = TFU * c - F * t
        if den <= 0:
            return None
        num = L * TFU * (t - c) // den
        r = num * c // Q
        return r if r < 2 ** 255 else None
    den = TFU * t - F * c
    if den <= 0 or den - F * t < 0:
        return None
    num = L * (den - F * t) // den
    r = num * (c - t) // Q
    return -r if r < 2 ** 255 else None


def step_violations(case, out):
    """(requirement_id, message) for every requirement that the step output breaks."""
    L, c, t, F, spec, ei = case["L"], case["c"], case["t"], case["F"], case["spec"], case["exact_input"]
    used, ret, dl, nxt = out["used"], out["returned"], out["deltaL"], out["next"]
    v = []
    where = f"step L={L} c={c} t={t} F={F} spec={spec}"
    if ei and exact_in(L, c, t, F, spec):
        if not (c <= nxt <= t):
            v.append(("REQ-IN-WITHIN-TARGET", f"{where} (token1 in): next price {nxt} is outside [current {c}, target {t}]"))
        if used != spec:
            ok = nxt == t and 0 <= used < spec and used * Q * (TFU * c - F * t) <= L * TFU * (t - c) * c
            if not ok:
                v.append(("REQ-STEP-REACH", f"{where} (token1 in): used {used} of {spec}, next {nxt}: not a step that ends on the target with at most the exact amount"))
        if (nxt != t or dl > 0) and (L + dl) * nxt > L * c + used * Q:
            v.append(("REQ-STEP-PAID", f"{where} (token1 in): (L + deltaL) * next = {(L + dl) * nxt} exceeds L * c + used * 2^96 = {L * c + used * Q}"))
        if nxt != t and not (F * used * Q < TFU * c * (dl + 1) and TFU * c * dl < F * used * Q + TFU * c):
            v.append(("REQ-IN-FEE-LIQUIDITY", f"{where} (token1 in): deltaL {dl} is not within one unit of fee * used * 2^96 / (2 * c) = {F * used * Q / (TFU * c):.3f}"))
    if (not ei) and exact_out(L, c, t, F, spec):
        if not (t <= nxt <= c):
            v.append(("REQ-OUT-WITHIN-TARGET", f"{where} (token1 out): next price {nxt} is outside [target {t}, current {c}]"))
        if used != spec:
            ok = (nxt == t and used <= 0 and spec < used
                  and -used * Q * (TFU * t - F * c) <= L * (TFU * t - F * c - F * t) * (c - t))
            if not ok:
                v.append(("REQ-STEP-REACH", f"{where} (token1 out): used {used} of {spec}, next {nxt}: not a step that ends on the target with at most the exact amount"))
        if (L + dl) * Q * c > nxt * (L * Q + ret * c):
            v.append(("REQ-STEP-PAID", f"{where} (token1 out): the token0 reserve after the step exceeds the reserve before plus the input {ret}"))
        if nxt != t:
            lhs = 2 * dl * ((FU - F) * L * c + FU * used * Q)
            rhs = F * c * dl * dl - F * L * used * Q
            if lhs > rhs:
                v.append(("REQ-OUT-FEE-LIQUIDITY", f"{where} (token1 out): deltaL {dl} is above the smaller root of the fee equation"))
    return v


def loop_violations(case, out):
    L, p, tick, limit, F, spec, ei = (case["L"], case["p"], case["tick"], case["limit"], case["F"], case["spec"],
                                      case["exact_input"])
    nxt, crossed = out["next"], out["crossed"]
    if crossed:
        return []
    where = f"loop L={L} p={p} tick={tick} limit={limit} F={F} spec={spec}"
    if ei and in_range(L, p, tick, F) and p < tick and p < limit < MAX_SQRT_RATIO and 0 < spec < 2 ** 255:
        if not nxt < tick:
            return [("REQ-POOL-CROSSES", f"{where}: the loop stops without crossing the tick at {tick} with the price at {nxt}")]
    if (not ei) and in_range(L, p, tick, F) and tick < p and MIN_SQRT_RATIO < limit < p and -2 ** 255 <= spec < 0:
        if not tick < nxt:
            return [("REQ-POOL-CROSSES", f"{where}: the loop stops without crossing the tick at {tick} with the price at {nxt}")]
    return []


def _price(rng):
    k = rng.random()
    if k < 0.1:
        return rng.choice([MIN_SQRT_RATIO, MIN_SQRT_RATIO + 1, Q, Q + 1, Q - 1, MAX_SQRT_RATIO // 2,
                           MAX_SQRT_RATIO * 40 // 41])
    bits = rng.randint(33, 160)
    return max(MIN_SQRT_RATIO, min(rng.getrandbits(bits) | 2 ** (bits - 1), MAX_SQRT_RATIO - 2))


def _other(rng, c, up):
    """A second price within the window of a step, above `c` when `up`."""
    for _ in range(20):
        k = rng.random()
        if k < 0.2:
            d = rng.randint(1, 1000)
        else:
            d = max(1, c * rng.choice([1, 10, 100, 1000, 10000, 24000, 24390]) // 1000000 + rng.randint(-5, 5))
        t = c + d if up else c - d
        if in_window(c, t):
            return t
    return c + 1 if up else c - 1


def _liquidity(rng):
    if rng.random() < 0.15:
        return rng.choice([1, 2, 100, 100000, 2 ** 128 - 1, 2 ** 129 - 2])
    return rng.getrandbits(rng.randint(1, 129)) or 1


def _fee(rng):
    return rng.choice(FEES) if rng.random() < 0.8 else rng.randrange(0, FU)


def _amount(rng, reach):
    k = rng.random()
    if reach is not None and k < 0.45 and abs(reach) > 0:
        return max(1, abs(reach) + rng.choice([-3, -2, -1, -1, 0, 0, 1]))
    if reach is not None and k < 0.55 and abs(reach) > 1:
        return rng.randint(1, abs(reach))
    if k < 0.7:
        return rng.randint(1, 5)
    return rng.getrandbits(rng.randint(1, 255)) or 1


def gen_case(rng):
    k = rng.random()
    if k < 0.04:
        return dict(rng.choice([FLAGSHIP] + KNOWN))
    ei = rng.random() < 0.5
    c = _price(rng)
    L = _liquidity(rng)
    F = _fee(rng)
    if k < 0.2:
        tick = _other(rng, c, ei)
        j = rng.random()
        if j < 0.4:
            limit = tick
        elif j < 0.7:
            limit = (c + tick) // 2 if (c + tick) // 2 != c else tick
        else:
            limit = _other(rng, c, ei)
        if ei and not c < limit < MAX_SQRT_RATIO:
            limit = tick
        if (not ei) and not MIN_SQRT_RATIO < limit < c:
            limit = tick
        target = limit if (ei == (tick > limit)) else tick
        a = _amount(rng, reach_amount(L, c, target, F, ei))
        return {"op": "loop", "L": L, "p": c, "tick": tick, "limit": limit, "F": F,
                "spec": a if ei else -min(a, 2 ** 255), "exact_input": ei}
    t = _other(rng, c, ei)
    a = _amount(rng, reach_amount(L, c, t, F, ei))
    spec = min(a, 2 ** 255 - 1) if ei else -min(a, 2 ** 255)
    if rng.random() < 0.02:
        spec = -spec
    return {"op": "step", "L": L, "c": c, "t": t, "F": F, "spec": spec, "exact_input": ei}


def describe(out):
    if out.get("revert"):
        return "revert"
    return f"next price {out.get('next')}, used {out.get('used')}, deltaL {out.get('deltaL')}"


def _is_word(x):
    return isinstance(x, int) and not isinstance(x, bool) and 0 <= x < U256


def _is_int(x):
    return isinstance(x, int) and not isinstance(x, bool)


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    if out.get("revert") is True:
        return []
    if not (_is_int(out.get("used")) and _is_int(out.get("returned")) and _is_word(out.get("deltaL"))
            and _is_word(out.get("next"))):
        return [("WRAPPER", "malformed step output")]
    if case["op"] == "step":
        return step_violations(case, out)
    if not isinstance(out.get("crossed"), bool):
        return [("WRAPPER", "malformed loop output")]
    return loop_violations(case, out)
