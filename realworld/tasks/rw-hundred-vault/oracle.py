"""Independent Python model of spec/ShareVault/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean requirements, step by step, on the states the
binary reports. It never assigns VERIFIED; it can only produce witnesses (REFUTED) or
TESTED_ONLY evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). `violations(case, steps)` is also used by eval/vault.py to check the outputs of
the real Solidity contract against the same requirements.
"""

INITIAL_SHARES_PER_UNIT = 50

# First round of the Hundred Finance attack (Optimism tx 0x6e9ebcde...f451), from the empty
# vault: deposit 4 WBTC, redeem all but 2 share units, donate 500.30063816 WBTC, withdraw
# 500.30063815 WBTC.
FLAGSHIP = {"ops": [
    {"op": "deposit", "who": 1, "amount": 400000000},
    {"op": "redeem", "who": 1, "shares": 19999999998},
    {"op": "donate", "amount": 50030063816},
    {"op": "withdraw", "who": 1, "amount": 50030063815},
]}


def _amount(rng):
    k = rng.random()
    if k < 0.35:
        return rng.randint(0, 50)
    if k < 0.7:
        return rng.randint(0, 10**6)
    if k < 0.9:
        return rng.randint(0, 10**11)
    return rng.choice([0, 1, 2, 3, 99, 100, 101, 10**8, 4 * 10**8, 5 * 10**10])


def _attack(rng):
    """Empty market, small deposit, redeem down to a few share units, large donation, then a
    withdrawal just under what the remaining units are worth."""
    ops = []
    if rng.random() < 0.3:
        ops.append({"op": "donate", "amount": rng.randint(0, 1000)})
    d = rng.choice([1, 3, 7, 100, 12345, 10**6, 4 * 10**8])
    keep = rng.choice([1, 2, 2, 3, 5, 10])
    ops.append({"op": "deposit", "who": 1, "amount": d})
    ops.append({"op": "redeem", "who": 1, "shares": max(0, d * INITIAL_SHARES_PER_UNIT - keep)})
    big = rng.choice([10**4, 10**6, 10**9, 50030063816, rng.randint(1, 10**12)])
    ops.append({"op": "donate", "amount": big})
    if rng.random() < 0.3:
        ops.append({"op": "deposit", "who": 0, "amount": rng.randint(0, 3 * big)})
    frac = rng.choice([(keep - 1, keep), (2 * keep - 1, 2 * keep), (1, 1), (1, 2), (3, 4)])
    x = big * frac[0] // frac[1] + rng.randint(-3, 3)
    ops.append({"op": "withdraw", "who": 1, "amount": max(0, x)})
    if rng.random() < 0.5:
        ops.append({"op": "redeem", "who": 1, "shares": rng.randint(0, keep)})
    return {"ops": ops}


def _walk(rng, start=None):
    actors = rng.randint(1, 4)
    ops = []
    for _ in range(rng.randint(1, 12)):
        who = rng.randrange(actors)
        k = rng.random()
        if k < 0.35:
            ops.append({"op": "deposit", "who": who, "amount": _amount(rng)})
        elif k < 0.6:
            ops.append({"op": "redeem", "who": who, "shares": _amount(rng) * rng.choice([1, 50, 10**3])})
        elif k < 0.85:
            ops.append({"op": "withdraw", "who": who, "amount": _amount(rng)})
        else:
            ops.append({"op": "donate", "amount": _amount(rng)})
    case = {"ops": ops}
    if start:
        case["start"] = start
    return case


def _start(rng):
    n = rng.randint(1, 3)
    k = rng.random()
    if k < 0.2:
        return {"assets": rng.randint(0, 1000), "supply": 0, "balances": [0] * n}
    bal = [rng.choice([0, 1, 2, rng.randint(0, 10**4), rng.randint(0, 10**12)]) for _ in range(n)]
    supply = sum(bal) + (rng.randint(0, 5) if rng.random() < 0.2 else 0)
    assets = rng.choice([0, 1, 2, rng.randint(0, 10**4), rng.randint(0, 10**12), supply // 50 + 1])
    return {"assets": assets, "supply": supply, "balances": bal}


def gen_case(rng):
    k = rng.random()
    if k < 0.3:
        return _attack(rng)
    if k < 0.75:
        return _walk(rng)
    return _walk(rng, _start(rng))


def describe(out):
    steps = out.get("steps") or []
    if not steps:
        return "no steps"
    last = steps[-1]
    return f"assets {last['assets']}, supply {last['supply']}, balances {last['balances']}"


def _state(start):
    if not start:
        return {"assets": 0, "supply": 0, "balances": []}
    return {"assets": start["assets"], "supply": start["supply"], "balances": list(start["balances"])}


def _bal(s, a):
    return s["balances"][a] if a < len(s["balances"]) else 0


def _others_same(p, q, who):
    n = max(len(p["balances"]), len(q["balances"]))
    return all(_bal(p, b) == _bal(q, b) for b in range(n) if b != who)


def step_violations(op, p, ok, q):
    """(requirement_id, message) for one operation from state p to state q."""
    v = []
    A, S = p["assets"], p["supply"]
    if op["op"] == "donate":
        if not (ok and q["assets"] == A + op["amount"] and q["supply"] == S and _others_same(p, q, -1)):
            v.append(("WRAPPER", "donation not applied as specified"))
        return v
    who = op["who"]
    b = _bal(p, who)
    if not ok:
        if (q["assets"], q["supply"]) != (A, S) or not _others_same(p, q, -1):
            v.append(("WRAPPER", "refused call changed the state"))
        if op["op"] == "deposit" and (S == 0 or A > 0):
            v.append(("REQ-DEPOSIT-SUCCEEDS", f"deposit of {op['amount']} refused (assets {A}, supply {S})"))
        if op["op"] == "redeem" and op["shares"] <= b and op["shares"] <= S:
            v.append(("REQ-REDEEM-SUCCEEDS", f"redeem of {op['shares']} of {b} held shares refused"))
        if op["op"] == "withdraw":
            x = op["amount"]
            if S > 0 and A > 0 and b <= S and x * S <= b * A:
                v.append(("REQ-WITHDRAW-SUCCEEDS", f"withdraw of {x} refused; caller's {b} shares are worth {b * A / S:.6g}"))
        return v
    if op["op"] == "deposit":
        x = op["amount"]
        t = q["supply"] - S
        if not (q["assets"] == A + x and t >= 0 and _bal(q, who) == b + t and _others_same(p, q, who)):
            v.append(("REQ-DEPOSIT-EFFECTS", f"deposit of {x}: assets {A} -> {q['assets']}, supply {S} -> {q['supply']}"))
            return v
        if S == 0 and t != INITIAL_SHARES_PER_UNIT * x:
            v.append(("REQ-DEPOSIT-ROUNDS-DOWN", f"first deposit of {x} minted {t} shares, expected {INITIAL_SHARES_PER_UNIT * x}"))
        if S > 0 and not (t * A <= x * S < (t + 1) * A):
            v.append(("REQ-DEPOSIT-ROUNDS-DOWN", f"deposit of {x} minted {t} shares; exact value {x * S / A if A else float('inf'):.12g}"))
        return v
    if op["op"] == "redeem":
        t = op["shares"]
        y = A - q["assets"]
        if not (t <= b and t <= S and 0 <= y <= A and q["supply"] == S - t and _bal(q, who) == b - t
                and _others_same(p, q, who)):
            v.append(("REQ-REDEEM-EFFECTS", f"redeem of {t} shares (held {b}, supply {S}): supply {S} -> {q['supply']}, assets {A} -> {q['assets']}"))
            return v
        if S == 0 and y != 0:
            v.append(("REQ-REDEEM-ROUNDS-DOWN", f"paid {y} with no shares outstanding"))
        if S > 0 and not (y * S <= t * A < (y + 1) * S):
            v.append(("REQ-REDEEM-ROUNDS-DOWN", f"redeem of {t} shares paid {y}; exact value {t * A / S:.12g}"))
        return v
    x = op["amount"]
    t = S - q["supply"]
    if not (x <= A and q["assets"] == A - x and 0 <= t <= b and _bal(q, who) == b - t and _others_same(p, q, who)):
        v.append(("REQ-WITHDRAW-EFFECTS", f"withdraw of {x}: assets {A} -> {q['assets']}, supply {S} -> {q['supply']}, held {b}"))
        return v
    if not (S > 0 and x * S <= t * A and t * A < x * S + A):
        exact = f"{x * S / A:.12g}" if A else "undefined"
        v.append(("REQ-WITHDRAW-ROUNDS-UP", f"withdraw of {x} burned {t} shares; exact value {exact}"))
    return v


def reachable_start(case):
    """States reachable from the empty vault: the empty vault, or a donation to it."""
    st = case.get("start")
    return not st or (st["supply"] == 0 and not any(st["balances"]))


def violations(case, steps):
    """Every requirement the reported steps break, as in Spec.lean."""
    ops = case["ops"]
    if steps is None or len(steps) != len(ops):
        return [("WRAPPER", f"{0 if steps is None else len(steps)} steps for {len(ops)} operations")]
    v = []
    states = [_state(case.get("start"))] + steps
    for i, op in enumerate(ops):
        v += step_violations(op, states[i], steps[i]["ok"], states[i + 1])
    # REQ-SHARE-VALUE: within every stretch where shares stay outstanding, the value of a share
    # never falls (checked for every pair of states in the stretch).
    if reachable_start(case):
        seg = []
        for s in states + [None]:
            if s is not None and s["supply"] > 0:
                seg.append(s)
                continue
            for i in range(len(seg)):
                for j in range(i + 1, len(seg)):
                    a, c = seg[i], seg[j]
                    if a["assets"] * c["supply"] > c["assets"] * a["supply"]:
                        v.append(("REQ-SHARE-VALUE",
                                  f"share worth {a['assets']}/{a['supply']} fell to {c['assets']}/{c['supply']}"))
                        break
                else:
                    continue
                break
            seg = []
    seen, out = set(), []
    for rid, msg in v:
        if rid not in seen:
            seen.add(rid)
            out.append((rid, msg))
    return out


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out:
        return [("WRAPPER", "binary could not parse input")]
    return violations(case, out.get("steps"))
