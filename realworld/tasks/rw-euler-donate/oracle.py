"""Independent Python model of spec/EulerLending/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean definitions. It never assigns VERIFIED;
it can only produce witnesses (REFUTED) or TESTED_ONLY evidence.

A case is one sequence of operations from `genesis` over accounts 0 to n - 1. The binary prints
the state after every operation. `check` walks the sequence: every transition it reports must
meet the requirements from the state before it, so every reported state is a state the
implementation reaches from `genesis`.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). `transition_violations` and `healthy` are also used by eval/realworld_euler.py
to check the real contracts' outputs against the same requirements.
"""

ONE = 10**18
E18 = 10**18

ATTACK = [["deposit", 0, 8904507], ["deposit", 1, 20000000], ["mint", 1, 200000000],
          ["repay", 1, 10000000], ["mint", 1, 200000000], ["donate", 1, 100000000],
          ["liquidate", 2, 1, "max"], ["withdraw", 2, 38904507]]
FLAGSHIP = {"n": 3, "ops": ATTACK}

HONEST = [["deposit", 0, 1000], ["deposit", 1, 100], ["borrow", 1, 95], ["repay", 1, 95],
          ["deposit", 2, 10], ["mint", 2, 190], ["burn", 2, 190], ["withdraw", 2, 10],
          ["withdraw", 1, 100]]


# Spec mirror.

def healthy(e, d):
    return d * 20 // 19 <= e


def health_score(e, d):
    return 0 if d == 0 else (e * 19 // 20) * ONE // d


def discount(e, d):
    return min(ONE // 5, ONE // 50 + max(0, ONE - health_score(e, d)))


def conversion_rate(e, d):
    return ONE * ONE // (ONE - discount(e, d))


def liq_yield(e, d, r):
    return r * conversion_rate(e, d) // ONE


def max_repay(e, d):
    c = conversion_rate(e, d)
    return d if d * c // ONE <= e else e * ONE // c


def liq_fee(r):
    return r // 50


def resolve(op, acct):
    """The op with a `"max"` liquidation amount replaced by maxRepay of the violator."""
    if op[0] == "liquidate" and op[3] == "max":
        e, d = acct[op[2]]
        return op[:3] + [max_repay(e, d)]
    return op


def allowed(s, op):
    acct, cash = s["acct"], s["cash"]
    k = op[0]
    if k == "deposit":
        e, d = acct[op[1]]
        return d == 0 or healthy(e + op[2], d)
    if k == "withdraw":
        (e, d), x = acct[op[1]], op[2]
        return x <= e and x <= cash and healthy(e - x, d)
    if k == "borrow":
        (e, d), x = acct[op[1]], op[2]
        return x <= cash and healthy(e, d + x)
    if k == "repay":
        return True
    if k == "mint":
        (e, d), x = acct[op[1]], op[2]
        return healthy(e + x, d + x)
    if k == "burn":
        (e, d), x = acct[op[1]], op[2]
        y = min(x, d)
        return y <= e and healthy(e - y, d - y)
    if k == "transfer":
        u, v, x = op[1], op[2], op[3]
        (e, d), (ev, dv) = acct[u], acct[v]
        return u != v and x <= e and healthy(e - x, d) and (dv == 0 or healthy(ev + x, dv))
    if k == "donate":
        (e, d), x = acct[op[1]], op[2]
        return x <= e and healthy(e - x, d)
    if k == "liquidate":
        l, v, r = op[1], op[2], op[3]
        (el, dl), (ev, dv) = acct[l], acct[v]
        return (l != v and not healthy(ev, dv) and r <= max_repay(ev, dv)
                and healthy(el + liq_yield(ev, dv, r), dl + r + liq_fee(r)))
    raise ValueError(k)


def expected_effect(s, op):
    """The next state EffectOn requires, or a message when its side conditions fail."""
    acct = [list(a) for a in s["acct"]]
    cash, res = s["cash"], s["reserves"]
    k = op[0]
    if k in ("deposit", "withdraw", "borrow", "repay", "mint", "burn", "donate"):
        u, x = op[1], op[2]
        e, d = acct[u]
        if k == "deposit":
            acct[u], cash = [e + x, d], cash + x
        elif k == "withdraw":
            if x > e or x > cash:
                return "withdrew more than the balance or the pool's cash"
            acct[u], cash = [e - x, d], cash - x
        elif k == "borrow":
            if x > cash:
                return "borrowed more than the pool's cash"
            acct[u], cash = [e, d + x], cash - x
        elif k == "repay":
            y = min(x, d)
            acct[u], cash = [e, d - y], cash + y
        elif k == "mint":
            acct[u] = [e + x, d + x]
        elif k == "burn":
            y = min(x, d)
            if y > e:
                return "burned more than the balance"
            acct[u] = [e - y, d - y]
        elif k == "donate":
            if x > e:
                return "donated more than the balance"
            acct[u], res = [e - x, d], res + x
    elif k == "transfer":
        u, v, x = op[1], op[2], op[3]
        if u == v or x > acct[u][0]:
            return "transfer to itself or of more than the balance"
        acct[u] = [acct[u][0] - x, acct[u][1]]
        acct[v] = [acct[v][0] + x, acct[v][1]]
    elif k == "liquidate":
        l, v, r = op[1], op[2], op[3]
        ev, dv = acct[v]
        if l == v or healthy(ev, dv) or r > max_repay(ev, dv):
            return "liquidation of a healthy account, by itself, or above the largest repay"
        y = liq_yield(ev, dv, r)
        acct[v] = [max(0, ev - y), max(0, dv - r)]
        acct[l] = [acct[l][0] + y, acct[l][1] + r + liq_fee(r)]
        res += liq_fee(r)
    return {"acct": acct, "cash": cash, "reserves": res}


def checked(op):
    k = op[0]
    return [op[1]] if k in ("withdraw", "borrow", "mint", "burn", "transfer", "donate", "liquidate") else []


def transition_violations(s, op, ok, s2):
    """(requirement_id, message) for one reported transition s -> s2 under `op`."""
    v = []
    if not ok:
        if allowed(s, op):
            v.append(("REQ-ALLOWED-SUCCEEDS", f"{op} reverted although it is allowed"))
        return v
    want = expected_effect(s, op)
    if isinstance(want, str):
        v.append(("REQ-EFFECTS", f"{op} succeeded: {want}"))
    elif [list(a) for a in s2["acct"]] != want["acct"] or s2["cash"] != want["cash"] or s2["reserves"] != want["reserves"]:
        v.append(("REQ-EFFECTS", f"{op} produced {s2}, expected {want}"))
    for w in checked(op):
        e, d = s2["acct"][w]
        if not healthy(e, d):
            v.append(("REQ-ACTOR-HEALTHY", f"after {op} account {w} owes {d} against {e}"))
    for w, ((e, d), (e2, d2)) in enumerate(zip(s["acct"], s2["acct"])):
        if healthy(e, d) and not healthy(e2, d2):
            v.append(("REQ-STAYS-HEALTHY", f"{op} made account {w} unhealthy: {d2} owed against {e2}"))
            break
    return v


def genesis(n):
    return {"acct": [[0, 0] for _ in range(n)], "cash": 0, "reserves": 0}


def check(case, out):
    """Return a list of (requirement_id, message) violations for one binary result."""
    if "error" in out or "steps" not in out:
        return [("WRAPPER", "binary could not parse input")]
    steps = out["steps"]
    if len(steps) != len(case["ops"]):
        return [("WRAPPER", f"{len(steps)} steps for {len(case['ops'])} operations")]
    n = case["n"]
    s = genesis(n)
    v, seen = [], set()
    for op, st in zip(case["ops"], steps):
        op = resolve(op, s["acct"])
        if op[0] == "liquidate" and st.get("r") != op[3]:
            return v + [("WRAPPER", f"liquidation amount {st.get('r')}, expected {op[3]}")]
        s2 = {"acct": st["acct"], "cash": st["cash"], "reserves": st["reserves"]}
        if not st["ok"] and s2 != s:
            return v + [("WRAPPER", "a reverted operation changed the reported state")]
        for rid, msg in transition_violations(s, op, st["ok"], s2):
            if rid not in seen:
                v.append((rid, msg))
                seen.add(rid)
        for w, (e, d) in enumerate(s2["acct"]):
            if not healthy(e, d) and "REQ-NO-BAD-DEBT" not in seen:
                v.append(("REQ-NO-BAD-DEBT", f"reachable state with account {w} owing {d} against {e}"))
                seen.add("REQ-NO-BAD-DEBT")
        s = s2
    if case["ops"] == HONEST:
        a = s["acct"]
        if not (all(st["ok"] for st in steps) and a[0] == [1000, 0] and a[1] == [0, 0]
                and a[2] == [0, 0] and s["cash"] == 1000 and s["reserves"] == 0):
            v.append(("REQ-HONEST-FLOW", "the honest session did not end with every position settled"))
    return v


def describe(out):
    steps = out.get("steps") or []
    if not steps:
        return "no steps"
    last = steps[-1]
    oks = "".join("1" if st["ok"] else "0" for st in steps)
    return f"ok={oks} accounts={last['acct']} cash={last['cash']} reserves={last['reserves']}"


# Generator.

def _sim(s, op):
    """Permissive simulation used only to choose amounts: the port's semantics."""
    op = resolve(op, s["acct"])
    if op[0] == "donate":
        e, d = s["acct"][op[1]]
        if op[2] > e:
            return s
        s = {"acct": [list(a) for a in s["acct"]], "cash": s["cash"], "reserves": s["reserves"] + op[2]}
        s["acct"][op[1]] = [e - op[2], d]
        return s
    if not allowed(s, op):
        return s
    want = expected_effect(s, op)
    return s if isinstance(want, str) else want


def _max_mint(e, d):
    """Largest x with healthy(e + x, d + x), or -1 when none."""
    if not healthy(e, d):
        return -1
    lo, hi = 0, 20 * e + 40
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if healthy(e + mid, d + mid):
            lo = mid
        else:
            hi = mid - 1
    return lo


def _amount(rng, scale):
    k = rng.random()
    if k < 0.3:
        return rng.randint(0, 300)
    if k < 0.7:
        return rng.randint(1, 1000) * scale
    return rng.randint(0, 10**6) * scale + rng.randint(0, 10**6)


def gen_case(rng):
    if rng.random() < 0.04:
        return {"n": 3, "ops": [list(op) for op in HONEST]}
    n = rng.choice([2, 3, 3, 4])
    scale = rng.choice([1, 1000, E18])
    s, ops = genesis(n), []
    for _ in range(rng.randint(1, 14)):
        u, v = rng.randrange(n), rng.randrange(n)
        e, d = s["acct"][u]
        k = rng.choices(["deposit", "withdraw", "borrow", "repay", "mint", "burn", "transfer",
                         "donate", "liquidate"], [5, 2, 2, 2, 4, 1, 2, 3, 3])[0]
        x = _amount(rng, scale)
        if k == "mint" and rng.random() < 0.7:
            m = _max_mint(e, d)
            x = max(0, m - rng.choice([0, 0, 1, rng.randint(0, max(1, m // 3))]) + (1 if rng.random() < 0.2 else 0))
        elif k in ("withdraw", "donate", "transfer", "burn") and e and rng.random() < 0.7:
            x = rng.choice([e, rng.randint(0, e), e - min(e, d * 20 // 19), e - min(e, d * 20 // 19) + 1, e + 1])
        elif k == "borrow" and rng.random() < 0.6:
            x = rng.choice([s["cash"], rng.randint(0, s["cash"] + 1), s["cash"] + 1])
        elif k == "repay" and d and rng.random() < 0.6:
            x = rng.choice([d, rng.randint(0, d), d + 1])
        op = {"transfer": ["transfer", u, v, x], "liquidate": ["liquidate", u, v, "max" if rng.random() < 0.8 else x]}.get(k, [k, u, x])
        ops.append(op)
        s = _sim(s, op)
    return {"n": n, "ops": ops}
