"""Independent Python model of spec/CompRewards/Spec.lean, used to test binaries.

Trusted test code: it mirrors the protected Lean requirements on the states the binary
reports. It never assigns VERIFIED; it can only produce witnesses (REFUTED) or TESTED_ONLY
evidence.

Interface used by harness/binary_check.py: FLAGSHIP, gen_case(rng), check(case, out),
describe(out). `violations(case, start, steps)` is also used by eval/realworld_compound.py to
check the states of the real Solidity Comptroller against the same requirements.
"""
import copy

D = 10 ** 36            # doubleScale
INIT = 10 ** 36         # compInitialIndex
NOACCT = {"supply": 0, "borrow": 0, "supplierIndex": 0, "borrowerIndex": 0, "accrued": 0, "wallet": 0}
FIELDS = ("supply", "borrow", "supplierIndex", "borrowerIndex", "accrued", "wallet")


def acct(**kw):
    a = dict(NOACCT)
    a.update(kw)
    return a


# The cSUSHI claim of 2021-09-29 (transaction 0xc9244e53...0001, block 13322937): a borrower with
# 18977306140567618322762 borrow units and no recorded index in a market that never had rewards.
FLAGSHIP = {
    "legacy": {"blockNumber": 13322798, "compSpeed": 0, "supplyIndex": 0, "supplyBlock": 13320900,
               "borrowIndex": 0, "borrowBlock": 13322577, "supplyStart": 0, "borrowStart": 0,
               "reserve": 300514463598935139440340,
               "accts": [acct(borrow=18977306140567618322762)]},
    "ops": [{"op": "advance", "blocks": 139}, {"op": "claim", "who": 0}],
}


def sub(a, b):
    return a - b if a >= b else 0


# Spec.lean, transcribed.

def upgrade(L):
    def init(idx, blk):
        return {"index": INIT, "block": L["blockNumber"], "speed": L["compSpeed"]} if idx == 0 else \
            {"index": idx, "block": blk, "speed": L["compSpeed"]}
    return {"blockNumber": L["blockNumber"], "supplyState": init(L["supplyIndex"], L["supplyBlock"]),
            "borrowState": init(L["borrowIndex"], L["borrowBlock"]), "reserve": L["reserve"],
            "accts": copy.deepcopy(L["accts"])}


def get(s, w):
    return s["accts"][w] if w < len(s["accts"]) else NOACCT


def total(s, f):
    return sum(a[f] for a in s["accts"])


def accrue_side(sd, now, tot):
    d = sub(now, sd["block"])
    if d > 0 and sd["speed"] > 0 and tot > 0:
        return {"index": sd["index"] + d * sd["speed"] * D // tot, "block": now, "speed": sd["speed"]}
    return {"index": sd["index"], "block": now, "speed": sd["speed"]}


def accrual_start(u, idx):
    if u == 0:
        return INIT if INIT <= idx else 0
    return u


def credit(units, start, idx):
    return units * sub(idx, start) // D


def distributed(s, who, side):
    """SupplyDistributed / BorrowDistributed: the next state, or None when the call must revert."""
    key, tot_f, uf, bal = (("supplyState", "supply", "supplierIndex", "supply") if side == "supply"
                           else ("borrowState", "borrow", "borrowerIndex", "borrow"))
    if s[key]["block"] > s["blockNumber"]:
        return None
    sd = accrue_side(s[key], s["blockNumber"], total(s, tot_f))
    a = get(s, who)
    st = accrual_start(a[uf], sd["index"])
    if st > sd["index"]:
        return None
    t = copy.deepcopy(s)
    t[key] = sd
    if who < len(t["accts"]):
        b = t["accts"][who]
        b["accrued"] = b["accrued"] + credit(b[bal], st, sd["index"])
        b[uf] = sd["index"]
    return t


def grant(s, who):
    x = get(s, who)["accrued"]
    if 0 < x <= s["reserve"]:
        t = copy.deepcopy(s)
        t["reserve"] -= x
        b = t["accts"][who]
        b["accrued"], b["wallet"] = 0, b["wallet"] + x
        return t
    return s


def claimed(s, who):
    m1 = distributed(s, who, "borrow")
    if m1 is None:
        return None
    m2 = distributed(m1, who, "supply")
    return None if m2 is None else grant(m2, who)


def speeds_set(s, a, b):
    if (s["supplyState"]["speed"] != a and s["supplyState"]["block"] > s["blockNumber"]) or \
            (s["borrowState"]["speed"] != b and s["borrowState"]["block"] > s["blockNumber"]):
        return None
    t = copy.deepcopy(s)
    if s["supplyState"]["speed"] != a:
        t["supplyState"] = dict(accrue_side(s["supplyState"], s["blockNumber"], total(s, "supply")), speed=a)
    if s["borrowState"]["speed"] != b:
        t["borrowState"] = dict(accrue_side(s["borrowState"], s["blockNumber"], total(s, "borrow")), speed=b)
    return t


def consistent(s):
    return (s["supplyState"]["block"] <= s["blockNumber"] and s["borrowState"]["block"] <= s["blockNumber"] and
            all(a["supplierIndex"] <= s["supplyState"]["index"] and a["borrowerIndex"] <= s["borrowState"]["index"]
                for a in s["accts"]))


def with_acct(s, w, f, d):
    t = copy.deepcopy(s)
    if w < len(t["accts"]):
        t["accts"][w][f] += d
    return t


def expected(s, op):
    """(applied, next state) of `exec` with an implementation that meets the effects
    requirements, and the requirement that names the call the operation makes."""
    k, n = op["op"], len(s["accts"])
    if k in ("mint", "redeem", "borrow", "repay"):
        side = "supply" if k in ("mint", "redeem") else "borrow"
        rid = "REQ-SUPPLY-HOOK" if side == "supply" else "REQ-BORROW-HOOK"
        if op["who"] >= n:
            return False, s, rid
        h = distributed(s, op["who"], side)
        if h is None:
            return False, s, rid
        x = op["amount"]
        if k in ("redeem", "repay"):
            if x > get(h, op["who"])[side]:
                return False, s, rid
            x = -x
        return True, with_acct(h, op["who"], side, x), rid
    if k == "transfer":
        src, dst, x = op["src"], op["dst"], op["amount"]
        if not (src < n and dst < n and src != dst):
            return False, s, "REQ-SUPPLY-HOOK"
        h1 = distributed(s, src, "supply")
        h2 = None if h1 is None else distributed(h1, dst, "supply")
        if h2 is None or x > get(h2, src)["supply"]:
            return False, s, "REQ-SUPPLY-HOOK"
        return True, with_acct(with_acct(h2, src, "supply", -x), dst, "supply", x), "REQ-SUPPLY-HOOK"
    if k == "claim":
        t = claimed(s, op["who"])
        return (t is not None), (s if t is None else t), "REQ-CLAIM"
    if k == "setSpeeds":
        t = speeds_set(s, op["supply"], op["borrow"])
        return (t is not None), (s if t is None else t), "REQ-SET-SPEEDS"
    if k == "advance":
        return True, dict(copy.deepcopy(s), blockNumber=s["blockNumber"] + op["blocks"]), "WRAPPER"
    return True, dict(copy.deepcopy(s), reserve=s["reserve"] + op["amount"]), "WRAPPER"


def wellformed(L):
    return (L["supplyStart"] in (0, INIT) and L["supplyStart"] <= L["supplyIndex"] and
            L["borrowStart"] in (0, INIT) and L["borrowStart"] <= L["borrowIndex"] and
            L["supplyBlock"] <= L["blockNumber"] and L["borrowBlock"] <= L["blockNumber"] and
            all(a["supplierIndex"] <= L["supplyIndex"] and a["borrowerIndex"] <= L["borrowIndex"]
                for a in L["accts"]))


def legacy_start(start, u):
    return start if u == 0 else u


def pending_scaled(L, a):
    return (a["supply"] * sub(L["supplyIndex"], legacy_start(L["supplyStart"], a["supplierIndex"])) +
            a["borrow"] * sub(L["borrowIndex"], legacy_start(L["borrowStart"], a["borrowerIndex"])))


def unindexed(L):
    return (sub(L["blockNumber"], L["supplyBlock"]) * L["compSpeed"],
            sub(L["blockNumber"], L["borrowBlock"]) * L["compSpeed"])


def owed(L):
    us, ub = unindexed(L)
    return sum(pending_scaled(L, a) for a in L["accts"]) // D + us + ub


def owed_to(L, w):
    a = L["accts"][w] if w < len(L["accts"]) else NOACCT
    us, ub = unindexed(L)
    return pending_scaled(L, a) // D + (us if a["supply"] > 0 else 0) + (ub if a["borrow"] > 0 else 0)


def credited(s):
    return sum(a["accrued"] + a["wallet"] for a in s["accts"])


def credited_to(s, w):
    a = get(s, w)
    return a["accrued"] + a["wallet"]


def emitted_steps(L, ops):
    """Cumulative COMP emitted after each operation, and the speeds before each operation."""
    sp, e, cum, speeds = (L["compSpeed"], L["compSpeed"]), 0, [0], []
    for op in ops:
        speeds.append(sp)
        if op["op"] == "advance":
            e += op["blocks"] * (sp[0] + sp[1])
        elif op["op"] == "setSpeeds":
            sp = (op["supply"], op["borrow"])
        cum.append(e)
    return cum


def diff(p, q):
    """A short description of the first field where states p and q differ."""
    for k in ("blockNumber", "reserve"):
        if p[k] != q[k]:
            return f"{k} {q[k]} expected {p[k]}"
    for k in ("supplyState", "borrowState"):
        for f in ("index", "block", "speed"):
            if p[k][f] != q[k][f]:
                return f"{k}.{f} {q[k][f]} expected {p[k][f]}"
    if len(p["accts"]) != len(q["accts"]):
        return f"{len(q['accts'])} accounts, expected {len(p['accts'])}"
    for i, (a, b) in enumerate(zip(p["accts"], q["accts"])):
        for f in FIELDS:
            if a[f] != b[f]:
                return f"account {i} {f} {b[f]} expected {a[f]}"
    return "states differ"


def violations(case, start, steps):
    """Every requirement the reported states break, as in Spec.lean. `steps` is a list of
    {"ok", "state"}; `start` is the state reported after the upgrade."""
    L, ops = case["legacy"], case["ops"]
    if steps is None or len(steps) != len(ops):
        return [("WRAPPER", f"{0 if steps is None else len(steps)} steps for {len(ops)} operations")]
    v = []
    if start != upgrade(L):
        v.append(("WRAPPER", "state after the upgrade differs from upgrade(legacy): " + diff(upgrade(L), start)))
        return v
    states = [start] + [st["state"] for st in steps]
    for i, op in enumerate(ops):
        p, q, ok = states[i], states[i + 1], steps[i]["ok"]
        ok_e, exp, rid = expected(p, op)
        if ok and not ok_e and rid != "WRAPPER":
            # The spec's implementation would revert, but this one went ahead.
            v.append((rid, f"step {i} ({op['op']}): applied where the call must revert"))
        elif not ok and ok_e:
            if consistent(p) and rid != "WRAPPER":
                v.append(("REQ-CALLS-SUCCEED", f"step {i} ({op['op']}): refused in a consistent state"))
            elif q != p:
                v.append(("WRAPPER", f"step {i}: refused operation changed the state"))
        elif ok and q != exp:
            v.append((rid, f"step {i} ({op['op']}): " + diff(exp, q)))
        elif not ok and q != p:
            v.append(("WRAPPER", f"step {i}: refused operation changed the state"))
    if wellformed(L):
        cum = emitted_steps(L, ops)
        base, ow = credited(start), owed(L)
        for j, s in enumerate(states):
            if credited(s) > base + ow + cum[j]:
                v.append(("REQ-REWARDS-BOUNDED", f"after step {j - 1}: {credited(s)} credited, bound "
                          f"{base} held + {ow} owed + {cum[j]} emitted"))
                break
        n = max(len(s["accts"]) for s in states)
        done = False
        for w in range(n):
            bound = credited_to(start, w) + owed_to(L, w)
            for j, s in enumerate(states):
                if credited_to(s, w) > bound + cum[j]:
                    v.append(("REQ-ACCOUNT-BOUNDED", f"account {w} after step {j - 1}: {credited_to(s, w)} credited, "
                              f"bound {credited_to(start, w)} held + {owed_to(L, w)} owed + {cum[j]} emitted"))
                    done = True
                    break
            if done:
                break
        done = False
        for w in range(n):
            for i, s in enumerate(states):
                a = get(s, w)
                if a["supply"] or a["borrow"]:
                    continue
                for j in range(i + 1, len(states)):
                    if credited_to(states[j], w) > credited_to(s, w) + cum[j] - cum[i]:
                        v.append(("REQ-NO-BACKDATED-REWARDS",
                                  f"account {w} held no position after step {i - 1} and gained "
                                  f"{credited_to(states[j], w) - credited_to(s, w)} by step {j - 1}, "
                                  f"emitted {cum[j] - cum[i]}"))
                        done = True
                        break
                if done:
                    break
            if done:
                break
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
    return violations(case, out.get("start"), out.get("steps"))


def describe(out):
    steps = out.get("steps") or []
    if not steps:
        return "no steps"
    s = steps[-1]["state"]
    return (f"block {s['blockNumber']}, supply index {s['supplyState']['index']}, borrow index "
            f"{s['borrowState']['index']}, reserve {s['reserve']}, credited "
            f"{[a['accrued'] + a['wallet'] for a in s['accts']]}")


# Generators.

def _amount(rng):
    k = rng.random()
    if k < 0.3:
        return rng.randint(0, 100)
    if k < 0.6:
        return rng.randint(0, 10 ** 8)
    if k < 0.9:
        return rng.randint(0, 10 ** 22)
    return rng.choice([0, 1, 10 ** 8, 10 ** 18, 18977306140567618322762])


def _side(rng):
    """(index, block offset, start) for one side before the upgrade."""
    k = rng.random()
    if k < 0.35:
        return 0, 0                                      # never had rewards
    if k < 0.55:
        return INIT, INIT                                # rewards just started at compInitialIndex
    if k < 0.75:
        return INIT + rng.randint(0, 10 ** 38), INIT     # rewards since compInitialIndex
    if k < 0.9:
        return rng.randint(1, INIT - 1), 0               # grew from 0, still below compInitialIndex
    return INIT + rng.randint(0, 10 ** 38), 0            # grew from 0 past compInitialIndex


def _user_index(rng, idx, start):
    if idx == 0 or rng.random() < 0.45:
        return 0
    lo = max(start, 1)
    return rng.choice([idx, lo, rng.randint(lo, idx)]) if lo <= idx else 0


def gen_legacy(rng):
    blk = 13322798 + rng.randint(0, 1000)
    si, ss = _side(rng)
    bi, bs = _side(rng)
    speed = 0 if rng.random() < 0.5 else rng.choice([1, 3, 10 ** 15, rng.randint(1, 10 ** 17)])
    if si == 0 and bi == 0 and rng.random() < 0.8:
        speed = 0
    n = rng.randint(1, 4)
    accts = []
    for _ in range(n):
        accts.append(acct(supply=_amount(rng) if rng.random() < 0.7 else 0,
                          borrow=_amount(rng) if rng.random() < 0.6 else 0,
                          supplierIndex=_user_index(rng, si, ss), borrowerIndex=_user_index(rng, bi, bs),
                          accrued=rng.choice([0, 0, rng.randint(0, 10 ** 18)]),
                          wallet=rng.choice([0, 0, rng.randint(0, 10 ** 18)])))
    return {"blockNumber": blk, "compSpeed": speed, "supplyIndex": si,
            "supplyBlock": blk - (0 if si == 0 and rng.random() < 0.5 else rng.randint(0, 2000)),
            "borrowIndex": bi, "borrowBlock": blk - (0 if bi == 0 and rng.random() < 0.5 else rng.randint(0, 2000)),
            "supplyStart": ss, "borrowStart": bs,
            "reserve": rng.choice([0, 10 ** 18, 300514463598935139440340, rng.randint(0, 10 ** 24)]),
            "accts": accts}


def gen_ops(rng, n_accts, k=None):
    ops = []
    for _ in range(k if k is not None else rng.randint(1, 10)):
        who = rng.randrange(n_accts + (1 if rng.random() < 0.1 else 0))
        r = rng.random()
        if r < 0.12:
            ops.append({"op": "mint", "who": who, "amount": _amount(rng)})
        elif r < 0.2:
            ops.append({"op": "redeem", "who": who, "amount": _amount(rng)})
        elif r < 0.3:
            ops.append({"op": "transfer", "src": who, "dst": rng.randrange(n_accts), "amount": _amount(rng)})
        elif r < 0.4:
            ops.append({"op": "borrow", "who": who, "amount": _amount(rng)})
        elif r < 0.48:
            ops.append({"op": "repay", "who": who, "amount": _amount(rng)})
        elif r < 0.66:
            ops.append({"op": "claim", "who": who})
        elif r < 0.76:
            ops.append({"op": "setSpeeds", "supply": rng.choice([0, 1, 10 ** 15, rng.randint(0, 10 ** 17)]),
                        "borrow": rng.choice([0, 2, 10 ** 15, rng.randint(0, 10 ** 17)])})
        elif r < 0.94:
            ops.append({"op": "advance", "blocks": rng.choice([0, 1, 10, 139, rng.randint(0, 50000)])})
        else:
            ops.append({"op": "drip", "amount": _amount(rng)})
    return ops


def _incident(rng):
    """A market that never had rewards, holders with no recorded index, then a hook or a claim."""
    L = gen_legacy(rng)
    side = rng.choice(["supply", "borrow"])
    if side == "supply":
        L["supplyIndex"], L["supplyStart"] = 0, 0
        for a in L["accts"]:
            a["supplierIndex"] = 0
        L["accts"][0]["supply"] = max(1, L["accts"][0]["supply"])
    else:
        L["borrowIndex"], L["borrowStart"] = 0, 0
        for a in L["accts"]:
            a["borrowerIndex"] = 0
        L["accts"][0]["borrow"] = max(1, L["accts"][0]["borrow"])
    if rng.random() < 0.6:
        L["compSpeed"] = 0
    first = rng.choice([{"op": "claim", "who": 0}, {"op": "mint", "who": 0, "amount": rng.randint(0, 10 ** 8)},
                        {"op": "borrow", "who": 0, "amount": rng.randint(0, 10 ** 8)},
                        {"op": "advance", "blocks": rng.randint(0, 200)}])
    return {"legacy": L, "ops": [first] + gen_ops(rng, len(L["accts"]), rng.randint(0, 5)) + [{"op": "claim", "who": 0}]}


def gen_case(rng):
    if rng.random() < 0.3:
        return _incident(rng)
    L = gen_legacy(rng)
    return {"legacy": L, "ops": gen_ops(rng, len(L["accts"]))}
