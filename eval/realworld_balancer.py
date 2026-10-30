#!/usr/bin/env python3
"""Balancer V2 swap rounding: the deployed Vault and pool against the proved swap wrapper.

For realworld/tasks/rw-balancer-upscale this script:
  1. port       kernel-checks witnesses/attack_batch.lean on the Lean port of the swap wrapper
                (the refutations with the constant-product math, and the replay of the attack's 90
                swaps with the StableMath port), and the Balancer-style unit tests
                (tests/PortUnitTests.lean) on the port and on the proved component;
  2. real code  forks Ethereum just before the attack transaction
                0x6ed07db1a9fe5c0794d44cd36081d6a6df103fab868cdd75d581e3bd23bc9742, runs the
                attack's first 22 swaps as one batchSwap (BPT for WETH and osETH, which leaves the
                osETH/WETH pool with 67,000 wei of each), and runs every swap batch through the
                deployed Vault's `swap` (realworld/adapters/balancer, forge), from that state or from
                the state before the transaction;
  3. Lean       runs the same batches, from the same balances and with the scaling factors, fee and
                amplification the fork reports, through the executable of the port and of a
                judge-accepted candidate (an accepted Muse repair when one exists, otherwise the
                build-team reference), both with the StableMath port as the pool math;
  4. compare    compares the deployed code with the port and with the proved component swap by swap,
                measures the pool's invariant D (StableMath port) and the deployed pool's own
                getRate() before and after every batch, and states each fall of D on the deployed
                code's balances as a `decide` goal, checked in the kernel.

What is proved: the swap wrapper accepted by the judge meets every requirement for every pool math
that meets `WellBehaved`, every pool and every batch. What is tested: the deployed contracts, batch
by batch. StableMath is not proved to meet `WellBehaved`, so on the StableMath batches the
proved component's results are tested, not proved.

Needs Docker, git, forge, and an Ethereum RPC endpoint that serves archive state at block 23717397
(PF_ETH_RPC, default https://eth.drpc.org). forge-std is fetched at a pinned commit into
PF_REALWORLD_CACHE (default ~/.cache/proofforge-realworld).

Usage: realworld_balancer.py [--cases 500] [--seed 0] [--out results/balancer-1]
"""
import argparse, json, os, pathlib, random, shutil, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import binary_check, judge, task as taskmod  # noqa: E402

TASK = ROOT / "realworld" / "tasks" / "rw-balancer-upscale"
ADAPTER = ROOT / "realworld" / "adapters" / "balancer"
CACHE = pathlib.Path(os.environ.get("PF_REALWORLD_CACHE", pathlib.Path.home() / ".cache" / "proofforge-realworld"))
RPC = os.environ.get("PF_ETH_RPC", "https://eth.drpc.org")
FORGE_STD = ("https://github.com/foundry-rs/forge-std", "v1.11.0", "8e40513d678f392f398620b3ef2b418648b33e89")
ATTACK_TX = "0x6ed07db1a9fe5c0794d44cd36081d6a6df103fab868cdd75d581e3bd23bc9742"

# Swap events 1 to 22 of the attack transaction: GIVEN_OUT, BPT (registered index 1) in, WETH
# (0) or osETH (2) out, with the amounts out the Vault logged.
SETUP = [(1, 0, 4873132999218408001625), (1, 2, 6783065423678905706961), (1, 0, 48731329992184080017),
         (1, 2, 67830654236789057069), (1, 0, 487313299921840800), (1, 2, 678306542367890571),
         (1, 0, 4873132999218408), (1, 2, 6783065423678906), (1, 0, 48731329992184), (1, 2, 67830654236789),
         (1, 0, 487313299922), (1, 2, 678306542367), (1, 0, 4873132999), (1, 2, 6783065424), (1, 0, 48731330),
         (1, 2, 67830654), (1, 0, 487313), (1, 2, 678307), (1, 0, 4873), (1, 2, 6783), (1, 0, 50), (1, 2, 69)]

# Swap events 23 to 112: 30 rounds of GIVEN_OUT swaps on the pool's two tokens, (token in, token
# out, amount out) with 0 = WETH and 1 = osETH, and the amounts in the Vault logged.
ATTACK_OUT = [66982, 17, 891000, 5165, 17, 666000, 9016, 17, 495000, 12206, 17, 369000, 17532, 17, 270000,
              14434, 17, 198000, 11377, 17, 160000, 22554, 17, 120000, 17663, 17, 89100, 12038, 17, 67500,
              10414, 17, 52200, 9007, 17, 40500, 7867, 17, 31500, 6554, 17, 24300, 5472, 17, 19800, 4749,
              17, 16200, 4397, 17, 12600, 3442, 17, 10800, 3296, 17, 9000, 2886, 17, 7371, 2286, 17, 6480,
              2124, 17, 6075, 2014, 17, 5589, 1902, 17, 4779, 1730, 17, 4455, 1664, 17, 3969, 1562, 17,
              3726, 1492, 17, 3645, 1484, 17, 3564, 1444, 17, 3564]
ATTACK_IN = [307353, 625492, 5182, 173500, 467227, 9033, 132041, 342353, 12223, 100574, 248534, 17549, 81018,
             180744, 14451, 59801, 132219, 11394, 43522, 97179, 22571, 46521, 72880, 17680, 34992, 55507,
             12055, 24595, 40578, 10431, 19485, 31093, 9024, 15863, 23232, 7884, 12817, 17991, 6571, 10203,
             13414, 5489, 8237, 11093, 4766, 6908, 8499, 4414, 6056, 6537, 3459, 4937, 5309, 3313, 4365,
             4440, 2903, 3926, 3590, 2303, 3137, 3131, 2141, 2937, 3098, 2031, 2827, 2670, 1919, 2385, 2200,
             1747, 2189, 2173, 1681, 2109, 1716, 1579, 1984, 1701, 1509, 1909, 1692, 1501, 1893, 1687, 1461,
             1858, 1685, 1471]


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def attack_swaps():
    return [{"kind": "out", "in": 0 if k % 3 != 2 else 1, "out": 1 if k % 3 != 2 else 0, "amount": a}
            for k, a in enumerate(ATTACK_OUT)]


# Cases: batches in the deployed Vault's domain (amounts above zero, the pool's two tokens).

def attack_balances():
    """Pool balances (WETH, osETH) before each round of the attack, from the logged amounts."""
    bal, out = [67000, 67000], []
    for k, (o, i) in enumerate(zip(ATTACK_OUT, ATTACK_IN)):
        if k % 3 == 0:
            out.append(list(bal))
        tin, tout = (0, 1) if k % 3 != 2 else (1, 0)
        bal[tin] += i
        bal[tout] -= o
    return out + [bal]


def gen_cases(n, seed):
    rng = random.Random(seed)
    rounds = attack_balances()
    out = []
    while len(out) < n:
        k = rng.random()
        if k < 0.4:
            # The attack's shape from the 67,000-wei state: the first r rounds of the attack as
            # logged, then 1 to 3 rounds of the same shape with other amounts (osETH out down to a
            # few wei, a few wei of osETH out, WETH out paid with osETH).
            r = rng.randint(0, 29)
            swaps = attack_swaps()[:3 * r]
            weth, oseth = rounds[r]
            for _ in range(rng.randint(1, 3)):
                left = rng.randint(2, 40)
                swaps.append({"kind": "out", "in": 0, "out": 1, "amount": max(1, oseth - left)})
                swaps.append({"kind": "out", "in": 0, "out": 1, "amount": rng.randint(1, left - 1)})
                swaps.append({"kind": "out", "in": 1, "out": 0, "amount": rng.randint(1, max(1, weth))})
            out.append({"start": 0, "swaps": swaps})
        else:
            start = 0 if k < 0.7 else 1
            swaps = []
            for _ in range(rng.randint(1, 6)):
                i = rng.randrange(2)
                hi = 70000 if start == 0 else 6 * 10**21
                a = rng.choice([rng.randint(1, 40), rng.randint(1, hi), rng.randint(1, hi // 1000 + 1)])
                swaps.append({"kind": rng.choice(["in", "out"]), "in": i, "out": 1 - i, "amount": a})
            out.append({"start": start, "swaps": swaps})
    return out


def encode(case):
    f = [str(case["start"]), str(len(case["swaps"]))]
    for s in case["swaps"]:
        f += ["0" if s["kind"] == "in" else "1", str(s["in"]), str(s["out"]), str(s["amount"])]
    return " ".join(f)


# The deployed contracts.

def forge_project():
    d = CACHE / "balancer-forge"
    std = d / "lib" / "forge-std"
    if not std.exists():
        std.parent.mkdir(parents=True, exist_ok=True)
        r = sh(["git", "clone", "-q", FORGE_STD[0], str(std)])
        if r.returncode:
            raise RuntimeError(r.stderr)
    r = sh(["git", "-C", str(std), "checkout", "-q", FORGE_STD[2]])
    if r.returncode or sh(["git", "-C", str(std), "rev-parse", "HEAD"]).stdout.strip() != FORGE_STD[2]:
        raise RuntimeError(f"forge-std is not at {FORGE_STD[2]}")
    shutil.copy(ADAPTER / "foundry.toml", d / "foundry.toml")
    (d / "test").mkdir(exist_ok=True)
    shutil.copy(ADAPTER / "test" / "Replay.t.sol", d / "test" / "Replay.t.sol")
    (d / "io").mkdir(exist_ok=True)
    return d


def run_chunk(d, cases):
    """One forge run (a fresh fork) on `cases`; returns the header, start states and outputs."""
    (d / "io" / "cases.txt").write_text("".join(encode(c) + "\n" for c in cases))
    (d / "io" / "out.txt").unlink(missing_ok=True)
    r = sh(["forge", "test", "--match-test", "test_replay"], cwd=d, env={**os.environ, "PF_ETH_RPC": RPC}, timeout=7200)
    if "[PASS]" not in r.stdout:
        raise RuntimeError(r.stdout[-3000:] + r.stderr[-3000:])
    lines = (d / "io" / "out.txt").read_text().splitlines()
    head = lines[0].split()
    pool = {"rates": [int(head[1]), int(head[2])], "fee": int(head[3]), "amp": int(head[4])}
    starts = {}
    for line in lines[1:3]:
        f = line.split()
        starts[int(f[1])] = {"balances": [int(f[2]), int(f[3])], "rate": None if f[4] == "x" else int(f[4])}
    outs, cur = [], []
    for line in lines[3:]:
        f = line.split()
        if f[0] == "end":
            outs.append({"steps": cur, "rate_after": None if f[1] == "x" else int(f[1])})
            cur = []
            continue
        cur.append({"ok": f[0] == "1", "quote": int(f[1]) if f[0] == "1" else None, "balances": [int(f[2]), int(f[3])]})
    if len(outs) != len(cases):
        raise RuntimeError(f"forge reported {len(outs)} batches for {len(cases)}")
    return pool, starts, outs


def run_real(cases, chunk=100):
    """Every batch on the deployed contracts, in forge runs of `chunk` batches (each a fresh fork
    of the same state; one run holds all its output in EVM memory)."""
    d = forge_project()
    (d / "io" / "setup.txt").write_text("".join(f"{i} {j} {a}\n" for i, j, a in SETUP))
    pool = starts = None
    outs = []
    for k in range(0, len(cases), chunk):
        p, s, o = run_chunk(d, cases[k:k + chunk])
        if pool is None:
            pool, starts = p, s
        elif (p, s) != (pool, starts):
            raise RuntimeError("the fork's pool parameters or start states differ between runs")
        outs += o
    return pool, starts, outs, sh(["forge", "--version"]).stdout.splitlines()[0]


# Lean executables built from candidates.

def lean_outputs(t, candidate, reqs, need_accept):
    j = judge.judge(str(candidate), task=t) if need_accept else None
    if need_accept and not j["accepted"]:
        raise RuntimeError(f"{candidate} is not accepted by the judge")
    ws = judge.load_workspace(str(candidate))
    project = judge.fresh_project(ws, judge.candidate_files(ws), t)
    b = binary_check.build(project, t)
    if b["exit_code"]:
        raise RuntimeError(b["output_tail"])
    sha = (project / "binary.sha256").read_text().strip()
    outs = binary_check.run_cases(project, t.exe, reqs, "balancer")
    shutil.rmtree(project, ignore_errors=True)
    return outs, sha, (j or {}).get("solution_tree_sha256")


def lean_check(t, candidate, files):
    """Build `candidate` in a fresh project and check each Lean file in `files` ({name: text})."""
    ws = judge.load_workspace(str(candidate))
    project = judge.fresh_project(ws, judge.candidate_files(ws), t)
    for name, text in files.items():
        (project / name).write_text(text)
    script = "lake build BalancerSwap Solution >/tmp/b.log 2>&1 || { tail -20 /tmp/b.log; exit 3; }; " + "; ".join(
        f"echo '== {name}'; lake env lean {name} 2>&1; echo \"exit $?\"" for name in files)
    r = judge.in_container(project, script)
    shutil.rmtree(project, ignore_errors=True)
    out, res = r["output_tail"], {}
    for name in files:
        part = out.split(f"== {name}\n", 1)[-1].split("\n== ", 1)[0]
        res[name] = ("exit 0" in part and "error" not in part, part.strip()[-1500:])
    return res


def verified_candidate(t, out):
    for run in sorted(out.glob("repair-*")):
        p = run / "passport.json"
        if p.exists() and json.loads(p.read_text())["status"] == "VERIFIED":
            return run / "final.lean", f"Muse repair {run.name} (Passport {json.loads(p.read_text())['passport_sha256'][:16]})"
    return t.root / "reference" / "SolutionA.lean", "build-team reference (reference/SolutionA.lean)"


def request(pool, balances, swaps):
    return {"math": "stable", "amp": pool["amp"], "pool": {"balances": balances, "rates": pool["rates"], "fee": pool["fee"]},
            "swaps": swaps}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=500)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default="results/balancer-1")
    a = ap.parse_args()
    out = (ROOT / a.out).resolve()
    d = out / "real-code"
    d.mkdir(parents=True, exist_ok=True)
    t = taskmod.load(TASK)
    t0 = time.monotonic()

    # 1. The port: kernel refutation, attack replay and unit tests.
    port = TASK / "attacks" / "balancer_port.lean"
    tests = (TASK / "tests" / "PortUnitTests.lean").read_text()
    res = lean_check(t, port, {"AttackBatch.lean": (TASK / "witnesses" / "attack_batch.lean").read_text(),
                               "UnitTests.lean": tests})
    candidate, label = verified_candidate(t, out)
    res_proved = lean_check(t, candidate, {"UnitTests.lean": tests})
    print(f"port: attack witness {'checked' if res['AttackBatch.lean'][0] else 'FAILED'}, unit tests "
          f"{'pass' if res['UnitTests.lean'][0] else 'FAIL'}; proved component ({label}): unit tests "
          f"{'pass' if res_proved['UnitTests.lean'][0] else 'FAIL'}", flush=True)

    # 2. The deployed contracts.
    documented = [{"start": 0, "swaps": attack_swaps(), "label": "attack transaction, Swap events 23 to 112"}]
    cases = documented + gen_cases(a.cases, a.seed)
    pool, starts, real, forge = run_real(cases)
    print(f"fork: scaling factors {pool['rates']}, fee {pool['fee']}, amp {pool['amp']}; start states {starts}; "
          f"{len(real)} batches run", flush=True)

    # 3. The Lean executables on the same batches; D of every real balance pair.
    reqs = [request(pool, starts[c["start"]]["balances"], c["swaps"]) for c in cases]
    ref_outs, ref_sha, ref_tree = lean_outputs(t, candidate, reqs, True)
    port_outs, port_sha, _ = lean_outputs(t, port, reqs, False)
    pairs = sorted({tuple(starts[c["start"]]["balances"]) for c in cases} |
                   {tuple(s["balances"]) for r in real for s in r["steps"]})
    d_outs, _, _ = lean_outputs(t, port, [request(pool, list(p), []) for p in pairs], False)
    D = {p: o.get("value_before") for p, o in zip(pairs, d_outs)}

    # 4. Compare.
    rep = {"batches": len(cases), "documented": len(documented), "swaps": sum(len(c["swaps"]) for c in cases),
           "real_same_as_port": 0, "real_differs_from_port": [], "real_same_as_proved": 0,
           "swaps_real_charged_less_than_proved": 0, "batches_lowering_D_real": 0, "batches_lowering_D_proved": 0,
           "batches_lowering_rate_real": 0, "batches_ok_real": 0, "batches_ok_proved": 0,
           "by_start": {k: {"batches": 0, "ok_real": 0, "D_falls_real": 0, "rate_falls_real": 0} for k in (0, 1)},
           "documented_results": [], "witnesses": []}
    for i, (c, r, p, q) in enumerate(zip(cases, real, port_outs, ref_outs)):
        rs = [(s["ok"], s["quote"], s["balances"]) for s in r["steps"]]
        ps = [(s["ok"], s["quote"] if s["ok"] else None, s["balances"]) for s in p.get("steps", [])]
        qs = [(s["ok"], s["quote"] if s["ok"] else None, s["balances"]) for s in q.get("steps", [])]
        if rs == ps:
            rep["real_same_as_port"] += 1
        elif len(rep["real_differs_from_port"]) < 20:
            rep["real_differs_from_port"].append({"case": i, "input": c, "real": r, "port": p})
        if rs == qs:
            rep["real_same_as_proved"] += 1
        for s, rr, qq in zip(c["swaps"], r["steps"], q.get("steps", [])):
            if s["kind"] == "out" and rr["ok"] and qq["ok"] and rr["quote"] < qq["quote"]:
                rep["swaps_real_charged_less_than_proved"] += 1
        b0 = tuple(starts[c["start"]]["balances"])
        ok = all(s["ok"] for s in r["steps"]) and len(r["steps"]) == len(c["swaps"])
        b1 = tuple(r["steps"][-1]["balances"]) if ok and r["steps"] else b0
        d0, d1 = D.get(b0), D.get(b1)
        lowered = d0 is not None and d1 is not None and d1 < d0
        bs = rep["by_start"][c["start"]]
        bs["batches"] += 1
        if ok:
            rep["batches_ok_real"] += 1
            bs["ok_real"] += 1
        if q.get("ok"):
            rep["batches_ok_proved"] += 1
        if lowered:
            rep["batches_lowering_D_real"] += 1
            bs["D_falls_real"] += 1
        if q.get("ok") and q.get("value_before") is not None and q.get("value_after") is not None and \
                q["value_after"] < q["value_before"]:
            rep["batches_lowering_D_proved"] += 1
        r0 = starts[c["start"]]["rate"]
        if ok and r0 is not None and r["rate_after"] is not None and r["rate_after"] < r0:
            rep["batches_lowering_rate_real"] += 1
            bs["rate_falls_real"] += 1
        if i < len(documented):
            rep["documented_results"].append({
                "case": i, "label": c["label"], "swaps": len(c["swaps"]),
                "all_ok": ok, "amounts_in_match_chain": [s["quote"] for s in r["steps"]] == ATTACK_IN,
                "balances_after": list(b1), "D_before": d0, "D_after": d1,
                "rate_before": r0, "rate_after": r["rate_after"],
                "port_same": rs == ps, "proved": {"ok": q.get("ok"), "steps_ok": sum(1 for s in q.get("steps", []) if s["ok"]),
                                                  "first_quote": (q.get("steps") or [{}])[0].get("quote")}})
        if lowered and (i < len(documented) or len(rep["witnesses"]) < 6):
            rep["witnesses"].append({"case": i, "documented": i < len(documented), "balances_before": list(b0),
                                     "balances_after": list(b1), "D_before": d0, "D_after": d1})
    lines = ["import BalancerSwap.StableMath", "open BalancerSwap", "",
             "def pool2 (w o : Nat) : Pool where",
             "  n := 2",
             "  balance k := if k = 0 then w else if k = 1 then o else 0",
             f"  rate k := if k = 1 then {pool['rates'][1]} else {pool['rates'][0]}",
             f"  fee := {pool['fee']}", ""]
    for w in rep["witnesses"]:
        (x0, y0), (x1, y1) = w["balances_before"], w["balances_after"]
        w["lean_goal"] = (f"value (stableMath {pool['amp']} 2) (pool2 {x1} {y1}) < "
                          f"value (stableMath {pool['amp']} 2) (pool2 {x0} {y0})")
        lines += [f"-- case {w['case']}: D {w['D_before']} -> {w['D_after']}", f"example : {w['lean_goal']} := by decide", ""]
    text = "\n".join(lines) + "\n"
    (d / "Confirm.lean").write_text(text)
    ok, tail = lean_check(t, candidate, {"Confirm.lean": text})["Confirm.lean"] if rep["witnesses"] else (True, "")
    (d / "cases.jsonl").write_text("".join(json.dumps(r) + "\n" for r in reqs))
    (d / "real-outputs.jsonl").write_text("".join(json.dumps(o) + "\n" for o in real))
    (d / "port-outputs.jsonl").write_text("".join(json.dumps(o) + "\n" for o in port_outs))
    (d / "proved-outputs.jsonl").write_text("".join(json.dumps(o) + "\n" for o in ref_outs))
    report = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "elapsed_s": round(time.monotonic() - t0, 1),
        "task": t.id, "source": t.meta["source"], "rpc": RPC, "fork": {"transaction": ATTACK_TX,
        "note": "forked at the state just before the attack transaction (forge createSelectFork with the transaction hash)"},
        "forge": forge, "forge_std": {"repository": FORGE_STD[0], "tag": FORGE_STD[1], "commit": FORGE_STD[2]},
        "image": judge.IMAGE, "image_id": judge.image_id(), "seed": a.seed,
        "pool": pool, "start_states": starts, "setup": "the attack's first 22 swaps as one batchSwap (GIVEN_OUT, BPT in)",
        "port": {"candidate": "realworld/tasks/rw-balancer-upscale/attacks/balancer_port.lean", "executable_sha256": port_sha,
                 "attack_witness": "realworld/tasks/rw-balancer-upscale/witnesses/attack_batch.lean",
                 "attack_witness_checked": res["AttackBatch.lean"][0], "attack_witness_output_tail": res["AttackBatch.lean"][1],
                 "unit_tests": "realworld/tasks/rw-balancer-upscale/tests/PortUnitTests.lean",
                 "unit_tests_pass": res["UnitTests.lean"][0], "unit_tests_output_tail": res["UnitTests.lean"][1],
                 "unit_tests_on_proved": res_proved["UnitTests.lean"][0],
                 "unit_tests_on_proved_output_tail": res_proved["UnitTests.lean"][1]},
        "proved": {"candidate": label, "executable_sha256": ref_sha, "solution_tree_sha256": ref_tree},
        "comparison": rep,
        "lean_confirmation": {"file": "real-code/Confirm.lean", "goals": len(rep["witnesses"]),
                              "checked": len(rep["witnesses"]) if ok else 0, "output_tail": tail},
    }
    (d / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"real code: {rep['real_same_as_port']} of {len(cases)} batches identical to the port, "
          f"{rep['real_same_as_proved']} identical to the proved component; D falls in {rep['batches_lowering_D_real']} "
          f"real batches and {rep['batches_lowering_D_proved']} proved-component batches; getRate falls in "
          f"{rep['batches_lowering_rate_real']} real batches; Lean goals checked {report['lean_confirmation']['checked']} "
          f"of {len(rep['witnesses'])}", flush=True)
    print(f"wrote {d / 'report.json'}")


if __name__ == "__main__":
    main()
