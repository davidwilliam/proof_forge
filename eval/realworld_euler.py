#!/usr/bin/env python3
"""Real-world bug: Euler Finance v1 donateToReserves, checked against the proved lending market.

For realworld/tasks/rw-euler-donate this script:
  1. port       checks the kernel refutation of the Lean port (witnesses/buggy_original.lean:
                the attack sequence, `decide`) and Euler's own donateToReserves unit tests,
                ported to Lean (unit-tests/ReservesDonate.lean), on the port and on the
                proved component;
  2. reference  builds the executable from a judge-accepted candidate (an accepted Muse repair
                when one exists, otherwise the build-team reference) and runs it on every
                sequence;
  3. real code  fetches euler-xyz/euler-contracts at the pinned commit, checks every Solidity
                file it relies on against the commit's git blob hashes, deploys the modules
                unmodified in a local Foundry test (realworld/adapters/euler), runs the attack
                sequence, Euler's own reservesDonate.js scenarios and generated sequences, and
                checks the state after every operation against the task's requirements (the task
                oracle mirrors Spec.lean) and against Euler's own liquidity computation
                (`Exec.liquidity`: collateralValue < liabilityValue is a violation). It does the
                same on a local copy with one line added to donateToReserves,
                `checkLiquidity(account)`, which is not an upstream release;
  4. confirm    states each real-code solvency violation as a `decide` goal over the Lean
                `Healthy` predicate and checks it in the Lean kernel.

What is proved: the Lean component accepted by the judge meets every requirement for every
reachable state. What is tested: the real contracts, sequence by sequence. The real contracts
are not proved.

Euler's sources are fetched at run time into PF_REALWORLD_CACHE (default
~/.cache/proofforge-realworld) and never copied into this repository. Needs network access for
the first fetch, Docker (the pinned Lean image), and Foundry (`forge`, which downloads solc
0.8.10 on first use).

Usage: realworld_euler.py [--cases 1000] [--seed 0] [--out results/euler-1]
"""
import argparse, hashlib, io, json, os, pathlib, random, shutil, subprocess, sys, tarfile, time, urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "eval")]
import judge, task as taskmod  # noqa: E402
from realworld import lean_check, reference_outputs, verified_candidate  # noqa: E402

TASK = ROOT / "realworld" / "tasks" / "rw-euler-donate"
ADAPTER = ROOT / "realworld" / "adapters" / "euler"
CACHE = pathlib.Path(os.environ.get("PF_REALWORLD_CACHE", pathlib.Path.home() / ".cache" / "proofforge-realworld"))
COMMIT = "b1ee3265853628d5a529081d7908c38404201b4e"
ARCHIVE = f"https://codeload.github.com/euler-xyz/euler-contracts/tar.gz/{COMMIT}"
# Git blob hashes at COMMIT (as `git hash-object` computes them), checked after extraction.
BLOBS = {
    "contracts/modules/EToken.sol": "8ab8d85a96b328f16c6004bb87c2ee8fdcb93b82",
    "contracts/modules/DToken.sol": "d539cc7b708e106f446d7d89d85e5a471e00b266",
    "contracts/modules/Liquidation.sol": "72d7dec4e7aa3976c050806fdbbc321e01075625",
    "contracts/modules/RiskManager.sol": "7b5a1dd9b9a4525e59682005bea92cf3dbb77312",
    "contracts/BaseLogic.sol": "c8b5e9c247fb37ab7598223a3e4f1097ef94d4bb",
    "contracts/Constants.sol": "023aec639eae4f8001d02cd7c3d4fab298a61859",
    "test/reservesDonate.js": "9d945147532fd967dd0cb30b377a468aa7a3e55b",
}
DONATE_END = ("        emitViaProxy_Transfer(proxyAddr, account, address(0), amount);\n\n"
              "        logAssetStatus(assetCache);\n    }\n}")
DONATE_PATCHED = ("        emitViaProxy_Transfer(proxyAddr, account, address(0), amount);\n\n"
                  "        checkLiquidity(account);\n\n"
                  "        logAssetStatus(assetCache);\n    }\n}")
SEED = 10**6               # wei sent to the Euler contract so the pool matches INITIAL_RESERVES
INITIAL_RESERVES = 10**6   # Constants.sol
E18 = 10**18
KINDS = {"deposit": 0, "withdraw": 1, "borrow": 2, "repay": 3, "mint": 4, "burn": 5, "transfer": 6,
         "donate": 7, "liquidate": 8}

VARIANTS = [
    {"tag": "b1ee326", "commit": COMMIT, "status": "buggy", "patched": False,
     "note": "unmodified contracts at the pinned commit (EToken.sol is byte-identical on the archived master branch)"},
    {"tag": "b1ee326+checkLiquidity", "commit": COMMIT, "status": "patched locally", "patched": True,
     "note": "local copy with `checkLiquidity(account);` added to donateToReserves; not an upstream release"},
]


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def blob_sha(b):
    return hashlib.sha1(b"blob %d\0" % len(b) + b).hexdigest()


def source():
    """The project tree at COMMIT, extracted into the cache; every file in BLOBS is checked."""
    dest = CACHE / "euler" / f"src-{COMMIT[:12]}"
    if not dest.exists():
        data = urllib.request.urlopen(ARCHIVE, timeout=300).read()
        tmp = CACHE / "euler" / f"tmp-{os.getpid()}"
        shutil.rmtree(tmp, ignore_errors=True)
        tmp.mkdir(parents=True)
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tf:
            tf.extractall(tmp, filter="data")
        (top,) = list(tmp.iterdir())
        if top.name != f"euler-contracts-{COMMIT}":
            raise RuntimeError(f"unexpected archive root {top.name}")
        top.rename(dest)
        shutil.rmtree(tmp, ignore_errors=True)
    for rel, want in BLOBS.items():
        got = blob_sha((dest / rel).read_bytes())
        if got != want:
            raise RuntimeError(f"{rel}: blob {got}, expected {want} at {COMMIT}")
    return dest


def workdir(src, v):
    """A Foundry project: Euler's contracts in src/ (patched or not), the driver in test/."""
    d = CACHE / "euler" / f"work-{v['tag']}"
    if not (d / "src").exists():
        shutil.copytree(src / "contracts", d / "src")
    et = d / "src/modules/EToken.sol"
    text = (src / "contracts/modules/EToken.sol").read_text()
    if v["patched"]:
        if text.count(DONATE_END) != 1:
            raise RuntimeError("donateToReserves end not found")
        text = text.replace(DONATE_END, DONATE_PATCHED)
    et.write_text(text)
    (d / "test").mkdir(exist_ok=True)
    (d / "io").mkdir(exist_ok=True)
    shutil.copy(ADAPTER / "EulerDriver.t.sol", d / "test/EulerDriver.t.sol")
    shutil.copy(ADAPTER / "foundry.toml", d / "foundry.toml")
    (d / "lib/hardhat").mkdir(parents=True, exist_ok=True)
    shutil.copy(ADAPTER / "console.sol", d / "lib/hardhat/console.sol")
    return d, hashlib.sha256(et.read_bytes()).hexdigest()


def encode(case):
    words = [case["n"], len(case["ops"])]
    for op in case["ops"]:
        k = KINDS[op[0]]
        if k == 6:
            words += [k, op[1], op[2], op[3]]
        elif k == 8:
            words += [k, op[1], op[2], 0]
        else:
            words += [k, op[1], op[2], 0]
    b = (32).to_bytes(32, "big") + len(words).to_bytes(32, "big") + b"".join(w.to_bytes(32, "big") for w in words)
    return "0x" + b.hex()


def run_forge(d, cases):
    (d / "io/cases.txt").write_text("".join(encode(c) + "\n" for c in cases))
    out = d / "io/out.jsonl"
    out.unlink(missing_ok=True)
    env = {**os.environ, "EULER_CASES": "io/cases.txt", "EULER_OUT": "io/out.jsonl"}
    r = sh(["forge", "test", "--match-test", "testRunCases", "-q"], cwd=d, env=env, timeout=7200)
    if r.returncode or not out.exists():
        raise RuntimeError((r.stdout + r.stderr)[-4000:])
    return [json.loads(l) for l in out.read_text().splitlines() if l.strip()]


def normalize(st):
    """Model state from the contracts' raw values (exchange rate exactly 1, see the driver)."""
    return {"acct": [list(a) for a in st["acct"]], "cash": st["pool"] - SEED,
            "reserves": st["reserveBalance"] - INITIAL_RESERVES}


def real_cases(rng, n):
    """Generated sequences in the contracts' domain: liquidations use checkLiquidation's largest
    repay, and amounts stay below MAX_SANE_AMOUNT (2^112)."""
    out = []
    while len(out) < n:
        c = oracle.gen_case(rng)
        if c["ops"] == oracle.HONEST:
            out.append(c)
            continue
        c["ops"] = [op[:3] + ["max"] if op[0] == "liquidate" else op for op in c["ops"]]
        if all(x < 2**100 for op in c["ops"] for x in op[1:] if isinstance(x, int)):
            out.append(c)
    return out


ATTACK = [["deposit", 0, 8904507 * E18], ["deposit", 1, 20000000 * E18], ["mint", 1, 200000000 * E18],
          ["repay", 1, 10000000 * E18], ["mint", 1, 200000000 * E18], ["donate", 1, 100000000 * E18],
          ["liquidate", 2, 1, "max"], ["withdraw", 2, 38904507 * E18]]
# test/reservesDonate.js at COMMIT, the three tests the model covers (et.eth(n) = n * 1e18).
REPO_TESTS = [
    {"name": "donate to reserves - basic", "ops": [["deposit", 0, 10 * E18], ["donate", 0, E18]],
     "expect": {"ok": [True, True], "acct0": [9 * E18, 0], "reserves": E18, "cash": 10 * E18}},
    {"name": "donate to reserves - max uint (the whole balance)", "ops": [["deposit", 0, 10 * E18], ["donate", 0, 10 * E18]],
     "expect": {"ok": [True, True], "acct0": [0, 0], "reserves": 10 * E18, "cash": 10 * E18}},
    {"name": "donate to reserves - insufficient balance", "ops": [["deposit", 0, 10 * E18], ["donate", 0, 11 * E18]],
     "expect": {"ok": [True, False], "acct0": [10 * E18, 0], "reserves": 0, "cash": 10 * E18}},
]


def classify(case, real, proved):
    """Per sequence: requirement violations of the real contracts, Euler's own liquidity
    violations, and agreement with the proved component. A step where the contracts succeed
    without changing anything on an operation the model refuses (Euler returns early on a
    zero-amount transfer and on a liquidation without opportunity) is counted as a no-op and
    agrees with the proved component when the states agree."""
    n = case["n"]
    s = oracle.genesis(n)
    viol, euler_viol, noops, first_diff = [], [], 0, None
    for i, (op, st) in enumerate(zip(case["ops"], real["steps"])):
        op = oracle.resolve(op, s["acct"])
        s2 = normalize(st)
        ok = st["ok"]
        noop = ok and s2 == s and not oracle.allowed(s, op)
        if noop:
            noops += 1          # Euler returns early (zero transfer, healthy violator): no change
        else:
            for rid, msg in oracle.transition_violations(s, op, ok, s2):
                viol.append({"step": i, "requirement": rid, "message": msg})
        for w, (e, d) in enumerate(s2["acct"]):
            if not oracle.healthy(e, d):
                viol.append({"step": i, "requirement": "REQ-NO-BAD-DEBT",
                             "message": f"account {w} owes {d} against {e}", "account": w, "e": e, "d": d})
        for w, (cv, lv) in enumerate(st["liq"]):
            if cv < lv:
                euler_viol.append({"step": i, "account": w, "collateralValue": cv, "liabilityValue": lv})
        if proved is not None and first_diff is None:
            p = proved["steps"][i]
            if (p["ok"] != ok and not noop) or {"acct": p["acct"], "cash": p["cash"], "reserves": p["reserves"]} != s2:
                first_diff = {"step": i, "op": op, "real": {"ok": ok, **s2},
                              "proved": {k: p[k] for k in ("ok", "acct", "cash", "reserves")}}
        s = s2
    return viol, euler_viol, noops, first_diff


def to_model_case(case):
    return {"n": case["n"], "ops": [list(op) for op in case["ops"]]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default="results/euler-1")
    a = ap.parse_args()
    t = taskmod.load(TASK)
    global oracle
    oracle = t.oracle
    out = (ROOT / a.out).resolve()
    d = out / t.id / "real-code"
    d.mkdir(parents=True, exist_ok=True)

    documented = [{"n": 3, "ops": ATTACK, "label": "attack (whole DAI x 1e18)"}] + \
                 [{"n": 1, "ops": rt["ops"], "label": f"reservesDonate.js: {rt['name']}"} for rt in REPO_TESTS]
    rng = random.Random(a.seed)
    cases = documented + real_cases(rng, a.cases)
    (d / "cases.jsonl").write_text("".join(json.dumps({k: c[k] for k in ("n", "ops")}) + "\n" for c in cases))
    print(f"[euler] {len(cases)} sequences ({len(documented)} documented)", flush=True)

    # 1. Port: kernel refutation and Euler's unit tests in Lean.
    port = t.root / "attacks" / "buggy_original.lean"
    ref = t.root / "reference" / "SolutionA.lean"
    wit = (t.root / "witnesses" / "buggy_original.lean").read_text()
    ut = (t.root / "unit-tests" / "ReservesDonate.lean").read_text()
    on_port = lean_check(t, port, {"Refute.lean": wit, "ReservesDonate.lean": ut})
    candidate, label = verified_candidate(t, out)
    on_proved = lean_check(t, candidate, {"ReservesDonate.lean": ut})
    lean_report = {
        "kernel_refutation": {"file": f"realworld/tasks/{t.id}/witnesses/buggy_original.lean",
                              "checked": on_port["Refute.lean"][0], "output_tail": on_port["Refute.lean"][1]},
        "repo_unit_tests_on_port": {"file": f"realworld/tasks/{t.id}/unit-tests/ReservesDonate.lean",
                                    "passed": on_port["ReservesDonate.lean"][0], "output_tail": on_port["ReservesDonate.lean"][1]},
        "repo_unit_tests_on_proved": {"candidate": label, "passed": on_proved["ReservesDonate.lean"][0],
                                      "output_tail": on_proved["ReservesDonate.lean"][1]},
    }
    print(f"[euler] kernel refutation of the port: {lean_report['kernel_refutation']['checked']}; "
          f"Euler's donate unit tests in Lean: port {lean_report['repo_unit_tests_on_port']['passed']}, "
          f"proved {lean_report['repo_unit_tests_on_proved']['passed']}", flush=True)

    # 2. The proved component on the same sequences.
    ref_outs, ref_sha, ref_tree = reference_outputs(t, candidate, [to_model_case(c) for c in cases])
    print(f"[euler] proved component: {label}, executable {ref_sha[:16]}", flush=True)

    # 3. Real contracts.
    src = source()
    report = {"spec_task": t.id, "project": t.meta["source"]["project"], "repository": t.meta["source"]["repository"],
              "license": t.meta["source"]["license"], "function": t.meta["source"]["function"],
              "references": t.meta["source"]["references"], "archive": ARCHIVE, "blobs": BLOBS,
              "forge_version": sh(["forge", "--version"]).stdout.strip().splitlines()[0],
              "solc": "0.8.10, optimizer on, 1000000 runs (hardhat.config.js at the commit)",
              "lean": lean_report,
              "proved": {"candidate": label, "executable_sha256": ref_sha, "solution_tree_sha256": ref_tree},
              "versions": {}}
    for v in VARIANTS:
        wd, et_sha = workdir(src, v)
        t0 = time.monotonic()
        real = []
        for k in range(0, len(cases), 250):
            real += run_forge(wd, cases[k:k + 250])
        vd = d / v["tag"]
        vd.mkdir(parents=True, exist_ok=True)
        (vd / "outputs.jsonl").write_text("".join(json.dumps(r) + "\n" for r in real))
        rep = {"tag": v["tag"], "commit": v["commit"], "status": v["status"], "note": v["note"],
               "etoken_sol_sha256": et_sha, "sequences": len(cases), "outputs": len(real),
               "elapsed_s": round(time.monotonic() - t0, 1),
               "violating_sequences": 0, "euler_liquidity_violations": 0, "by_requirement": {},
               "same_as_proved": 0, "differs_from_proved": 0, "noop_successes": 0,
               "documented": [], "witnesses": [], "differences": []}
        seen = set()
        for i, (c, r, p) in enumerate(zip(cases, real, ref_outs)):
            viol, ev, noops, diff = classify(c, r, p)
            rep["noop_successes"] += noops
            if diff is None:
                rep["same_as_proved"] += 1
            else:
                rep["differs_from_proved"] += 1
                if len(rep["differences"]) < 10:
                    rep["differences"].append({"case": i, **diff})
            if viol:
                rep["violating_sequences"] += 1
            if ev:
                rep["euler_liquidity_violations"] += 1
            for rid in {x["requirement"] for x in viol}:
                rep["by_requirement"][rid] = rep["by_requirement"].get(rid, 0) + 1
            if i < len(documented):
                last = normalize(r["steps"][-1])
                rep["documented"].append({"case": i, "label": c["label"], "ok": [s["ok"] for s in r["steps"]],
                                          "final": last, "repay": [s["repay"] for s in r["steps"]],
                                          "euler_liquidity_after": r["steps"][-1]["liq"],
                                          "violations": viol[:6], "euler_liquidity_violations": ev[:6]})
            for x in viol:
                if x["requirement"] == "REQ-NO-BAD-DEBT" and (i < len(documented) or "bad" not in seen):
                    rep["witnesses"].append({"case": i, "documented": i < len(documented), **x,
                                             "lean_goal": f"¬ Healthy ⟨{x['e']}, {x['d']}⟩"})
                    if i >= len(documented):
                        seen.add("bad")
                    break
        for k, rt in enumerate(REPO_TESTS):
            got = rep["documented"][1 + k]
            ex = rt["expect"]
            got["expected"] = ex
            got["matches_repo_test"] = (got["ok"] == ex["ok"] and got["final"]["acct"][0] == ex["acct0"]
                                        and got["final"]["reserves"] == ex["reserves"] and got["final"]["cash"] == ex["cash"])
        report["versions"][v["tag"]] = rep
        print(f"[euler] {v['tag']}: {rep['violating_sequences']} violating sequences, "
              f"{rep['euler_liquidity_violations']} with Euler's own collateral < liability, "
              f"{rep['same_as_proved']} same as proved, {rep['differs_from_proved']} differ; {rep['by_requirement']}",
              flush=True)

    # 4. Lean confirmation of the real-code solvency witnesses.
    items = [(tag, w) for tag, rep in report["versions"].items() for w in rep["witnesses"]]
    lines = ["import EulerLending.Spec", "open EulerLending", ""]
    for tag, w in items:
        lines += [f"-- {tag} case {w['case']} step {w['step']}: {w['message']}",
                  f"example : {w['lean_goal']} := by decide", ""]
    text = "\n".join(lines) + "\n"
    (d / "Confirm.lean").write_text(text)
    ok, tail = lean_check(t, candidate, {"Confirm.lean": text})["Confirm.lean"] if items else (True, "")
    for _, w in items:
        w["confirmed_in_lean"] = ok
    report["lean_confirmation"] = {"file": "real-code/Confirm.lean", "goals": len(items), "checked": ok,
                                   "output_tail": tail}
    report["generated"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    report["image_id"] = judge.image_id()
    report["cases"] = a.cases
    report["seed"] = a.seed
    (d / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"wrote {d / 'report.json'}")


if __name__ == "__main__":
    main()
