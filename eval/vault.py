#!/usr/bin/env python3
"""Hundred Finance share vault: the deployed hToken code against the proved component.

For realworld/tasks/rw-hundred-vault this script:
  1. port       kernel-checks the refutations of the Lean port of the hToken share accounting
                (witnesses/hundred_attack.lean: the first round of the April 2023 attack;
                witnesses/zero_share_withdraw.lean: a withdrawal by an actor with no shares)
                and the Compound-style unit tests on the port (tests/PortUnitTests.lean);
  2. reference  builds the executable from a judge-accepted candidate (an accepted Muse repair
                when one exists, otherwise the build-team reference);
  3. real code  forks Optimism at block 90761917, the last block before the attack, empties the
                hWBTC market the way the attacker did (the only holder redeems every share), has
                the admin withdraw the reserves (377 satoshi; the model has none), and runs every
                operation sequence on the deployed market through
                realworld/adapters/hundred (forge); the same sequences run on the proved
                executable and on the port, from the same starting state;
  4. compare    checks every real output against the task's requirements (the oracle mirrors
                Spec.lean), compares the real outputs with the port's step by step, and states
                each violation found in the real code as a `decide` goal over the Lean
                definitions, checked in the kernel.

What is proved: the Lean component accepted by the judge meets every requirement for every
sequence. What is tested: the deployed contract, sequence by sequence, against the same
requirements and against the port. The deployed contract is not proved.

Needs Docker, git, forge, and an Optimism RPC endpoint that serves archive state at block
90761917 (PF_OP_RPC, default https://mainnet.optimism.io). forge-std is fetched at a pinned
commit into PF_REALWORLD_CACHE (default ~/.cache/proofforge-realworld).

Usage: vault.py [--cases 500] [--seed 0] [--out results/vault-1]
"""
import argparse, json, os, pathlib, random, shutil, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import binary_check, judge, task as taskmod  # noqa: E402

TASK = ROOT / "realworld" / "tasks" / "rw-hundred-vault"
ADAPTER = ROOT / "realworld" / "adapters" / "hundred"
CACHE = pathlib.Path(os.environ.get("PF_REALWORLD_CACHE", pathlib.Path.home() / ".cache" / "proofforge-realworld"))
RPC = os.environ.get("PF_OP_RPC", "https://mainnet.optimism.io")
FORGE_STD = ("https://github.com/foundry-rs/forge-std", "v1.11.0", "8e40513d678f392f398620b3ef2b418648b33e89")
KIND = {"deposit": 0, "redeem": 1, "withdraw": 2, "donate": 3}
ACTORS = 4


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


# Cases: sequences from the emptied market, actors 0 to 3.

def gen_cases(t, n, seed):
    rng = random.Random(seed)
    out = []
    while len(out) < n:
        c = t.oracle._attack(rng) if rng.random() < 0.4 else t.oracle._walk(rng)
        if all(op.get("who", 0) < ACTORS for op in c["ops"]):
            out.append(c)
    return out


def encode(case):
    f = [str(len(case["ops"]))]
    for op in case["ops"]:
        f += [str(KIND[op["op"]]), str(op.get("who", 0)), str(op.get("amount", op.get("shares", 0)))]
    return " ".join(f)


# The deployed market.

def forge_project():
    d = CACHE / "hundred-forge"
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


def run_real(cases):
    d = forge_project()
    (d / "io" / "cases.txt").write_text("".join(encode(c) + "\n" for c in cases))
    if (d / "io" / "out.txt").exists():
        (d / "io" / "out.txt").unlink()
    r = sh(["forge", "test", "--match-test", "test_replay"], cwd=d, env={**os.environ, "PF_OP_RPC": RPC}, timeout=7200)
    if "[PASS]" not in r.stdout:
        raise RuntimeError(r.stdout[-3000:] + r.stderr[-3000:])
    lines = (d / "io" / "out.txt").read_text().splitlines()
    head = lines[0].split()
    start = {"assets": int(head[1]), "supply": int(head[2]), "cash": int(head[4]), "reserves_withdrawn": int(head[6])}
    outs, cur = [], []
    for line in lines[1:]:
        if line == "end":
            outs.append({"steps": cur})
            cur = []
            continue
        f = [int(x) for x in line.split()]
        cur.append({"ok": f[0] == 1, "assets": f[1], "supply": f[2], "balances": f[3:3 + ACTORS]})
    forge = sh(["forge", "--version"]).stdout.splitlines()[0]
    return start, outs, forge


# Lean executables built from candidates.

def lean_outputs(t, candidate, cases, need_accept):
    j = judge.judge(str(candidate), task=t) if need_accept else None
    if need_accept and not j["accepted"]:
        raise RuntimeError(f"{candidate} is not accepted by the judge")
    ws = judge.load_workspace(str(candidate))
    project = judge.fresh_project(ws, judge.candidate_files(ws), t)
    b = binary_check.build(project, t)
    if b["exit_code"]:
        raise RuntimeError(b["output_tail"])
    sha = (project / "binary.sha256").read_text().strip()
    outs = binary_check.run_cases(project, t.exe, cases, "vault")
    shutil.rmtree(project, ignore_errors=True)
    return outs, sha, (j or {}).get("solution_tree_sha256")


def lean_check(t, candidate, files):
    """Build `candidate` in a fresh project and check each Lean file in `files` ({name: text})."""
    ws = judge.load_workspace(str(candidate))
    project = judge.fresh_project(ws, judge.candidate_files(ws), t)
    for name, text in files.items():
        (project / name).write_text(text)
    script = "lake build Solution >/tmp/b.log 2>&1 || { tail -20 /tmp/b.log; exit 3; }; " + "; ".join(
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


# Lean statements of real-code violations.

def lean_goal(case, steps, start, rid):
    """A decidable statement over Spec.lean that holds exactly when the real steps break `rid`
    at the first step that breaks it (None when the requirement is not stated per step here)."""
    states = [start] + steps
    for i, op in enumerate(case["ops"]):
        p, q = states[i], states[i + 1]
        A, S = p["assets"], p["supply"]
        if rid == "REQ-WITHDRAW-ROUNDS-UP" and op["op"] == "withdraw" and q["ok"]:
            x, tb = op["amount"], S - q["supply"]
            if not (S > 0 and x * S <= tb * A and tb * A < x * S + A):
                return f"¬ (0 < {S} ∧ {x} * {S} ≤ {tb} * {A} ∧ {tb} * {A} < {x} * {S} + {A})", i
        if rid == "REQ-DEPOSIT-ROUNDS-DOWN" and op["op"] == "deposit" and q["ok"] and S > 0:
            x, tm = op["amount"], q["supply"] - S
            if not (tm * A <= x * S < (tm + 1) * A):
                return f"¬ ({tm} * {A} ≤ {x} * {S} ∧ {x} * {S} < ({tm} + 1) * {A})", i
        if rid == "REQ-REDEEM-ROUNDS-DOWN" and op["op"] == "redeem" and q["ok"] and S > 0:
            tr, y = op["shares"], A - q["assets"]
            if not (y * S <= tr * A < (y + 1) * S):
                return f"¬ ({y} * {S} ≤ {tr} * {A} ∧ {tr} * {A} < ({y} + 1) * {S})", i
    if rid == "REQ-SHARE-VALUE":
        for i in range(len(states)):
            for j in range(i + 1, len(states)):
                if all(states[k]["supply"] > 0 for k in range(i, j + 1)):
                    a, c = states[i], states[j]
                    if a["assets"] * c["supply"] > c["assets"] * a["supply"]:
                        v = lambda s: f"⟨{s['assets']}, {s['supply']}, fun _ => 0⟩"
                        return f"¬ ValueNotBelow {v(a)} {v(c)}", j - 1
    return None, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=500)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default="results/vault-1")
    a = ap.parse_args()
    out = (ROOT / a.out).resolve()
    d = out / "real-code"
    d.mkdir(parents=True, exist_ok=True)
    t = taskmod.load(TASK)
    t0 = time.monotonic()

    # 1. The port: kernel refutation and unit tests.
    port = TASK / "attacks" / "hundred_port.lean"
    res = lean_check(t, port, {"Refute.lean": (TASK / "witnesses" / "hundred_attack.lean").read_text(),
                               "ZeroShares.lean": (TASK / "witnesses" / "zero_share_withdraw.lean").read_text(),
                               "UnitTests.lean": (TASK / "tests" / "PortUnitTests.lean").read_text()})
    ref_unit = lean_check(t, TASK / "reference" / "SolutionA.lean",
                          {"UnitTests.lean": (TASK / "tests" / "PortUnitTests.lean").read_text()})
    print(f"port refutations {'checked' if res['Refute.lean'][0] and res['ZeroShares.lean'][0] else 'FAILED'}, "
          f"unit tests on the port {'pass' if res['UnitTests.lean'][0] else 'FAIL'}", flush=True)

    # 2 and 3. Cases on the real market, the proved executable and the port.
    documented = [dict(t.oracle.FLAGSHIP)]
    cases = documented + gen_cases(t, a.cases, a.seed)
    start, real, forge = run_real(cases)
    print(f"real market emptied: assets {start['assets']} (cash {start['cash']}, reserves withdrawn {start['reserves_withdrawn']}), "
          f"supply {start['supply']}; {len(real)} cases run", flush=True)
    st = {"assets": start["assets"], "supply": start["supply"], "balances": [0] * ACTORS}
    lean_cases = [dict(c, start=st) for c in cases]
    candidate, label = verified_candidate(t, out)
    ref_outs, ref_sha, ref_tree = lean_outputs(t, candidate, lean_cases, True)
    port_outs, port_sha, _ = lean_outputs(t, port, lean_cases, False)
    (d / "cases.jsonl").write_text("".join(json.dumps(c) + "\n" for c in lean_cases))
    (d / "real-outputs.jsonl").write_text("".join(json.dumps(o) + "\n" for o in real))
    (d / "proved-outputs.jsonl").write_text("".join(json.dumps(o) + "\n" for o in ref_outs))
    (d / "port-outputs.jsonl").write_text("".join(json.dumps(o) + "\n" for o in port_outs))

    # 4. Compare and check.
    rep = {"cases": len(cases), "documented": len(documented), "real_same_as_port": 0, "real_differs_from_port": [],
           "real_same_as_proved": 0, "violating_cases": 0, "by_requirement": {}, "witnesses": [],
           "proved_violations": 0}
    seen = set()
    for i, (c, lc, r, p, q) in enumerate(zip(cases, lean_cases, real, port_outs, ref_outs)):
        if r["steps"] == p.get("steps"):
            rep["real_same_as_port"] += 1
        elif len(rep["real_differs_from_port"]) < 20:
            rep["real_differs_from_port"].append({"case": i, "input": c, "real": r, "port": p})
        if r["steps"] == q.get("steps"):
            rep["real_same_as_proved"] += 1
        if t.oracle.check(lc, q):
            rep["proved_violations"] += 1
        viol = t.oracle.violations(lc, r["steps"])
        if not viol:
            continue
        rep["violating_cases"] += 1
        for rid, msg in viol:
            rep["by_requirement"][rid] = rep["by_requirement"].get(rid, 0) + 1
            if i < len(documented) or rid not in seen:
                g, step = lean_goal(c, r["steps"], st, rid)
                rep["witnesses"].append({"case": i, "documented": i < len(documented), "requirement": rid,
                                         "message": msg, "input": c, "real_steps": r["steps"],
                                         "proved_steps": q.get("steps"), "lean_goal": g, "step": step})
                if i >= len(documented):
                    seen.add(rid)
    items = [w for w in rep["witnesses"] if w["lean_goal"]]
    text = "import ShareVault.Spec\nopen ShareVault\n\n" + "".join(
        f"-- case {w['case']}, step {w['step']}, {w['requirement']}: {w['message']}\nexample : {w['lean_goal']} := by decide\n\n"
        for w in items)
    (d / "Confirm.lean").write_text(text)
    ok, tail = lean_check(t, candidate, {"Confirm.lean": text})["Confirm.lean"] if items else (True, "")
    for w in items:
        w["confirmed_in_lean"] = ok
    report = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "elapsed_s": round(time.monotonic() - t0, 1),
        "task": t.id, "source": t.meta["source"], "rpc": RPC, "fork_block": 90761917, "forge": forge,
        "forge_std": {"repository": FORGE_STD[0], "tag": FORGE_STD[1], "commit": FORGE_STD[2]},
        "image": judge.IMAGE, "image_id": judge.image_id(), "seed": a.seed,
        "real_start": start,
        "port": {"candidate": "realworld/tasks/rw-hundred-vault/attacks/hundred_port.lean", "executable_sha256": port_sha,
                 "kernel_refutation": "realworld/tasks/rw-hundred-vault/witnesses/hundred_attack.lean",
                 "kernel_refutation_checked": res["Refute.lean"][0], "refutation_output_tail": res["Refute.lean"][1],
                 "zero_share_refutation": "realworld/tasks/rw-hundred-vault/witnesses/zero_share_withdraw.lean",
                 "zero_share_refutation_checked": res["ZeroShares.lean"][0],
                 "zero_share_output_tail": res["ZeroShares.lean"][1],
                 "unit_tests": "realworld/tasks/rw-hundred-vault/tests/PortUnitTests.lean",
                 "unit_tests_pass": res["UnitTests.lean"][0], "unit_tests_output_tail": res["UnitTests.lean"][1],
                 "unit_tests_on_reference": ref_unit["UnitTests.lean"][0],
                 "unit_tests_on_reference_output_tail": ref_unit["UnitTests.lean"][1]},
        "proved": {"candidate": label, "executable_sha256": ref_sha, "solution_tree_sha256": ref_tree},
        "comparison": rep,
        "lean_confirmation": {"file": "real-code/Confirm.lean", "goals": len(items), "checked": len(items) if ok else 0,
                              "output_tail": tail},
    }
    (d / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"real code: {rep['violating_cases']} of {len(cases)} cases violate the requirements {rep['by_requirement']}; "
          f"{rep['real_same_as_port']} identical to the port, {rep['real_same_as_proved']} identical to the proved "
          f"component; proved component violations {rep['proved_violations']}; Lean goals checked "
          f"{report['lean_confirmation']['checked']} of {len(items)}", flush=True)
    print(f"wrote {d / 'report.json'}")


if __name__ == "__main__":
    main()
