#!/usr/bin/env python3
"""Real-world bugs: money routines from open-source projects, checked against proved
components.

For every task under realworld/tasks (one per project: Spliit, go-money, moneyphp), and for
RubyMoney (real code only, checked against the Allocation requirements), this script:
  1. ports      reports the judge and binary verdicts of the Lean ports of the buggy releases
                (from the task's validation.json) and checks each port's refutation in the
                Lean kernel (witnesses/<port>.lean: the documented input, `decide`);
  2. reference  builds the executable from a judge-accepted candidate (an accepted Muse
                repair when one exists, otherwise the build-team reference) and records it;
  3. real code  fetches the project at the exact commit of every listed release, runs its
                real routine unmodified through a small adapter (realworld/adapters) on the
                documented inputs plus generated inputs from the routine's own domain, runs
                the proved executable on the same inputs, and checks every real output
                against the task's requirements (the task oracle mirrors Spec.lean);
  4. confirm    states each violation found in the real code as a `decide` goal over the
                Lean `...On` predicates (or `Valid` for a refused valid input) and checks it
                in the Lean kernel.

What is proved: the Lean component accepted by the judge meets every requirement for every
input. What is tested: the real code, input by input, against the same requirements and
against the proved component's output. The real libraries are not proved.

The projects' sources are fetched at run time into PF_REALWORLD_CACHE (default
~/.cache/proofforge-realworld) and never copied into this repository. Needs git, Docker,
node and npm (Spliit), go (go-money), the pinned PHP image (moneyphp) and ruby (RubyMoney).

Usage: realworld.py [--cases 2000] [--seed 0] [--out results/realworld-1] [--only spliit,...]
"""
import argparse, json, os, pathlib, random, shutil, subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import binary_check, judge, task as taskmod  # noqa: E402

TASKS = ROOT / "realworld" / "tasks"
ADAPTERS = ROOT / "realworld" / "adapters"
CACHE = pathlib.Path(os.environ.get("PF_REALWORLD_CACHE", pathlib.Path.home() / ".cache" / "proofforge-realworld"))
PHP_IMAGE = "php@sha256:620a6b9f4d4feef2210026172570465e9d0c1de79766418d3affd09190a7fda5"   # php:7.4-cli
NODE_DEPS = ["typescript@5.9.3", "ts-pattern@5.9.0"]   # versions in Spliit's package-lock.json at both tags


# Each library's own input domain: the inputs its API accepts and its users pass.

def spliit_case(rng):
    """One expense: Spliit stores positive integer shares; amounts in cents, negative for income."""
    n = rng.randint(1, 10)
    rs = [1] * n if rng.random() < 0.4 else [rng.randint(1, 100) for _ in range(n)]
    k = rng.random()
    amount = rng.randint(-300, 300) if k < 0.4 else rng.randint(-10**6, 10**6) if k < 0.85 else rng.randint(-10**9, 10**9)
    return {"amount": amount, "ratios": rs}


def gomoney_case(rng):
    k = rng.random()
    amount = rng.randint(-12, 12) if k < 0.2 else rng.randint(-300, 300) if k < 0.5 else rng.randint(-10**6, 10**6) if k < 0.85 else rng.randint(-10**12, 10**12)
    return {"amount": amount, "n": rng.randint(1, 12)}


def moneyphp_case(rng):
    """Ratios are zero or positive integers, not all zero."""
    n = rng.randint(1, 8)
    k = rng.random()
    if k < 0.3:
        rs = [rng.randint(0, 10) for _ in range(n)]
    elif k < 0.6:
        rs = [rng.choice([0, 1, 2, 3, 25, 50, 75, 100]) for _ in range(n)]
    else:
        rs = [rng.randint(0, 10**4) for _ in range(n)]
    if sum(rs) == 0:
        rs[rng.randrange(n)] = rng.randint(1, 10)
    k = rng.random()
    amount = rng.randint(-300, 300) if k < 0.4 else rng.randint(-10**6, 10**6) if k < 0.85 else rng.randint(-10**9, 10**9)
    return {"amount": amount, "ratios": rs}


def rubymoney_case(rng):
    """Integer ratios, or decimal ratios (passed to the library as Floats) with 1 to 4 decimals."""
    n = rng.randint(1, 8)
    scale = 0 if rng.random() < 0.5 else rng.randint(1, 4)
    hi = 100 if scale == 0 else 10 ** (scale + 1)
    rs = [rng.randint(0, hi) for _ in range(n)]
    if sum(rs) == 0:
        rs[rng.randrange(n)] = rng.randint(1, hi)
    k = rng.random()
    amount = rng.randint(-300, 300) if k < 0.4 else rng.randint(-10**6, 10**6) if k < 0.85 else rng.randint(-10**9, 10**9)
    return {"amount": amount, "ratios": rs, "scale": scale}


RUBYMONEY = {
    "project": "RubyMoney/money", "repository": "https://github.com/RubyMoney/money", "license": "MIT",
    "function": "Money::Allocation.generate (lib/money/money/allocation.rb)",
    "buggy": [{"tag": "v6.18.0", "commit": "f5699476c629d291b943ebbe495561d287599ed4"}],
    "fixed": [{"tag": "v6.19.0", "commit": "faec0fbb7cb10646453c5ef6644289d83615b4fe"}],
    "references": ["https://github.com/RubyMoney/money/issues/1033", "https://github.com/RubyMoney/money/pull/1034"],
    "note": ("Real-code check only: no Lean port or repair. The documented bug (issue #1033) uses decimal "
             "ratios passed as Floats; the requirements read them as the exact decimals, scaled to integers."),
}

LIBS = {
    "spliit": {"task": "rw-spliit-balances", "runner": "node", "gen": spliit_case,
               "documented": [{"amount": 100, "ratios": [1, 1, 1]}]},
    "go-money": {"task": "rw-gomoney-split", "runner": "go", "gen": gomoney_case,
                 "documented": [{"amount": -101, "n": 4}, {"amount": -2, "n": 3}]},
    "moneyphp": {"task": "rw-moneyphp-allocate", "runner": "php", "gen": moneyphp_case,
                 "documented": [{"amount": 5, "ratios": [0, 7, 3]}, {"amount": 1, "ratios": [1, 1]},
                                {"amount": 9999, "ratios": [75, 25]}]},
    "rubymoney": {"task": "rw-moneyphp-allocate", "dir": "rubymoney", "source": RUBYMONEY, "runner": "ruby",
                  "gen": rubymoney_case,
                  "documented": [{"amount": 700273, "scale": 15,
                                  "ratios": [1181858314366100] * 7 + [1170126087450276] + [1000000000000000] * 4}]},
}


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


# Sources at pinned commits.

def checkout(repo_url, tag, commit):
    """Extract the tree of `commit` (which must be what `tag` points to) into the cache."""
    name = repo_url.rstrip("/").split("/")[-2] + "_" + repo_url.rstrip("/").split("/")[-1]
    repo = CACHE / "repos" / name
    if not repo.exists():
        repo.parent.mkdir(parents=True, exist_ok=True)
        r = sh(["git", "clone", "-q", "--filter=blob:none", "--no-checkout", repo_url, str(repo)])
        if r.returncode:
            raise RuntimeError(r.stderr)
    tagged = sh(["git", "-C", str(repo), "rev-parse", f"{tag}^{{commit}}"]).stdout.strip()
    if tagged != commit:
        raise RuntimeError(f"{repo_url} tag {tag} is {tagged}, expected {commit}")
    dest = CACHE / "checkouts" / f"{name}-{commit[:12]}"
    if not dest.exists():
        dest.parent.mkdir(parents=True, exist_ok=True)
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="pf-src-", dir=CACHE))
        archive = subprocess.run(["git", "-C", str(repo), "archive", commit], capture_output=True, check=True).stdout
        subprocess.run(["tar", "-x", "-C", str(tmp)], input=archive, check=True)
        tmp.rename(dest)
    return dest


# Adapters.

def node_modules():
    d = CACHE / "node"
    if not (d / "node_modules" / "ts-pattern").exists():
        d.mkdir(parents=True, exist_ok=True)
        (d / "package.json").write_text('{"private": true}\n')
        r = sh(["npm", "install", "--no-audit", "--no-fund", "--silent", *NODE_DEPS], cwd=d)
        if r.returncode:
            raise RuntimeError(r.stderr)
    return d / "node_modules"


def run_node(src, cases):
    env = {**os.environ, "NODE_PATH": str(node_modules())}
    r = sh(["node", str(ADAPTERS / "spliit/run.cjs"), str(src)], input=cases, env=env, timeout=900)
    return r.stdout, r.stderr


def run_go(src, cases):
    d = CACHE / "go" / src.name
    if not (d / "adapter").exists():
        d.mkdir(parents=True, exist_ok=True)
        shutil.copy(ADAPTERS / "gomoney/main.go", d / "main.go")
        (d / "go.mod").write_text((ADAPTERS / "gomoney/go.mod.in").read_text().replace("CHECKOUT", str(src)))
        env = {**os.environ, "GOFLAGS": "-mod=mod", "GOPROXY": "off", "GOWORK": "off", "GOSUMDB": "off",
               "GOTOOLCHAIN": "local"}
        r = sh(["go", "build", "-o", "adapter", "."], cwd=d, env=env)
        if r.returncode:
            raise RuntimeError(r.stderr)
    r = sh([str(d / "adapter")], input=cases, timeout=900)
    return r.stdout, r.stderr


def run_php(src, cases):
    r = sh(["docker", "run", "--rm", "-i", "--network", "none",
            "-v", f"{ADAPTERS / 'moneyphp'}:/adapter:ro", "-v", f"{src}:/src:ro",
            PHP_IMAGE, "php", "/adapter/run.php", "/src"], input=cases, timeout=900)
    return r.stdout, r.stderr


def run_ruby(src, cases):
    r = sh(["ruby", str(ADAPTERS / "rubymoney/run.rb"), str(src)], input=cases, timeout=900)
    return r.stdout, r.stderr


RUNNERS = {"node": run_node, "go": run_go, "php": run_php, "ruby": run_ruby}


# The proved component.

def verified_candidate(t, out):
    """An accepted Muse repair of this task if one exists, else the build-team reference."""
    for run in sorted((out / t.id).glob("repair-*")):
        p = run / "passport.json"
        if p.exists() and json.loads(p.read_text())["status"] == "VERIFIED":
            return run / "final.lean", f"Muse repair {run.name} (Passport {json.loads(p.read_text())['passport_sha256'][:16]})"
    return t.root / "reference" / "SolutionA.lean", "build-team reference (reference/SolutionA.lean)"


def reference_outputs(t, candidate, cases):
    """Judge the candidate, build its executable in a fresh container and run it on `cases`."""
    j = judge.judge(str(candidate), task=t)
    if not j["accepted"]:
        raise RuntimeError(f"{candidate} is not accepted by the judge")
    ws = judge.load_workspace(str(candidate))
    project = judge.fresh_project(ws, judge.candidate_files(ws), t)
    b = binary_check.build(project, t)
    if b["exit_code"]:
        raise RuntimeError(b["output_tail"])
    sha = (project / "binary.sha256").read_text().strip()
    outs = binary_check.run_cases(project, t.exe, cases, "reference")
    shutil.rmtree(project, ignore_errors=True)
    return outs, sha, j["solution_tree_sha256"]


# Lean confirmation.

def lean_int(x):
    return f"({x})" if x < 0 else str(x)


def lean_list(xs):
    return "[" + ", ".join(lean_int(x) for x in xs) + "]"


def goal(t, case, shares, rid):
    """A decidable Lean statement that holds exactly when the output breaks `rid`."""
    a = lean_int(case["amount"])
    if t.lib == "Allocation":
        rs = lean_list(case["ratios"])
        if shares is None:
            return f"Valid {a} {rs}" if rid == "REQ-VALID-SUCCEEDS" else None
        s = lean_list(shares)
        return {"REQ-INVALID-FAILS": f"¬ Valid {a} {rs}",
                "REQ-ONE-SHARE-EACH": f"¬ OneShareEachOn {rs} {s}",
                "REQ-CONSERVATION": f"¬ ConservesOn {a} {s}",
                "REQ-WITHIN-ONE-UNIT": f"¬ WithinOneUnitOn {a} {rs} {s}",
                "REQ-ZERO-RATIO": f"¬ ZeroRatioOn {rs} {s}",
                "REQ-SIGN": f"¬ SignOn {a} {s}",
                "REQ-LARGEST-REMAINDER": f"¬ LargestRemainderOn {a} {rs} {s}"}.get(rid)
    n = case["n"]
    if shares is None:
        return f"0 < {n}" if rid == "REQ-VALID-SUCCEEDS" else None
    s = lean_list(shares)
    return {"REQ-INVALID-FAILS": f"{n} = 0",
            "REQ-ONE-SHARE-EACH": f"¬ OneShareEachOn {n} {s}",
            "REQ-CONSERVATION": f"¬ ConservesOn {a} {s}",
            "REQ-WITHIN-ONE-UNIT": f"¬ WithinOneUnitOn {a} {n} {s}",
            "REQ-SIGN": f"¬ SignOn {a} {s}"}.get(rid)


def lean_check(t, candidate, files):
    """Build `candidate` in a fresh project, then check each Lean file in `files`
    ({name: text}) with `lake env lean`; returns {name: (ok, output tail)}."""
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


def confirm_file(t, items):
    """One `example` per witness; returns the file text and each example's line range."""
    lines = [f"import {t.lib}.Spec", f"open {t.lib}", ""]
    spans = []
    for it in items:
        start = len(lines) + 1
        lines += [f"-- {it['label']}", f"example : {it['goal']} := by decide", ""]
        spans.append((start, len(lines)))
    return "\n".join(lines) + "\n", spans


def failed_examples(output, name, spans):
    """Indices of examples with an error reported inside their line range."""
    bad = set()
    for line in output.splitlines():
        if line.startswith(f"{name}:") and "error" in line:
            try:
                n = int(line.split(":")[1])
            except ValueError:
                continue
            bad |= {k for k, (a, b) in enumerate(spans) if a <= n <= b}
    return bad


# Main loop.

def run_lib(name, cfg, a, out):
    t = taskmod.load(TASKS / cfg["task"])
    src_meta = cfg.get("source") or t.meta["source"]
    rng = random.Random(a.seed)
    cases = [dict(c) for c in cfg["documented"]] + [cfg["gen"](rng) for _ in range(a.cases)]
    d = out / cfg.get("dir", t.id)
    (d / "real-code").mkdir(parents=True, exist_ok=True)
    (d / "real-code" / "cases.jsonl").write_text("".join(json.dumps(c) + "\n" for c in cases))
    print(f"[{name}] {len(cases)} inputs ({len(cfg['documented'])} documented)", flush=True)

    candidate, label = verified_candidate(t, out)
    ref_outs, ref_sha, ref_tree = reference_outputs(t, candidate, cases)
    ref = {"candidate": label, "executable_sha256": ref_sha, "solution_tree_sha256": ref_tree}
    print(f"[{name}] proved reference: {label}, executable {ref_sha[:16]}", flush=True)

    versions = [dict(v, status="buggy") for v in src_meta["buggy"]] + [dict(v, status="fixed") for v in src_meta["fixed"]]
    lib_report = {"spec_task": t.id, "note": src_meta.get("note"), "project": src_meta["project"], "repository": src_meta["repository"],
                  "license": src_meta["license"], "function": src_meta["function"],
                  "references": src_meta["references"], "reference": ref, "versions": {}}
    for v in versions:
        src = checkout(src_meta["repository"], v["tag"], v["commit"])
        stdout, stderr = RUNNERS[cfg["runner"]](src, "".join(json.dumps(c) + "\n" for c in cases))
        outs = [json.loads(l) for l in stdout.splitlines() if l.strip()]
        vd = d / "real-code" / v["tag"]
        vd.mkdir(parents=True, exist_ok=True)
        (vd / "outputs.jsonl").write_text(stdout)
        if stderr.strip():
            (vd / "stderr.txt").write_text(stderr[-20000:])
        rep = {"tag": v["tag"], "commit": v["commit"], "status": v["status"], "cases": len(cases),
               "outputs": len(outs), "same_as_proved": 0, "differs_but_meets_requirements": 0,
               "violating_cases": 0, "failures_on_valid_input": 0, "by_requirement": {}, "witnesses": []}
        ndoc, seen = len(cfg["documented"]), set()
        for i, (c, o, r) in enumerate(zip(cases, outs, ref_outs)):
            shares = o.get("shares")
            viol = t.oracle.violations(c["amount"], c.get("ratios", c.get("n")), shares)
            if not viol:
                if shares == r.get("shares"):
                    rep["same_as_proved"] += 1
                else:
                    rep["differs_but_meets_requirements"] += 1
                continue
            rep["violating_cases"] += 1
            if shares is None:
                rep["failures_on_valid_input"] += 1
            for rid, msg in viol:
                rep["by_requirement"][rid] = rep["by_requirement"].get(rid, 0) + 1
                if i < ndoc or rid not in seen:     # every documented case, first generated one per requirement
                    rep["witnesses"].append({"case": i, "documented": i < ndoc, "requirement": rid,
                                             "message": msg, "input": c, "output": o,
                                             "proved_output": r.get("shares"),
                                             "lean_goal": goal(t, c, shares, rid)})
                    if i >= ndoc:
                        seen.add(rid)
        if len(outs) != len(cases):
            rep["adapter_problem"] = f"{len(outs)} outputs for {len(cases)} inputs"
        lib_report["versions"][v["tag"]] = rep
        print(f"[{name}] {v['tag']} ({v['status']}): {rep['violating_cases']} violating, "
              f"{rep['same_as_proved']} same as proved, {rep['differs_but_meets_requirements']} differ but meet "
              f"the requirements; {rep['by_requirement']}", flush=True)

    # Confirm every recorded witness in the Lean kernel.
    items = [{"label": f"{tag} case {w['case']}, {w['requirement']}: {w['message']}", "goal": w["lean_goal"], "w": w}
             for tag, rep in lib_report["versions"].items() for w in rep["witnesses"] if w["lean_goal"]]
    text, spans = confirm_file(t, items)
    (d / "real-code" / "Confirm.lean").write_text(text)
    ok, tail = lean_check(t, candidate, {"Confirm.lean": text})["Confirm.lean"] if items else (True, "")
    bad = failed_examples(tail, "Confirm.lean", spans) if not ok else set()
    if not ok and not bad:
        bad = set(range(len(items)))        # the file failed as a whole
    for k, it in enumerate(items):
        it["w"]["confirmed_in_lean"] = k not in bad
    lib_report["lean_confirmation"] = {"file": "real-code/Confirm.lean", "goals": len(items),
                                       "checked": len(items) - len(bad), "output_tail": tail}

    if "source" in cfg:      # real-code check only: the task belongs to another project
        (d / "real-code" / "report.json").write_text(json.dumps(lib_report, indent=2) + "\n")
        return lib_report
    # Ports: verdicts from validation.json and kernel refutations.
    val = json.loads((t.root / "validation.json").read_text())
    ports = {}
    for port in sorted((t.root / "witnesses").glob("*.lean")):
        att = val["checks"]["attacks"].get(f"{port.stem}.lean", {})
        res = lean_check(t, t.root / "attacks" / f"{port.stem}.lean", {"Refute.lean": port.read_text()})["Refute.lean"]
        ports[port.stem] = {"note": att.get("expected", {}).get("note"), "judge": att.get("judge"),
                            "judge_reasons": att.get("judge_reasons"), "binary": att.get("binary"),
                            "violations": att.get("violations"), "witness": att.get("witness"),
                            "kernel_refutation": f"realworld/tasks/{t.id}/witnesses/{port.name}",
                            "kernel_refutation_checked": res[0], "lean_output_tail": res[1]}
        print(f"[{name}] port {port.stem}: judge {att.get('judge')}, binary {att.get('binary')}, "
              f"kernel refutation {'checked' if res[0] else 'FAILED'}", flush=True)
    lib_report["ports"] = ports
    lib_report["validation"] = {"passed": val.get("passed"),
                                "references": {k: {"judge": x["judge"], "binary": x["binary"]}
                                               for k, x in val["checks"]["references"].items()}}
    (d / "real-code" / "report.json").write_text(json.dumps(lib_report, indent=2) + "\n")
    return lib_report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default="results/realworld-1")
    ap.add_argument("--only", help="comma-separated: " + ",".join(LIBS))
    a = ap.parse_args()
    out = (ROOT / a.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    names = a.only.split(",") if a.only else list(LIBS)
    summary_path = out / "summary.json"
    summary = json.loads(summary_path.read_text()) if summary_path.exists() else {"projects": {}}
    summary.update({"generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "image": judge.IMAGE,
                    "image_id": judge.image_id(), "cases": a.cases, "seed": a.seed,
                    "php_image": PHP_IMAGE, "node_deps": NODE_DEPS,
                    "go_version": sh(["go", "version"]).stdout.strip(),
                    "node_version": sh(["node", "--version"]).stdout.strip(),
                    "ruby_version": sh(["ruby", "--version"]).stdout.strip()})
    for name in names:
        summary["projects"][name] = run_lib(name, LIBS[name], a, out)
        summary_path.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"wrote {summary_path}")


if __name__ == "__main__":
    main()
