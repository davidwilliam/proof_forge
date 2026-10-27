#!/usr/bin/env python3
"""Build a task's executable from a candidate in a fresh container, then run
requirement-derived property tests against the binary using the task's oracle.

Round 1 runs the oracle's FLAGSHIP case (if any) plus N generated cases. Round 2 runs the
cases the oracle derives from round-1 results (for example resubmissions).

Usage: binary_check.py <workspace-dir | candidate.lean> [--task T] [--cases N] [--seed S] [--json out]
"""
import argparse, json, pathlib, random, shutil, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import judge, task as taskmod  # noqa: E402


def run_cases(project, exe, cases, name):
    (project / f"{name}.jsonl").write_text("\n".join(json.dumps(c) for c in cases) + "\n")
    r = judge.in_container(project, f".lake/build/bin/{exe} < {name}.jsonl > {name}.out")
    if r["exit_code"] not in (0, 2) or not (project / f"{name}.out").exists():
        return []
    return [json.loads(l) for l in (project / f"{name}.out").read_text().splitlines()]


def check_binary(arg, n_cases=2000, seed=0, task=None):
    t0 = time.monotonic()
    task = task or taskmod.load()
    oracle = task.oracle
    ws = judge.load_workspace(arg)
    files = judge.candidate_files(ws)
    project = judge.fresh_project(ws, files, task)
    rng = random.Random(seed)
    flagship = getattr(oracle, "FLAGSHIP", None)
    cases = ([flagship] if flagship else []) + [oracle.gen_case(rng) for _ in range(n_cases)]
    build = judge.in_container(project,
        f"lake build {task.exe} >/tmp/build.log 2>&1 || {{ tail -20 /tmp/build.log; exit 3; }}; "
        f"sha256sum .lake/build/bin/{task.exe} | cut -d' ' -f1 > binary.sha256")
    result = {"task": task.id, "candidate": str(arg),
              "build": {k: build[k] for k in ("exit_code", "elapsed_ms")},
              "cases": len(cases), "violations": {}, "witnesses": []}
    if build["exit_code"] != 0:
        result["build"]["output_tail"] = build["output_tail"]
        result["status"] = "BUILD_FAILED"
        shutil.rmtree(project, ignore_errors=True)
        return result
    result["binary_sha256"] = (project / "binary.sha256").read_text().strip()

    def record(rid, msg, case, out):
        result["violations"][rid] = result["violations"].get(rid, 0) + 1
        if len(result["witnesses"]) < 6:
            result["witnesses"].append({"requirement": rid, "message": msg, "input": case, "output": out})

    outs = run_cases(project, task.exe, cases, "round1")
    if len(outs) != len(cases):
        record("WRAPPER", f"binary produced {len(outs)} results for {len(cases)} inputs", cases[0], {})
    follow = []
    for c, o in zip(cases, outs):
        for rid, msg in oracle.check(c, o):
            record(rid, msg, c, o)
        nxt = oracle.followup(c, o) if hasattr(oracle, "followup") else None
        if nxt:
            follow.append(nxt)
    if follow:
        outs2 = run_cases(project, task.exe, [c for c, _ in follow], "round2")
        for (c, rid), o in zip(follow, outs2):
            for _, msg in oracle.check(c, o):
                record(rid, f"follow-up case: {msg}", c, o)
    result["followup_cases"] = len(follow)
    if flagship and outs:
        result["flagship_output"] = outs[0]
        if hasattr(oracle, "describe"):
            result["flagship"] = oracle.describe(outs[0])
    result["status"] = "PASS" if not result["violations"] else "REFUTED"
    result["elapsed_ms"] = int((time.monotonic() - t0) * 1000)
    shutil.rmtree(project, ignore_errors=True)
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("candidate")
    ap.add_argument("--task")
    ap.add_argument("--cases", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--json")
    a = ap.parse_args()
    r = check_binary(a.candidate, a.cases, a.seed, taskmod.load(a.task))
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(r, indent=2) + "\n")
    print(f"{r['status']}  {a.candidate}  cases={r['cases']}+{r.get('followup_cases', 0)}  "
          f"violations={r['violations']}  flagship={r.get('flagship', '-')}")
    sys.exit(0 if r["status"] == "PASS" else 1)
