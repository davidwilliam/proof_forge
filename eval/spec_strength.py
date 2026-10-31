#!/usr/bin/env python3
"""Specification strength gate over the flagship, real-world and benchmark specifications.

Runs harness/spec_strength.py on one task per locked specification: the payout flagship, every
real-world task, and the first variant of each benchmark base specification (variants share the
locked files, the reference solutions and the oracle, so their mutants and verdicts are the same;
payouts-flagship-b2 and -b3 share the payout flagship's). Writes, under
results/spec-strength-1/<task id>/, `report.json` (with its content hash) and `report.md`, and
results/spec-strength-1/summary.json and table.md. An existing report.json is kept unless --force.

Tasks run in at most `--jobs` worker threads (default 2); each task's containers run one at a
time, and harness/spec_strength.py bounds this process to two containers at once.

Usage: eval/spec_strength.py [--only ID[,ID...]] [--jobs N] [--force] [--table-only]
                             [--max-mutants N] [--extended-cases N]
"""
import argparse, concurrent.futures, json, pathlib, sys, threading, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import spec_strength as ss, task as taskmod  # noqa: E402

OUT = ROOT / "results" / "spec-strength-1"
FLAGSHIPS = ["payout-flagship", "rw-cetus-shlw", "rw-euler-donate", "rw-hundred-vault", "rw-balancer-upscale",
             "rw-compound-comp", "rc-knight-router"]
REALWORLD = ["rw-gomoney-split", "rw-moneyphp-allocate", "rw-spliit-balances"]
SHARED = {"payouts-flagship-b2": "payout-flagship", "payouts-flagship-b3": "payout-flagship"}


def benchmark_bases():
    """The first variant of each base specification under tasks/, except the payout flagship's."""
    seen, out = set(), []
    for d in sorted(taskmod.TASKS.iterdir()):
        if not (d / "task.json").exists() or d.name in SHARED:
            continue
        base = d.name.rsplit("-", 1)[0]
        if base not in seen:
            seen.add(base)
            out.append(d.name)
    return out


def targets():
    return FLAGSHIPS + REALWORLD + benchmark_bases()


def variants(task_id):
    """Task ids that share `task_id`'s locked specification."""
    if task_id == "payout-flagship":
        return sorted(SHARED)
    base = task_id.rsplit("-", 1)[0]
    return [d.name for d in sorted(taskmod.TASKS.glob(f"{base}-b*")) if d.name != task_id] if task_id.endswith("-b1") else []


def row(rep):
    s, tid = rep["summary"], rep["task"]["id"]
    if not rep.get("supported"):
        return f"| `{tid}` | not measured: baseline {rep['baseline'].get('status')} | | | | | | | | |"
    kernel_reqs = sum(1 for v in rep["vacuity"] if v["not_trivially_true"] == "kernel-checked")
    tested_reqs = sum(1 for v in rep["vacuity"] if v["not_trivially_true"] != "not shown")
    return (f"| `{tid}` | {s['generated']} | {s['compiled']} | {s['equivalent']} | "
            f"{s['killed'] - s['killed_kernel_only']} | {s['killed_kernel_only']} | {s['killed_kernel']} | "
            f"{s['survived_differs']} | {s['survived_same']} | {s['kill_ratio']} | "
            f"{tested_reqs} / {kernel_reqs} of {len(rep['vacuity'])} |")


HEADER = ("| Task | Mutants | Compiled | Equivalent (identical executable) | Killed by property tests | "
          "Killed by kernel only | Killed with kernel-checked counterexample | Survived, behaviour differs | "
          "Survived, no observed difference | Killed of non-equivalent | Requirements violated / kernel-refuted |\n"
          "|---|---|---|---|---|---|---|---|---|---|---|")


def table(reports):
    lines = [HEADER] + [row(r) for r in reports]
    tot = {k: sum(r["summary"].get(k, 0) for r in reports if r.get("supported"))
           for k in ("generated", "compiled", "equivalent", "killed", "killed_kernel_only", "killed_kernel",
                     "survived_differs", "survived_same")}
    nonequiv = tot["compiled"] - tot["equivalent"]
    lines.append(f"| total | {tot['generated']} | {tot['compiled']} | {tot['equivalent']} | "
                 f"{tot['killed'] - tot['killed_kernel_only']} | {tot['killed_kernel_only']} | {tot['killed_kernel']} | "
                 f"{tot['survived_differs']} | {tot['survived_same']} | {tot['killed']} of {nonequiv} | |")
    return "\n".join(lines) + "\n", tot


def survivors_md(reports):
    out = []
    for r in reports:
        for m in r.get("mutants") or []:
            if m["status"] == "survived_differs":
                f = m.get("first_difference") or {}
                out.append(f"- `{r['task']['id']}` {m['id']} ({m['operator']}, `{m['decl']}` line {m['line']}): "
                           f"{m['description']}; outputs differ on {m.get('differing_cases', 0)} cases, first input "
                           f"`{json.dumps(f.get('input'), sort_keys=True)[:200]}`")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only")
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--table-only", action="store_true")
    ap.add_argument("--max-mutants", type=int, default=None)
    ap.add_argument("--extended-cases", type=int, default=10000)
    a = ap.parse_args()
    ids = a.only.split(",") if a.only else targets()
    lock = threading.Lock()

    def log(msg):
        with lock:
            print(f"{time.strftime('%H:%M:%S')} {msg}", flush=True)

    def one(tid):
        out = OUT / tid
        if (out / "report.json").exists() and not a.force:
            log(f"{tid}: kept existing report")
            return
        try:
            rep = ss.run_task(taskmod.load(tid), a.max_mutants, ext_cases=a.extended_cases, log=log)
        except Exception as e:  # one task's failure does not stop the others
            log(f"{tid}: FAILED: {type(e).__name__}: {e}")
            return
        rep["shared_with"] = variants(tid)
        rep["report_sha256"] = ss.content_hash(rep)
        ss.write(rep, out)
        s = rep["summary"]
        log(f"{tid}: done in {rep['elapsed_s']} s: {s['compiled']} compiled, {s['equivalent']} equivalent, "
            f"{s['killed']} killed ({s['killed_kernel']} kernel-checked), {s['survived_differs']} differ, "
            f"{s['survived_same']} same")

    if not a.table_only:
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, min(a.jobs, 2))) as ex:
            for f in concurrent.futures.as_completed([ex.submit(one, t) for t in ids]):
                f.result()
    reports = [json.loads((OUT / t / "report.json").read_text()) for t in targets() if (OUT / t / "report.json").exists()]
    tbl, tot = table(reports)
    (OUT / "table.md").write_text(tbl + "\nSurviving mutants whose behaviour differs from the reference:\n\n"
                                  + survivors_md(reports))
    (OUT / "summary.json").write_text(json.dumps({
        "tasks": [{"task": r["task"]["id"], "report_sha256": r["report_sha256"], "shared_with": r.get("shared_with", []),
                   "supported": r.get("supported"), "summary": r["summary"], "vacuity": r["vacuity"]} for r in reports],
        "total": tot}, indent=2) + "\n")
    print(tbl)


if __name__ == "__main__":
    main()
