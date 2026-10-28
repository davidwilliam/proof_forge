#!/usr/bin/env python3
"""E1: does the harness raise completed, verified repairs under the same budget?

For every (task, arm) pair the arm's agent runs once under identical caps (dollars at
standard-tier list prices, wall clock including Lean and tool time). Every final
candidate is then scored by one shared evaluator, outside the budget: the official judge
(harness/judge.py) and the binary property check (harness/binary_check.py). A repair is
completed when the judge accepts and the binary passes.

Arms: A0 compile-and-retry (agents/baseline.py), A1 harness without planner, A2 harness
with the planner (agents/repair.py).

Usage: e1.py --label NAME [--split dev] [--tasks id,id] [--arms A0,A1,A2]
             [--budget-usd 3] [--budget-wall 2700] [--parallel 3] [--report-only]
Results: results/e1-<label>/ (per run: summary.json, final.lean, eval.json, events.jsonl).
"""
import argparse, hashlib, json, math, pathlib, random, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import binary_check, judge, task as taskmod  # noqa: E402

ARMS = {
    "A0": [sys.executable, str(ROOT / "agents/baseline.py")],
    "A1": [sys.executable, str(ROOT / "agents/repair.py"), "--planner", "none"],
    "A2": [sys.executable, str(ROOT / "agents/repair.py"), "--planner", "muse-wonder-1.0"],
}
EVAL_CASES, EVAL_SEED = 2000, 1


def task_ref(t):
    return str(t.root) if t.root == taskmod.FLAGSHIP else t.id


CODE_GLOBS = ["agents/*.py", "harness/*.py", "eval/e1.py", "infra/docker/Dockerfile.lean"]


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True).stdout.strip()


def frozen_config(a, tasks, arms):
    """Everything that determines a run's outcome; its hash keys every stored result."""
    code = {str(p.relative_to(ROOT)): taskmod.sha256(p) for g in CODE_GLOBS for p in sorted(ROOT.glob(g))}
    task_hashes = {t.id: {"manifest_sha256": t.locked()["manifest_sha256"],
                          "task_json": taskmod.sha256(t.root / "task.json"),
                          "oracle": taskmod.sha256(t.root / "oracle.py"),
                          "start_candidate": taskmod.sha256(t.start)} for t in tasks}
    cfg = {"tasks": [t.id for t in tasks], "arms": {arm: ARMS[arm][1:] for arm in arms}, "model": a.model,
           "budget_usd_list": a.budget_usd, "budget_wall_s": a.budget_wall, "parallel": a.parallel,
           "eval_cases": EVAL_CASES, "eval_seed": EVAL_SEED, "judge_image": judge.image_id(),
           "container_slots": judge.SLOTS, "code_sha256": code, "task_sha256": task_hashes,
           "batch_usd_list": a.batch_usd}
    cfg["config_sha256"] = hashlib.sha256(json.dumps(cfg, sort_keys=True).encode()).hexdigest()
    return cfg


class BatchCap:
    """Admit a run only if spent + (running + 1) * per-run cap stays within the batch cap,
    so the batch total never exceeds it."""
    def __init__(self, cap, per_run):
        self.cap, self.per_run, self.spent, self.running = cap, per_run, 0.0, 0
        self.lock = threading.Lock()

    def admit(self):
        with self.lock:
            if self.cap is not None and self.spent + (self.running + 1) * self.per_run > self.cap:
                return False
            self.running += 1
            return True

    def add(self, usd):
        """Count a run completed earlier (resume)."""
        with self.lock:
            self.spent += usd or 0.0

    def done(self, usd):
        with self.lock:
            self.running -= 1
            self.spent += usd or 0.0


def run_one(t, arm, a, out, cfg, cap):
    d = out / t.id / arm
    if (d / "eval.json").exists():
        ev = json.loads((d / "eval.json").read_text())
        if ev.get("config_sha256") != cfg["config_sha256"]:
            raise SystemExit(f"{d}: stored result has a different configuration; use a new label")
        cap.add(ev.get("usd_list"))
        return ev
    d.mkdir(parents=True, exist_ok=True)
    if not (d / "summary.json").exists():
        if not cap.admit():
            print(f"[{t.id} {arm}] skipped: batch cap reached", flush=True)
            return None
        cmd = ARMS[arm] + ["--task", task_ref(t), "--model", a.model, "--out", str(d),
                           "--budget-usd", str(a.budget_usd), "--budget-wall", str(a.budget_wall)]
        with (d / "agent.log").open("w") as log:
            try:
                subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, cwd=ROOT,
                               timeout=a.budget_wall + 1800)
            except subprocess.TimeoutExpired:
                log.write("\nrunner: agent process exceeded the wall cap plus grace and was stopped\n")
        s = json.loads((d / "summary.json").read_text()) if (d / "summary.json").exists() else {}
        cap.done(s.get("budget", {}).get("usd_list", a.budget_usd))
    ev = evaluate(t, d)
    ev["config_sha256"] = cfg["config_sha256"]
    (d / "eval.json").write_text(json.dumps(ev, indent=2) + "\n")
    print(f"[{t.id} {arm}] completed={ev['completed']} judge={ev['judge']} binary={ev['binary']} "
          f"usd_list={ev['usd_list']} stop={ev['stop']}", flush=True)
    return ev


def evaluate(t, d):
    """Shared evaluator: identical for every arm, outside the budget."""
    s = json.loads((d / "summary.json").read_text()) if (d / "summary.json").exists() else {}
    final = d / "final.lean"
    ev = {"task": t.id, "family": t.family, "base": base_of(t.id), "arm": d.name,
          "usd_list": s.get("budget", {}).get("usd_list"), "usd_actual": s.get("budget", {}).get("usd_actual"),
          "elapsed_s": s.get("budget", {}).get("elapsed_s"), "stop": s.get("budget", {}).get("stop"),
          "by_model": s.get("budget", {}).get("by_model", {})}
    if not final.exists():
        return {**ev, "judge": "MISSING", "binary": "MISSING", "completed": False}
    j = judge.judge(str(final), task=t)
    b = binary_check.check_binary(str(final), n_cases=EVAL_CASES, seed=EVAL_SEED, task=t)
    ev.update(judge="ACCEPT" if j["accepted"] else "REJECT", binary=b["status"],
              violations=b["violations"], final_sha256=taskmod.sha256(final),
              completed=j["accepted"] and b["status"] == "PASS")
    return ev


def base_of(task_id):
    """Tasks that share a base specification differ only in the trailing variant suffix."""
    parts = task_id.rsplit("-", 1)
    return parts[0] if len(parts) == 2 and parts[1][:1] == "b" and parts[1][1:].isdigit() else task_id


def mcnemar_exact(b, c):
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    p = sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n
    return min(1.0, 2 * p)


def paired_bootstrap(pairs, clusters, reps=10000, seed=0):
    """95% interval for mean(x - y); resampling whole clusters (base specifications)."""
    rng = random.Random(seed)
    groups = {}
    for (x, y), cl in zip(pairs, clusters):
        groups.setdefault(cl, []).append(x - y)
    keys = list(groups)
    stats = []
    for _ in range(reps):
        draw = [v for k in (rng.choice(keys) for _ in keys) for v in groups[k]]
        stats.append(sum(draw) / len(draw))
    stats.sort()
    return stats[int(0.025 * reps)], stats[int(0.975 * reps) - 1]


def report(out, results, arms):
    by = {(r["task"], r["arm"]): r for r in results}
    tasks = sorted({r["task"] for r in results})
    lines = ["# E1 results", "",
             f"Tasks: {len(tasks)}. A repair is completed when the judge accepts the final candidate and its binary passes {EVAL_CASES} property cases (seed {EVAL_SEED}). Budgets are identical per arm; dollars are at standard-tier list prices.", "",
             "| Arm | Completed | Judge accepts | Binary pass | Budget stops (usd / wall) | Mean list $ | List $ per completed repair |",
             "|---|---|---|---|---|---|---|"]
    summary = {"tasks": tasks, "arms": {}, "pairs": {}}
    for arm in arms:
        rs = [by[(t, arm)] for t in tasks if (t, arm) in by]
        done = sum(r["completed"] for r in rs)
        usd = [r["usd_list"] or 0 for r in rs]
        stops = (sum(r["stop"] == "usd" for r in rs), sum(r["stop"] == "wall" for r in rs))
        per = f"{sum(usd) / done:.2f}" if done else "n/a"
        lines.append(f"| {arm} | {done}/{len(rs)} | {sum(r['judge'] == 'ACCEPT' for r in rs)} | "
                     f"{sum(r['binary'] == 'PASS' for r in rs)} | {stops[0]} / {stops[1]} | "
                     f"{sum(usd) / max(1, len(rs)):.2f} | {per} |")
        summary["arms"][arm] = {"completed": done, "n": len(rs), "usd_list_total": round(sum(usd), 4)}
    for hi, lo in (("A1", "A0"), ("A2", "A1"), ("A2", "A0")):
        if hi not in arms or lo not in arms:
            continue
        common = [t for t in tasks if (t, hi) in by and (t, lo) in by]
        if not common:
            continue
        pairs = [(int(by[(t, hi)]["completed"]), int(by[(t, lo)]["completed"])) for t in common]
        b = sum(x == 1 and y == 0 for x, y in pairs)
        c = sum(x == 0 and y == 1 for x, y in pairs)
        lo_ci, hi_ci = paired_bootstrap(pairs, [base_of(t) for t in common])
        diff = sum(x - y for x, y in pairs) / len(pairs)
        p = mcnemar_exact(b, c)
        summary["pairs"][f"{hi}-{lo}"] = {"n": len(common), "diff": diff, "ci95_cluster": [lo_ci, hi_ci],
                                          "discordant": {"hi_only": b, "lo_only": c}, "mcnemar_p": p}
        lines += ["", f"{hi} vs {lo} on {len(common)} paired tasks: {sum(x for x, _ in pairs)} vs "
                  f"{sum(y for _, y in pairs)} completed; difference {diff:+.3f}, 95% interval "
                  f"[{lo_ci:+.3f}, {hi_ci:+.3f}] (bootstrap over base specifications); discordant pairs "
                  f"{hi} only {b}, {lo} only {c}; McNemar exact p = {p:.4f}."]
    lines += ["", "## Per family", "", "| Family | Tasks | " + " | ".join(arms) + " |",
              "|---|---|" + "---|" * len(arms)]
    summary["families"] = {}
    for fam in sorted({r["family"] for r in results}):
        ft = [t for t in tasks if any(by.get((t, a), {}).get("family") == fam for a in arms)]
        counts = {a: [sum(by[(t, a)]["completed"] for t in ft if (t, a) in by), sum((t, a) in by for t in ft)]
                  for a in arms}
        summary["families"][fam] = {a: {"completed": c, "n": n} for a, (c, n) in counts.items()}
        cells = [f"{c}/{n}" for c, n in counts.values()]
        lines.append(f"| {fam} | {len(ft)} | " + " | ".join(cells) + " |")
    lines += ["", "## Per task", "", "| Task | " + " | ".join(arms) + " |", "|---|" + "---|" * len(arms)]
    for t in tasks:
        cells = []
        for a in arms:
            r = by.get((t, a))
            cells.append("-" if not r else ("completed" if r["completed"] else
                         f"{r['judge'].lower()}/{r['binary'].lower()}") + (f" ({r['stop']} stop)" if r and r["stop"] else ""))
        lines.append(f"| {t} | " + " | ".join(cells) + " |")
    (out / "e1.md").write_text("\n".join(lines) + "\n")
    (out / "e1.json").write_text(json.dumps({"summary": summary, "results": results}, indent=2) + "\n")
    print("\n".join(lines[:12]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--label", required=True)
    ap.add_argument("--split", default="dev")
    ap.add_argument("--tasks", help="comma-separated task ids (overrides --split)")
    ap.add_argument("--arms", default="A0,A1,A2")
    ap.add_argument("--model", default="muse-spark-1.3-contributor")
    ap.add_argument("--budget-usd", type=float, default=3.0)
    ap.add_argument("--budget-wall", type=float, default=2700)
    ap.add_argument("--parallel", type=int, default=2)
    ap.add_argument("--report-only", action="store_true")
    ap.add_argument("--batch-usd", type=float, help="cap on the batch total at list prices")
    ap.add_argument("--require-clean", action="store_true", help="refuse to run with uncommitted tracked changes")
    a = ap.parse_args()
    arms = a.arms.split(",")
    tasks = [taskmod.load(x) for x in a.tasks.split(",")] if a.tasks else taskmod.all_tasks(a.split)
    out = ROOT / "results" / f"e1-{a.label}"
    out.mkdir(parents=True, exist_ok=True)
    if not a.report_only:
        dirty = git("status", "--porcelain", "--untracked-files=no")
        if a.require_clean and dirty:
            raise SystemExit("uncommitted tracked changes:\n" + dirty)
        cfg = frozen_config(a, tasks, arms)
        cfg_path = out / "config.json"
        if cfg_path.exists():
            old = json.loads(cfg_path.read_text())
            if old["config_sha256"] != cfg["config_sha256"]:
                diff = [k for k in cfg if k not in ("config_sha256",) and old.get(k) != cfg.get(k)]
                raise SystemExit(f"configuration differs from {cfg_path} in {diff}; use a new label")
        else:
            cfg.update(label=a.label, git_commit=git("rev-parse", "HEAD"), git_dirty=bool(dirty),
                       started=time.strftime("%Y-%m-%dT%H:%M:%S%z"))
            cfg_path.write_text(json.dumps(cfg, indent=2) + "\n")
        cap = BatchCap(a.batch_usd, a.budget_usd)
        # Interleave arms so a partial run still yields paired tasks.
        jobs = [(t, arm) for t in tasks for arm in arms]
        with ThreadPoolExecutor(a.parallel) as ex:
            results = [r for r in ex.map(lambda j: run_one(j[0], j[1], a, out, cfg, cap), jobs) if r]
    else:
        results = [json.loads(p.read_text()) for p in sorted(out.glob("*/*/eval.json"))]
    report(out, results, arms)


if __name__ == "__main__":
    main()
