#!/usr/bin/env python3
"""Implement mode on the frozen E1 test tasks: can the agent write the code from the
specification alone, and prove every locked requirement?

The arm is the E1 A1 configuration (agents/repair.py, Muse Spark, no planner) with
`--mode implement`: the run starts from a stub generated from the locked challenge (every
required definition keeps its signature with a neutral placeholder body, every required
theorem is `sorry`) and the brief asks for an implementation from the spec instead of giving
the issue report. Everything else is E1 (eval/e1.py): the same per-run caps, the test freeze
check, the batch ledger, and the shared evaluator outside the budget (harness/judge.py plus
the binary rebuilt from the final candidate and 2,000 property cases). One run per task.

Variants of a base specification (the -bN suffix) differ only in their buggy candidate and
issue report, which implement mode does not use, so they are repeated trials of the same
problem: 30 runs over 9 specifications.

Usage: implement.py --label 1 [--tasks id,id] [--budget-usd 3] [--budget-wall 3600]
                    [--parallel 2] [--batch-usd 150] [--report-only]
Results: results/implement-<label>/ (per run: <task>/A1/{summary.json, final.lean,
start.lean, eval.json, events.jsonl, agent.log}; implement.json, implement.md).
"""
import argparse, json, pathlib, sys, time
from concurrent.futures import ThreadPoolExecutor

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "eval"))
sys.path.insert(0, str(ROOT / "harness"))
import e1, task as taskmod  # noqa: E402

ARM = "A1"
e1.ARMS = {ARM: [sys.executable, str(ROOT / "agents/repair.py"), "--planner", "none", "--mode", "implement"]}
e1.CODE_GLOBS = e1.CODE_GLOBS + ["eval/implement.py"]
REPAIR_RESULTS = ROOT / "results/e1-test-1"


def failure_reason(ev, s, events):
    """Plain description of why a run was not accepted, from its recorded artifacts."""
    parts = []
    stop = ev.get("stop")
    parts.append({"usd": "stopped at the dollar cap", "wall": "stopped at the wall-clock cap"}.get(
        stop, "ended before the caps" if not stop else f"stopped: {stop}"))
    phase0 = [e for e in events if e.get("kind") == "phase" and e.get("phase") == "implement"]
    if phase0 and not phase0[-1].get("ok"):
        parts.append("the implementation never passed the property tests in phase 1")
    st = s.get("final_status") or {}
    if st:
        if all(v == "ERROR" for v in st.values()):
            parts.append("final candidate does not compile")
        else:
            proved = [k for k, v in st.items() if v == "PROVED"]
            other = [f"{k}={v}" for k, v in st.items() if v != "PROVED"]
            parts.append(f"{len(proved)} of {len(st)} requirements proved" + (f" (open: {', '.join(other)})" if other else ""))
    parts.append(f"judge {ev.get('judge')}, binary {ev.get('binary')}")
    if ev.get("violations"):
        parts.append("binary violations: " + ", ".join(f"{k} ({v})" for k, v in ev["violations"].items()))
    return "; ".join(parts)


def report(out, tasks):
    results, rows = [], []
    for t in tasks:
        d = out / t.id / ARM
        if not (d / "eval.json").exists():
            continue
        ev = json.loads((d / "eval.json").read_text())
        s = json.loads((d / "summary.json").read_text()) if (d / "summary.json").exists() else {}
        events = [json.loads(l) for l in (d / "events.jsonl").read_text().splitlines()] if (d / "events.jsonl").exists() else []
        rep = REPAIR_RESULTS / t.id / ARM / "eval.json"
        repair_done = json.loads(rep.read_text())["completed"] if rep.exists() else None
        row = {"task": t.id, "family": t.family, "base": e1.base_of(t.id), "accepted": ev["completed"],
               "judge": ev["judge"], "binary": ev["binary"], "usd_list": ev["usd_list"], "usd_actual": ev["usd_actual"],
               "elapsed_s": ev["elapsed_s"], "stop": ev["stop"], "versions": s.get("versions"),
               "accepted_in_session": s.get("accepted_in_session"), "final_status": s.get("final_status"),
               "repair_mode_A1_completed": repair_done}
        if not ev["completed"]:
            row["failure"] = failure_reason(ev, s, events)
        rows.append(row)
        results.append(ev)
    n = len(rows)
    acc = sum(r["accepted"] for r in rows)
    usd_l = sum(r["usd_list"] or 0 for r in rows)
    usd_a = sum(r["usd_actual"] or 0 for r in rows)
    rep_rows = [r for r in rows if r["repair_mode_A1_completed"] is not None]
    rep_acc = sum(r["repair_mode_A1_completed"] for r in rep_rows)
    rep_usd = sum(json.loads((REPAIR_RESULTS / r["task"] / ARM / "eval.json").read_text())["usd_list"] for r in rep_rows)
    rep_usd_a = sum(json.loads((REPAIR_RESULTS / r["task"] / ARM / "eval.json").read_text())["usd_actual"] for r in rep_rows)
    cfg = json.loads((out / "config.json").read_text()) if (out / "config.json").exists() else {}
    summary = {"runs": n, "accepted": acc, "usd_list_total": round(usd_l, 4), "usd_actual_total": round(usd_a, 4),
               "usd_list_per_accepted": round(usd_l / acc, 4) if acc else None,
               "budget_usd_list_per_run": cfg.get("budget_usd_list"), "budget_wall_s_per_run": cfg.get("budget_wall_s"),
               "model": cfg.get("model"), "families": {}, "bases": {},
               "repair_mode_A1": {"source": "results/e1-test-1", "completed": rep_acc, "n": len(rep_rows),
                                  "usd_list_total": round(rep_usd, 4), "usd_actual_total": round(rep_usd_a, 4)}}
    for key, field in (("families", "family"), ("bases", "base")):
        for v in sorted({r[field] for r in rows}):
            rs = [r for r in rows if r[field] == v]
            summary[key][v] = {"accepted": sum(r["accepted"] for r in rs), "n": len(rs),
                               "repair_mode_A1_completed": sum(bool(r["repair_mode_A1_completed"]) for r in rs),
                               "usd_list": round(sum(r["usd_list"] or 0 for r in rs), 4),
                               "usd_actual": round(sum(r["usd_actual"] or 0 for r in rs), 4)}
    both = sum(r["accepted"] and r["repair_mode_A1_completed"] for r in rep_rows)
    impl_only = sum(r["accepted"] and not r["repair_mode_A1_completed"] for r in rep_rows)
    rep_only = sum(r["repair_mode_A1_completed"] and not r["accepted"] for r in rep_rows)
    summary["paired_with_repair"] = {"both": both, "implement_only": impl_only, "repair_only": rep_only,
                                     "mcnemar_p": e1.mcnemar_exact(impl_only, rep_only)}
    stops = {k: sum(r["stop"] == k for r in rows) for k in ("usd", "wall")}
    summary["budget_stops"] = stops
    L = ["# Implement mode on the E1 test tasks", "",
         f"Arm: the E1 A1 configuration ({cfg.get('model', 'muse-spark-1.3-contributor')}, no planner) with `--mode implement`. "
         "Each run starts from a stub generated from the locked challenge: the required definition keeps its exact "
         "signature with a placeholder body that rejects every input and returns the state unchanged, and every "
         "required theorem is `sorry`. The brief asks for an implementation of the definition from the spec, which it "
         "names as the source of truth; the issue report, the buggy candidate and the reference solutions are not used. "
         f"Per-run caps: ${cfg.get('budget_usd_list', 3.0):g} at standard list prices and {cfg.get('budget_wall_s', 3600):g} s. "
         "A run is accepted when the official judge accepts its final candidate and the binary rebuilt from it passes "
         f"{e1.EVAL_CASES} property cases (seed {e1.EVAL_SEED}), the E1 evaluator unchanged. One run per task, no reruns.", "",
         "The 30 tasks are 9 base specifications with 3 or 4 variants each. Variants differ only in their buggy candidate "
         "and issue report, so in implement mode they share the starting stub and the prompt: the variants of a base are "
         "repeated trials of the same problem, not independent problems.", "",
         f"Accepted: {acc} of {n}.", "",
         f"Repair mode, same arm, same tasks (`results/e1-test-1`, A1): {rep_acc} of {len(rep_rows)}. "
         f"Paired: {both} accepted in both modes, {impl_only} only in implement mode, {rep_only} only in repair mode "
         f"(McNemar exact p = {summary['paired_with_repair']['mcnemar_p']:.4f}).", "",
         "| | Implement mode | Repair mode (E1 A1) |", "|---|---|---|",
         f"| Accepted | {acc} of {n} | {rep_acc} of {len(rep_rows)} |",
         f"| Total at standard list prices | ${usd_l:.2f} | ${rep_usd:.2f} |",
         f"| Total charged (Contributor tier) | ${usd_a:.2f} | ${rep_usd_a:.2f} |",
         f"| List $ per accepted run | {f'{usd_l / acc:.2f}' if acc else 'n/a'} | {f'{rep_usd / rep_acc:.2f}' if rep_acc else 'n/a'} |",
         f"| Budget stops (dollars / wall clock) | {stops['usd']} / {stops['wall']} | |", "",
         "## Per family", "", "| Family | Implement accepted | Repair (E1 A1) completed | List $ | Charged $ |", "|---|---|---|---|---|"]
    for fam, v in summary["families"].items():
        L.append(f"| {fam} | {v['accepted']} of {v['n']} | {v['repair_mode_A1_completed']} of {v['n']} | {v['usd_list']:.2f} | {v['usd_actual']:.2f} |")
    L += ["", "## Per base specification", "", "| Base | Implement accepted | Repair (E1 A1) completed |", "|---|---|---|"]
    for b, v in summary["bases"].items():
        L.append(f"| {b} | {v['accepted']} of {v['n']} | {v['repair_mode_A1_completed']} of {v['n']} |")
    L += ["", "## Per task", "", "| Task | Result | List $ | Charged $ | Seconds | Stop |", "|---|---|---|---|---|---|"]
    for r in rows:
        res = "accepted" if r["accepted"] else f"not accepted ({r['judge'].lower()}/{r['binary'].lower()})"
        L.append(f"| {r['task']} | {res} | {r['usd_list']:.2f} | {r['usd_actual']:.4f} | {r['elapsed_s']:.0f} | {r['stop'] or '-'} |")
    fails = [r for r in rows if not r["accepted"]]
    L += ["", "## Runs not accepted", ""]
    L += [f"- {r['task']}: {r['failure']}." for r in fails] if fails else ["None."]
    cov = out / "coverage.json"
    if cov.exists():
        c = json.loads(cov.read_text())
        L += ["", "## Coverage", "", f"Batch spend at list prices: ${c['batch_spent_usd_list']:.2f}. "
              + ("Every task ran." if not c["not_run"] else "Not run (batch cap): " + ", ".join(sorted(c["not_run"])) + ".")
              + f" Interrupted runs set aside: {len(list(out.glob('*/*.interrupted-*')))}."]
    (out / "implement.md").write_text("\n".join(L) + "\n")
    (out / "implement.json").write_text(json.dumps({"summary": summary, "runs": rows, "results": results}, indent=2) + "\n")
    print("\n".join(L[:22]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--label", required=True)
    ap.add_argument("--tasks", help="comma-separated task ids (default: the tasks of results/e1-test-1)")
    ap.add_argument("--model", default="muse-spark-1.3-contributor")
    ap.add_argument("--budget-usd", type=float, default=3.0)
    ap.add_argument("--budget-wall", type=float, default=3600)
    ap.add_argument("--parallel", type=int, default=2)
    ap.add_argument("--batch-usd", type=float, default=150)
    ap.add_argument("--report-only", action="store_true")
    ap.add_argument("--freeze", type=pathlib.Path, default=ROOT / "results/test-freeze.json")
    a = ap.parse_args()
    ids = a.tasks.split(",") if a.tasks else json.loads((REPAIR_RESULTS / "config.json").read_text())["tasks"]
    tasks = [taskmod.load(x) for x in ids]
    out = ROOT / "results" / f"implement-{a.label}"
    out.mkdir(parents=True, exist_ok=True)
    if not a.report_only:
        if any(t.split == "test" for t in tasks):
            from freeze import verify_record
            try:
                a.freeze_sha256 = verify_record(a.freeze, tasks)
            except (OSError, ValueError, KeyError) as exc:
                raise SystemExit(f"test freeze verification failed: {exc}") from exc
        cfg = e1.frozen_config(a, tasks, [ARM])
        cfg["task_mode"] = "implement"
        cfg_path = out / "config.json"
        if cfg_path.exists():
            old = json.loads(cfg_path.read_text())
            if old["config_sha256"] != cfg["config_sha256"]:
                diff = [k for k in cfg if k != "config_sha256" and old.get(k) != cfg.get(k)]
                raise SystemExit(f"configuration differs from {cfg_path} in {diff}; use a new label")
        else:
            dirty = e1.git("status", "--porcelain", "--untracked-files=no")
            cfg.update(label=a.label, git_commit=e1.git("rev-parse", "HEAD"), git_dirty=bool(dirty),
                       git_dirty_files=sorted(l[3:] for l in dirty.splitlines()),
                       started=time.strftime("%Y-%m-%dT%H:%M:%S%z"))
            cfg_path.write_text(json.dumps(cfg, indent=2) + "\n")
        cap = e1.BatchCap(a.batch_usd, a.budget_usd)
        cap.rebuild(out, tasks, [ARM])
        print(f"batch ledger before scheduling: ${cap.spent:.2f} at list prices", flush=True)
        with ThreadPoolExecutor(a.parallel) as ex:
            outcomes = list(ex.map(lambda t: e1.run_task(t, [ARM], a, out, cfg, cap), tasks))
        not_run = {o["task"]: o["not_run"] for o in outcomes if o.get("not_run")}
        (out / "coverage.json").write_text(json.dumps({"not_run": not_run, "batch_spent_usd_list": round(cap.spent, 4)},
                                                     indent=2) + "\n")
    report(out, tasks)


if __name__ == "__main__":
    main()
