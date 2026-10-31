#!/usr/bin/env python3
"""Replay the tactic portfolio (agents/portfolio.py) on the goals of recorded runs; no model calls.

For every goal a recorded repair run spent model turns on (a dialog labelled `<phase>:<goal>`: a
required theorem, a planner lemma, a skeleton helper), the goal is taken from the candidate version
on disk when its first dialog started (`candidate_v<k>.lean`, the newest write before that dialog's
first turn) and the portfolio batch is compiled on it exactly as the agent would have before that
turn: the goal removed from the file, one renamed copy per tactic under the heartbeat limit,
`#print axioms` of each copy. A goal counts as closed when some tactic's copy has no error and no
`sorryAx`. The recording gives what the goal cost: its turns, their list-price dollars (planner
calls are not included: the recorded runs do not log their usage per goal) and whether the model
proved it in the end. A run directory without candidate versions uses final.lean as the context
(marked `approximate`); a goal missing from it is restated from its last planner or snippet text.
For an A0 run (whole-file turns, no goal dialogs) the goals are the required theorems its final
candidate leaves unproved, replayed on final.lean, with the run's turns and dollars as run totals.

Usage: portfolio_replay.py RUN_DIR [RUN_DIR ...] --out DIR [--heartbeats N] [--seconds S] [--jobs J]
Writes DIR/portfolio-replay.json (per goal) and prints a summary.
"""
import argparse, concurrent.futures, json, pathlib, re, shutil, statistics, sys, tempfile, threading, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness")]
import budget, fin_lib, ledger, portfolio, repair, task as taskmod  # noqa: E402


def goal_dialogs(events):
    """Per goal: the version on disk when its first dialog started, its dialogs, turns and dollars,
    and whether a dialog on it ended with the goal proved."""
    version, goals = 0, {}
    for e in events:
        k = e.get("kind")
        if k == "write":
            version = e.get("version", version)
        elif k == "turn":
            g = ledger.goal_label(e.get("label"))
            if not g:
                continue
            r = goals.setdefault(g, {"goal": g, "first_version": version, "first_label": e["label"], "dialogs": 0,
                                     "turns": 0, "usd_list": 0.0, "proved_by_model": False})
            r["turns"] += 1
            r["dialogs"] += e.get("turn") == 0
            try:
                r["usd_list"] += budget.list_cost(e.get("model"), e.get("usage") or {})
            except KeyError:
                pass
        elif k == "obligation" and e.get("ok") and e.get("theorem") in goals:
            goals[e["theorem"]]["proved_by_model"] = True
    for r in goals.values():
        r["usd_list"] = round(r["usd_list"], 4)
    return list(goals.values())


def restated(events, name):
    """The newest statement of `name` in the run's planner code or snippet texts, as an open goal."""
    for e in reversed(events):
        texts = []
        if e.get("kind") == "plan":
            texts.append(e.get("code") or "")
        elif e.get("kind") == "tool":
            a = e.get("args") or {}
            texts += [a.get("code") or "", a.get("text") or ""]
        for t in texts:
            m = re.search(rf"^(?:theorem|lemma)\s+{re.escape(name)}(?=[\s:({{\[]).*?(?=^\S|\Z)", t, re.M | re.S)
            if m:
                head, _ = portfolio.split_proof(m.group(0))
                if head:
                    return head.strip() + " := by\n  sorry"
    return None


def reopen(src, task, name):
    """`src` with the proof of theorem `name` replaced by `sorry` (a goal the final candidate of an
    approximate context already proves, or proves wrongly, is asked again on its statement)."""
    for n, kind, text in ledger.declarations(src, task.ns):
        if n == name and kind in ("theorem", "lemma") and not ledger.has_sorry(text):
            head, _ = ledger.split_proof(text)
            if head:
                return src.replace(text, head.rstrip() + " := by\n  sorry", 1)
    return src


def contexts(run_dir, task):
    """(goal records, {context key: (source, approximate)}) for one run directory."""
    d = pathlib.Path(run_dir)
    summ = json.loads((d / "summary.json").read_text())
    ev = ledger._events(d)
    final = (d / "final.lean").read_text()
    goals = goal_dialogs(ev)
    if not goals:   # A0: whole-file turns
        turns = sum(1 for e in ev if e.get("kind") in ("attempt", "turn"))
        usd = (summ.get("budget") or {}).get("usd_list")
        for t, v in (summ.get("final_status") or {}).items():
            if v != "PROVED":
                goals.append({"goal": t, "first_version": None, "first_label": "whole-file", "dialogs": 0,
                              "turns": turns, "usd_list": usd, "scope": "run", "proved_by_model": False})
    ctx = {}
    for g in goals:
        f = d / f"candidate_v{g['first_version']:03d}.lean" if g["first_version"] else None
        src, approx = (f.read_text(), False) if f and f.exists() else (final, True)
        if approx:
            src = reopen(src, task, g["goal"])
        if not re.search(rf"^{repair.DECL_PREFIX}{repair.DECL_KINDS}\s+{re.escape(g['goal'])}(?=[\s:({{\[])", src, re.M):
            stmt = restated(ev, g["goal"])
            end = f"end {task.ns}"
            if stmt and end in src:
                head, tail = src.rsplit(end, 1)
                src, approx = head.rstrip("\n") + "\n\n" + stmt + "\n\n" + end + tail, True
        key = (hash(src), approx)
        ctx.setdefault(key, (src, approx))
        g["context"] = key
    return summ, goals, ctx


_lock = threading.Lock()


def replay_run(run_dir, heartbeats, seconds, log):
    d = pathlib.Path(run_dir)
    summ = json.loads((d / "summary.json").read_text())
    task = taskmod.load(summ["task"])
    _, goals, ctx = contexts(d, task)
    if not goals:
        return {"run_dir": str(d), "task": task.id, "arm": summ.get("arm"), "goals": []}
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="pf-replay-"))
    start = tmp / "start.lean"
    start.write_text(next(iter(ctx.values()))[0])
    lib = bool((summ.get("library") or {}).get("enabled"))
    s = repair.Session(task, summ.get("model") or "muse-spark-1.3-contributor", start, tmp, budget.Budget(None, None),
                       library=lib)
    out = []
    try:
        for bi, (key, (src, approx)) in enumerate(ctx.items()):
            mine = [g for g in goals if g["context"] == key]
            (s.ws / "candidate/Solution.lean").write_text(src)
            found = [(g, portfolio.goal_of(s, g["goal"], src)) for g in mine]
            batch = [x for _, x in found if x]
            res, info = (portfolio.run_portfolio(s, batch, heartbeats=heartbeats, seconds=seconds, src=src)
                         if batch else ({}, {"ms": 0, "attempts": 0, "stopped": False}))
            for g, x in found:
                r = res.get(g["goal"], {})
                closed = [k for k, _, _ in portfolio.PORTFOLIO if r.get(k, {}).get("ok")]
                rec = {k: v for k, v in g.items() if k != "context"}
                rec.update({"approximate_context": approx, "statement": x["head"] if x else None,
                            "replayed": x is not None, "closed_by": closed[0] if closed else None, "closing": closed,
                            "batch": bi, "batch_ms": info["ms"], "batch_goals": len(batch), "stopped": info.get("stopped", False),
                            "retried_without_search": info.get("retried", False),
                            "tactics": {k: {kk: v[kk] for kk in ("ok", "ms", "limit", "error")} | {"suggest": v["suggest"][:1]}
                                        for k, v in r.items()}})
                out.append(rec)
                with _lock:
                    log(f"{d.parent.name}/{d.name} {g['goal']}: {rec['closed_by'] or '-'} ({info['ms']} ms, "
                        f"{g['turns']} turns, ${g['usd_list'] or 0:.2f})")
    finally:
        shutil.rmtree(s.ws, ignore_errors=True)
        shutil.rmtree(tmp, ignore_errors=True)
    return {"run_dir": str(d), "task": task.id, "arm": summ.get("arm"), "library": lib, "goals": out}


def summarize(runs):
    rows, per_tactic = [], {}
    for r in runs:
        gs = [g for g in r["goals"] if g["replayed"]]
        closed = [g for g in gs if g["closed_by"]]
        scope_run = any(g.get("scope") == "run" for g in gs)
        rows.append({"run": r["run_dir"], "task": r["task"], "arm": r["arm"], "goals": len(r["goals"]),
                     "replayed": len(gs), "closed": len(closed),
                     "closed_goals": {g["goal"]: g["closed_by"] for g in closed},
                     "closed_turns": None if scope_run else sum(g["turns"] for g in closed),
                     "closed_usd": None if scope_run else round(sum(g["usd_list"] or 0 for g in closed), 4),
                     "all_turns": None if scope_run else sum(g["turns"] for g in gs),
                     "all_usd": None if scope_run else round(sum(g["usd_list"] or 0 for g in gs), 4),
                     "closed_proved_by_model_later": sum(1 for g in closed if g["proved_by_model"]),
                     "approximate_contexts": sum(1 for g in gs if g["approximate_context"]),
                     "portfolio_ms": sum({g["batch"]: g["batch_ms"] for g in gs}.values()),
                     "batches": len({g["batch"] for g in gs})})
        for g in gs:
            for k, v in g["tactics"].items():
                t = per_tactic.setdefault(k, {"attempts": 0, "closed": 0, "first": 0, "limit": 0, "ms": []})
                t["attempts"] += 1
                t["closed"] += bool(v["ok"])
                t["first"] += g["closed_by"] == k
                t["limit"] += bool(v["limit"])
                if v["ms"] is not None:
                    t["ms"].append(v["ms"])
    tactics = {}
    for k, t in per_tactic.items():
        ms = sorted(t["ms"])
        tactics[k] = {"attempts": t["attempts"], "closed": t["closed"], "closed_first": t["first"],
                      "heartbeat_limit": t["limit"], "timed": len(ms),
                      "ms_median": statistics.median(ms) if ms else None,
                      "ms_p90": ms[int(0.9 * (len(ms) - 1))] if ms else None, "ms_max": ms[-1] if ms else None,
                      "ms_total": sum(ms)}
    return {"runs": rows, "tactics": tactics}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("runs", nargs="+")
    ap.add_argument("--out", required=True)
    ap.add_argument("--heartbeats", type=int, default=portfolio.HEARTBEATS)
    ap.add_argument("--seconds", type=float, default=portfolio.SECONDS)
    ap.add_argument("--jobs", type=int, default=1, help="runs replayed at once (each uses one Lean container)")
    ap.add_argument("--threads", type=int, help="LEAN_NUM_THREADS for every Lean run (the machine may be shared)")
    a = ap.parse_args()
    if a.threads:
        import judge
        orig = judge.in_container
        judge.in_container = lambda project, script, timeout=900: orig(
            project, f"export LEAN_NUM_THREADS={a.threads}; {script}", timeout=timeout)
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    logf = (out / "portfolio-replay.log").open("a")

    def log(msg):
        print(msg, flush=True)
        logf.write(msg + "\n")
        logf.flush()
    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        runs = list(ex.map(lambda d: replay_run(d, a.heartbeats, a.seconds, log), a.runs))
    report = {"heartbeats": a.heartbeats, "seconds": a.seconds, "portfolio": [k for k, _, _ in portfolio.PORTFOLIO],
              "library_source_tree_sha256": fin_lib.tree_sha256(), "elapsed_s": round(time.time() - t0, 1),
              **summarize(runs), "goals": runs}
    (out / "portfolio-replay.json").write_text(json.dumps(report, indent=1))
    print(json.dumps({k: report[k] for k in ("runs", "tactics", "elapsed_s")}, indent=1))


if __name__ == "__main__":
    main()
