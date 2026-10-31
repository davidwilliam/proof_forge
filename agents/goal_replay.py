#!/usr/bin/env python3
"""Replay recorded try_snippet calls through the compile path and through the persistent Lean
session (agents/leanserver.py); no model calls.

For a window of consecutive try_snippet calls of a recorded run, each snippet is checked on the
candidate version it was recorded against (`candidate_v<k>.lean` of its `snippet` event), first as
the agent did then (`lake env lean Scratch.lean`: the whole candidate elaborated again), then on the
persistent session (the scratch text sent as an incremental change; Lean re-elaborates only from
the first changed character). Per snippet: both times, whether the verdicts agree (an error or a
`sorry` from the server, or clean and then compiled), the bytes of both answers, and `goal_at` on
the dialog's goal where it is still open (time and bytes). The recording gives each turn's model
time and tool time, so the per-turn latency with the session follows from the measured tool times.
Times are Lean's: the compile's run time and the session's elaboration time, both measured after a
container slot is acquired (the host's other Lean runs are not counted).

Usage: goal_replay.py RUN_DIR --out DIR [--snippets N] [--start F] [--threads T]
Writes DIR/goal-replay-<run>.json and prints a summary.
"""
import argparse, json, pathlib, statistics, sys, tempfile, shutil, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness")]
import budget, ledger, leanserver, repair, task as taskmod  # noqa: E402


def recorded_snippets(events):
    """[(snippet event, tool event)] in order: each try_snippet tool call with the `snippet` event
    of its compile (version, ok, ms)."""
    out, last = [], None
    for e in events:
        if e.get("kind") == "snippet":
            last = e
        elif e.get("kind") == "tool" and e.get("name") == "try_snippet":
            if last is not None and not str(e.get("result", "")).startswith("error: not compiled"):
                out.append((last, e))
            last = None
    return out


def turn_times(events):
    """Per dialog turn: seconds from the turn event to the next turn of the same dialog (model call of
    the next turn plus the tools of this one), and this turn's tool milliseconds."""
    turns, by_label = [], {}
    for e in events:
        if e.get("kind") == "turn":
            prev = by_label.get(e.get("label"))
            if prev is not None and e.get("turn") == prev["turn"] + 1:
                prev["next_s"] = e["t"] - prev["t"]
            rec = {"label": e.get("label"), "turn": e.get("turn"), "t": e["t"], "tool_ms": 0, "snippet_ms": 0,
                   "snippets": 0}
            by_label[e.get("label")] = rec
            turns.append(rec)
        elif e.get("kind") == "tool" and e.get("label") in by_label:
            r = by_label[e["label"]]
            r["tool_ms"] += e.get("ms") or 0
            if e.get("name") == "try_snippet":
                r["snippet_ms"] += e.get("ms") or 0
                r["snippets"] += 1
    return [t for t in turns if "next_s" in t]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--out", required=True)
    ap.add_argument("--snippets", type=int, default=40)
    ap.add_argument("--start", type=float, default=0.4, help="window start, as a fraction of the run's snippets")
    ap.add_argument("--threads", type=int)
    a = ap.parse_args()
    if a.threads:
        import judge, os
        os.environ["LEAN_NUM_THREADS"] = str(a.threads)
        orig = judge.in_container
        judge.in_container = lambda project, script, timeout=900: orig(
            project, f"export LEAN_NUM_THREADS={a.threads}; {script}", timeout=timeout)
    d = pathlib.Path(a.run)
    summ = json.loads((d / "summary.json").read_text())
    task = taskmod.load(summ["task"])
    ev = ledger._events(d)
    snips = recorded_snippets(ev)
    i0 = int(len(snips) * a.start)
    window = snips[i0:i0 + a.snippets]
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="pf-goal-replay-"))
    first = d / f"candidate_v{window[0][0]['version']:03d}.lean"
    s = repair.Session(task, summ.get("model") or "muse-spark-1.3-contributor", first, tmp, budget.Budget(None, None),
                       library=bool((summ.get("library") or {}).get("enabled")))
    s.topdown = summ.get("mode") == "topdown"
    rows = []
    try:
        for sn, tool in window:
            f = d / f"candidate_v{sn['version']:03d}.lean"
            if not f.exists():
                continue
            src = f.read_text()
            (s.ws / "candidate/Solution.lean").write_text(src)
            code, hoist, refusal = s._snippet_imports(tool["args"].get("code", ""), src)
            if refusal:
                continue
            code = s._snippet_opens(code)
            s.goal_tool = False
            clean_c, msgs_c, compile_ms = s._scratch(code, hoist)   # Lean time, without the wait for a slot
            s.goal_tool = True
            srv = leanserver.server(s)
            before = dict(srv.stats)
            st0 = dict(s.__dict__.get("goal_stats", {}))
            clean_s, msgs_s, _ = s._scratch(code, hoist)
            st1 = s.__dict__.get("goal_stats", {})
            fast = st1.get("fast_rejected", 0) > st0.get("fast_rejected", 0)
            server_ms = srv.stats["sync_ms"] - before.get("sync_ms", 0) + srv.stats["start_ms"] - before.get("start_ms", 0)
            goal = ledger.goal_label(tool.get("label")) or ""
            g = {}
            if goal and "sorry" in repair.decl_text(s, goal, src):
                t0 = time.monotonic()
                out = leanserver.goal_at(s, goal)
                g = {"goal_at_ms": int((time.monotonic() - t0) * 1000), "goal_at_bytes": len(out.encode())}
            rows.append({"version": sn["version"], "label": tool.get("label"), "recorded_ok": sn.get("ok"),
                         "recorded_ms": sn.get("ms"), "code_bytes": len(tool["args"].get("code", "").encode()),
                         "has_sorry": "sorry" in tool["args"].get("code", ""),
                         "compile_clean": clean_c, "compile_ms": compile_ms,
                         "compile_bytes": len("\n".join(msgs_c).encode()),
                         "server_verdict": "rejected" if fast else ("clean" if clean_s else "other"),
                         "server_ms": server_ms,
                         "server_bytes": len("\n".join(msgs_s).encode()) if fast else None,
                         "agree": (not clean_c) == fast or (clean_c and clean_s), "full_elaboration": srv.stats["full_syncs"] > before.get("full_syncs", 0),
                         **g})
            r = rows[-1]
            print(f"v{r['version']} {r['label']}: compile {r['compile_ms']} ms ({'clean' if clean_c else 'fails'}), "
                  f"server {r['server_ms']} ms ({r['server_verdict']}), agree {r['agree']}"
                  + (f", goal_at {g['goal_at_ms']} ms {g['goal_at_bytes']} B" if g else ""), flush=True)
    finally:
        leanserver.close(s)
        shutil.rmtree(s.ws, ignore_errors=True)
        shutil.rmtree(tmp, ignore_errors=True)
    fails = [r for r in rows if not r["compile_clean"]]
    warm = [r for r in fails if not r["full_elaboration"]]
    tt = turn_times(ev)
    snippet_turns = [t for t in tt if t["snippets"]]

    def med(xs):
        return statistics.median(xs) if xs else None
    rec_fail_ms = [sn.get("ms") for sn, _ in snips if not sn.get("ok") and sn.get("ms")]
    report = {
        "run": str(d), "task": task.id, "window": [i0, i0 + len(window)], "snippets": len(rows),
        "candidate_bytes": [min(len((d / f"candidate_v{r['version']:03d}.lean").read_bytes()) for r in rows),
                            max(len((d / f"candidate_v{r['version']:03d}.lean").read_bytes()) for r in rows)] if rows else None,
        "failing": len(fails), "agree": sum(r["agree"] for r in rows),
        "compile_ms_failing_median": med([r["compile_ms"] for r in fails]),
        "server_ms_failing_median": med([r["server_ms"] for r in fails]),
        "server_ms_failing_warm_median": med([r["server_ms"] for r in warm]),
        "full_elaborations": sum(r["full_elaboration"] for r in rows),
        "server_ms_full_elaboration": [r["server_ms"] for r in rows if r["full_elaboration"]],
        "clean_compile_ms_median": med([r["compile_ms"] for r in rows if r["compile_clean"]]),
        "clean_server_ms_median": med([r["server_ms"] for r in rows if r["compile_clean"]]),
        "bytes_failing_compile": sum(r["compile_bytes"] for r in fails),
        "bytes_failing_server": sum(r["server_bytes"] or 0 for r in fails),
        "goal_at": {"calls": sum(1 for r in rows if "goal_at_ms" in r),
                    "ms_median": med([r["goal_at_ms"] for r in rows if "goal_at_ms" in r]),
                    "bytes_median": med([r["goal_at_bytes"] for r in rows if "goal_at_bytes" in r])},
        "recorded": {"snippets": len(snips), "failing": len(rec_fail_ms), "failing_ms_median": med(rec_fail_ms),
                     "with_sorry": sum(1 for _, t in snips if "sorry" in t["args"].get("code", "")),
                     "with_sorry_code_bytes": sum(len(t["args"].get("code", "").encode()) for _, t in snips
                                                  if "sorry" in t["args"].get("code", "")),
                     "snippet_turns": len(snippet_turns),
                     "turn_s_median": med([t["next_s"] for t in snippet_turns]),
                     "turn_snippet_s_median": med([t["snippet_ms"] / 1000 for t in snippet_turns])},
        "rows": rows}
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    name = f"goal-replay-{d.parent.name}-{d.name}.json"
    (out / name).write_text(json.dumps(report, indent=1))
    print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=1))


if __name__ == "__main__":
    main()
