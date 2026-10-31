#!/usr/bin/env python3
"""Replay refutation by sampling (agents/refute.py) on the lemmas recorded runs introduced; no model
calls.

Introduced lemmas: every planner decomposition (`plan` events: its lemmas), every accepted skeleton
(`skeleton` events: its open helpers) and every helper the model stated with `sorry` through
replace_declaration that compiled. Each is sampled on the candidate version written when it was
introduced (`candidate_v<k>.lean` of the `plan ...`, `skeleton ...` or `inserted/replaced ...`
write), which is the context the agent would sample it in now. A run directory without candidate
versions uses final.lean with the lemma restated from its recorded text (marked approximate).
The recording gives what each lemma cost afterwards: the turns and list-price dollars of the
dialogs on it (agents/portfolio_replay.goal_dialogs) and whether the model proved or refuted it.

Usage: refute_replay.py RUN_DIR [RUN_DIR ...] --out DIR [--samples N] [--jobs J] [--threads T]
Writes DIR/refute-replay.json and prints a summary.
"""
import argparse, concurrent.futures, json, pathlib, re, shutil, sys, tempfile, threading, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness")]
import budget, fin_lib, ledger, portfolio_replay, refute, repair, task as taskmod  # noqa: E402


def introduced_with_versions(events):
    """Planner lemmas and skeleton helpers with the version of the write just before their event
    (the write that installed them); model-stated helpers with their tool event's version."""
    out, version = [], 0
    for e in events:
        k = e.get("kind")
        if k == "write":
            version = e.get("version", version)
        elif k == "plan":
            out += [(n, "plan", version, e.get("code") or "", e.get("theorem")) for n in e.get("lemmas") or []]
        elif k == "skeleton" and e.get("accepted") and e.get("source") != "resumed":
            out += [(n, "skeleton", version, e.get("code") or "", None) for n in (e.get("helpers") or {})]
        elif k == "tool" and e.get("name") == "replace_declaration":
            a = e.get("args") or {}
            text, name = a.get("text") or "", (a.get("name") or "").split(".")[-1]
            if "sorry" in text and re.match(r"(?:inserted|replaced) declaration", e.get("result") or "") \
                    and re.match(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+{re.escape(name)}\b", text):
                out.append((name, "replace_declaration", e.get("version"), text, None))
    return out


_lock = threading.Lock()


def replay_run(run_dir, samples, log):
    d = pathlib.Path(run_dir)
    summ = json.loads((d / "summary.json").read_text())
    task = taskmod.load(summ["task"])
    ev = ledger._events(d)
    lemmas = introduced_with_versions(ev)
    if not lemmas:
        return {"run_dir": str(d), "task": task.id, "arm": summ.get("arm"), "lemmas": []}
    goals = {g["goal"]: g for g in portfolio_replay.goal_dialogs(ev)}
    refuted_by_model = {e.get("name") for e in ev if e.get("kind") == "refute" and e.get("ok")}
    final = (d / "final.lean").read_text()
    ctx = {}
    for name, source, version, code, parent in lemmas:
        f = d / f"candidate_v{version:03d}.lean" if version else None
        src, approx = (f.read_text(), False) if f and f.exists() else (final, True)
        if not re.search(rf"^{repair.DECL_PREFIX}{repair.DECL_KINDS}\s+{re.escape(name)}(?=[\s:({{\[])", src, re.M):
            stmt = portfolio_replay.restated(ev, name)
            end = f"end {task.ns}"
            if not stmt or end not in src:
                ctx.setdefault(None, []).append((name, source, version, parent, approx))
                continue
            head, tail = src.rsplit(end, 1)
            src, approx = head.rstrip("\n") + "\n\n" + stmt + "\n\n" + end + tail, True
        elif approx:
            src = portfolio_replay.reopen(src, task, name)
        ctx.setdefault((src, approx), []).append((name, source, version, parent, approx))
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="pf-refute-replay-"))
    start = tmp / "start.lean"
    start.write_text(final)
    lib = bool((summ.get("library") or {}).get("enabled"))
    s = repair.Session(task, summ.get("model") or "muse-spark-1.3-contributor", start, tmp, budget.Budget(None, None),
                       library=lib)
    s.refute_samples = samples
    out = []
    try:
        for key, items in ctx.items():
            if key is None:
                for name, source, version, parent, approx in items:
                    out.append({"lemma": name, "source": source, "version": version, "status": "no statement"})
                continue
            src, approx = key
            (s.ws / "candidate/Solution.lean").write_text(src)
            names = list(dict.fromkeys(n for n, *_ in items))
            # The lemma must not use sorry in a way that hides it: sample only theorems stated with sorry.
            open_names = [n for n in names if "sorry" in repair.decl_text(s, n, src)]
            res, info = refute.run_probe(s, open_names, samples=samples) if open_names else ({}, {"ms": 0, "stopped": False})
            for name, source, version, parent, approx_ in items:
                r = res.get(name) or {"status": "proved in context" if name not in open_names else "not run"}
                g = goals.get(name, {})
                rec = {"lemma": name, "source": source, "version": version, "parent": parent,
                       "approximate_context": approx_, "statement": repair.statement_of(repair.decl_text(s, name, src))[:600],
                       **r, "probe_ms": info["ms"], "probe_stopped": info.get("stopped", False),
                       "probe_lemmas": len(open_names), "turns": g.get("turns", 0), "dialogs": g.get("dialogs", 0),
                       "usd_list": g.get("usd_list", 0.0), "proved_by_model": g.get("proved_by_model", False),
                       "refuted_by_model": name in refuted_by_model}
                if info.get("error"):
                    rec["probe_error"] = info["error"][-300:]
                out.append(rec)
                with _lock:
                    log(f"{d.parent.name}/{d.name} {source} {name}: {rec['status']} ({info['ms']} ms, {rec['turns']} turns)"
                        + (f" {rec.get('counterexample', '')[:160]}" if rec["status"] == "false" else ""))
    finally:
        shutil.rmtree(s.ws, ignore_errors=True)
        shutil.rmtree(tmp, ignore_errors=True)
    return {"run_dir": str(d), "task": task.id, "arm": summ.get("arm"), "lemmas": out}


def summarize(runs):
    rows = []
    tot = {"lemmas": 0, "sampled": 0, "false": 0, "survived": 0, "unsupported": 0, "unconfirmed": 0,
           "false_turns": 0, "false_usd": 0.0, "false_proved_by_model": 0, "all_turns": 0, "all_usd": 0.0}
    for r in runs:
        ls = r["lemmas"]
        f = [x for x in ls if x.get("status") == "false"]
        row = {"run": r["run_dir"], "task": r["task"], "lemmas": len(ls),
               "sampled": sum(1 for x in ls if x.get("status") in ("false", "survived", "unconfirmed")),
               "false": len(f), "survived": sum(1 for x in ls if x.get("status") == "survived"),
               "unsupported": sum(1 for x in ls if x.get("status") == "unsupported"),
               "unconfirmed": sum(1 for x in ls if x.get("status") == "unconfirmed"),
               "false_turns": sum(x["turns"] for x in f), "false_usd": round(sum(x["usd_list"] for x in f), 4),
               "false_proved_by_model": sum(1 for x in f if x["proved_by_model"]),
               "all_turns": sum(x.get("turns", 0) for x in ls), "all_usd": round(sum(x.get("usd_list", 0) for x in ls), 4),
               "unsupported_reasons": sorted({x.get("reason", "") for x in ls if x.get("status") == "unsupported"})[:8],
               "probe_ms": sum({(x["version"], x["probe_lemmas"]): x["probe_ms"] for x in ls if "probe_ms" in x}.values())}
        rows.append(row)
        for k in tot:
            tot[k] += row[k] if k in row else 0
    tot["false_usd"] = round(tot["false_usd"], 4)
    tot["all_usd"] = round(tot["all_usd"], 4)
    return {"runs": rows, "total": tot}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("runs", nargs="+")
    ap.add_argument("--out", required=True)
    ap.add_argument("--samples", type=int, default=refute.SAMPLES)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--threads", type=int)
    a = ap.parse_args()
    if a.threads:
        import judge
        orig = judge.in_container
        judge.in_container = lambda project, script, timeout=900: orig(
            project, f"export LEAN_NUM_THREADS={a.threads}; {script}", timeout=timeout)
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    logf = (out / "refute-replay.log").open("a")

    def log(msg):
        print(msg, flush=True)
        logf.write(msg + "\n")
        logf.flush()
    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        runs = list(ex.map(lambda d: replay_run(d, a.samples, log), a.runs))
    report = {"samples": a.samples, "library_source_tree_sha256": fin_lib.tree_sha256(),
              "elapsed_s": round(time.time() - t0, 1), **summarize(runs), "lemmas": runs}
    (out / "refute-replay.json").write_text(json.dumps(report, indent=1))
    print(json.dumps({k: report[k] for k in ("runs", "total", "elapsed_s")}, indent=1))


if __name__ == "__main__":
    main()
