#!/usr/bin/env python3
"""Ledger of every measured comparison between a Meta model alone and the same model with ProofForge.

No model calls, no Lean, no network. Every number is computed from the raw run files under
`results/` (summary.json, eval.json, passport.json, events.jsonl, mcp-calls.jsonl,
last_compiling.json, ledger.json, e1.json, e2.json); README prose is never parsed. The README
claims that are checked against the data are written out by hand in claims() below, each with
the file that states it.

    python3 eval/wins.py            # writes results/wins/ledger.json and results/wins/README.md
    python3 eval/wins.py --check    # exits 1 if the committed files differ from a fresh build

Two sources are optional and handled when present:
- results/vyper-replication-1 with runs/ and judged/ laid out as in results/hard-task-1;
- feedback-measure-1, read from results/feedback-measure-1 when it is on this branch, else
  read only from the measure-2 worktree (.claude/worktrees/measure-2/results/feedback-measure-1).
The ledger records which sources were found.
"""
import argparse, datetime, json, math, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RES = ROOT / "results"
OUT = RES / "wins"
TIE_BAND = 0.05     # a relative difference below 5% in cost or time is a tie

SPARK = "muse-spark-1.3-contributor"
ARM_LABEL = {
    "A0": "A0, the model alone (compile-and-retry: Lean errors and the axiom audit only)",
    "A1": "A1, the ProofForge harness",
    "A2": "A2, the ProofForge harness with the Muse Wonder 1.0 planner",
    "alone": "Muse Code alone (Lean through MCP, no judge, no library)",
    "proofforge": "Muse Code with ProofForge (MCP server, skill, ProofForgeFin)",
    "proofforge-full": "Muse Code with ProofForge (full MCP profile, skill, ProofForgeFin)",
}
A2_NOTE = ("A2 adds Muse Wonder 1.0 as lemma planner, a second Meta model charged to the same budget, "
           "so A2 is not the same model with ProofForge alone.")


# Files and small helpers

def rel(p):
    p = pathlib.Path(p)
    try:
        return str(p.relative_to(ROOT))
    except ValueError:
        parts = p.parts
        if ".claude" in parts:
            return str(pathlib.Path(*parts[parts.index(".claude"):]))
        return str(p)


def load(p):
    return json.loads(pathlib.Path(p).read_text())


def events(p):
    p = pathlib.Path(p)
    if not p.exists():
        return []
    out = []
    for line in p.read_text().splitlines():
        line = line.strip()
        if line:
            try:
                out.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return out


def r2(x):
    return None if x is None else round(x, 2)


def r4(x):
    return None if x is None else round(x, 4)


def rp(p):
    """A p-value to four significant digits."""
    return None if p is None else float(f"{p:.4g}")


def mean(xs):
    xs = [x for x in xs if x is not None]
    return sum(xs) / len(xs) if xs else None


def epoch(started):
    return datetime.datetime.strptime(started, "%Y-%m-%dT%H:%M:%S%z").timestamp()


def passport_info(p):
    """(status, sha256, verified requirement count, requirement count) of a Passport file."""
    d = load(p)
    reqs = d.get("requirements") or []
    if isinstance(reqs, dict):
        statuses = [v.get("status") if isinstance(v, dict) else v for v in reqs.values()]
    else:
        statuses = [r.get("status") for r in reqs]
    return d["status"], d["passport_sha256"], sum(s == "VERIFIED" for s in statuses), len(statuses)


# Statistics (exact, no dependencies)

def fisher_one_sided(pf_v, pf_n, al_v, al_n):
    """P(X >= pf_v) for the ProofForge arm's verified count under the hypergeometric null."""
    n, k = pf_n + al_n, pf_v + al_v
    tot = math.comb(n, pf_n)
    return sum(math.comb(k, x) * math.comb(n - k, pf_n - x) for x in range(pf_v, min(k, pf_n) + 1)) / tot


def mcnemar_exact(b, c):
    """Two-sided exact McNemar test on the discordant pairs, as eval/e1.py computes it."""
    n = b + c
    if n == 0:
        return 1.0
    p = sum(math.comb(n, i) for i in range(min(b, c) + 1)) / 2 ** n
    return min(1.0, 2 * p)


def mann_whitney_less(xs, ys):
    """One-sided exact p of H1 'xs tend to be smaller than ys' (midranks, permutation distribution)."""
    allv = sorted(xs + ys)
    rank = {}
    i = 0
    while i < len(allv):
        j = i
        while j < len(allv) and allv[j] == allv[i]:
            j += 1
        rank[allv[i]] = i + j + 1          # twice the midrank, an integer
        i = j
    r2s = [rank[v] for v in allv]
    m = len(xs)
    obs = sum(rank[v] for v in xs)
    dist = [dict() for _ in range(m + 1)]  # dist[c][sum] = ways
    dist[0][0] = 1
    for r in r2s:
        for c in range(m, 0, -1):
            for s, w in dist[c - 1].items():
                dist[c][s + r] = dist[c].get(s + r, 0) + w
    tot = sum(dist[m].values())
    return sum(w for s, w in dist[m].items() if s <= obs) / tot


# Run loaders

def agent_run(d, verified_by):
    """A run of agents/baseline.py (A0) or agents/repair.py (A1, A2)."""
    d = pathlib.Path(d)
    s = load(d / "summary.json")
    b = s["budget"]
    fs = s.get("final_status") or {}
    run = {"dir": rel(d), "arm": s["arm"], "model": s["model"],
           "planner": s.get("planner"), "mode": s.get("task_mode") or "repair",
           "usd_cap": b["usd_cap"], "wall_cap_s": b["wall_cap_s"],
           "list_usd": r4(b["usd_list"]), "charged_usd": r4(b["usd_actual"]), "wall_s": b["elapsed_s"],
           "stop": b["stop"], "req_total": len(fs)}
    evs = events(d / "events.jsonl")
    start = next((e["t"] for e in evs if e.get("kind") == "start"), None)
    judged = next((e["t"] for e in evs if e.get("kind") == "judge" and e.get("accepted")), None)
    if verified_by == "eval":
        ev = load(d / "eval.json")
        run["verified"] = bool(ev["completed"])
        run["status"] = f"judge {ev['judge']}, binary {ev['binary']}"
        run["list_usd"], run["charged_usd"], run["wall_s"], run["stop"] = r4(ev["usd_list"]), r4(ev["usd_actual"]), ev["elapsed_s"], ev["stop"]
        judges = sorted(p.name for p in d.glob("judge_v*.json"))
        run["evidence"] = {"judge_record": rel(d / judges[-1]) if judges else None, "final_sha256": ev["final_sha256"]}
    else:
        pp = d / "passport.json"
        if pp.exists():
            st, sha, nv, nt = passport_info(pp)
            run["verified"] = st == "VERIFIED"
            run["status"] = st
            run["evidence"] = {"passport": rel(pp), "passport_sha256": sha}
        else:
            run["verified"] = False
            run["status"] = "no Passport; accepted in session" if s.get("accepted_in_session") else "no Passport; not accepted in session"
            run["evidence"] = None
    run["req_proved"] = run["req_total"] if run["verified"] else sum(v == "PROVED" for v in fs.values())
    run["req_source"] = "Passport" if run["verified"] else "summary.json final_status (the run's own check of its final snapshot)"
    lg = d / "ledger.json"
    if not run["verified"] and lg.exists():
        best = load(lg).get("best_candidate") or {}
        if best.get("proved_required") is not None:
            run["req_proved"] = len(best["proved_required"])
            run["req_source"] = f"ledger.json best_candidate ({best.get('version')})"
    run["first_verified_s"] = round(judged - start, 1) if (run["verified"] and judged and start) else None
    run["first_verified_method"] = "first accepted judge event in events.jsonl" if run["first_verified_s"] is not None else None
    if s.get("resume"):
        run["resumed_from_proved"] = (s["resume"].get("base") or {}).get("proved")
    return run


def muse_code_run(d, judged=None):
    """A run of agents/muse_code.py; the official check is judged/<task>/<run>/passport.json when given."""
    d = pathlib.Path(d)
    s = load(d / "summary.json")
    m = s["meter"]
    pdir = pathlib.Path(judged) if judged else d
    st, sha, nv, nt = passport_info(pdir / "passport.json")
    verified = st == "VERIFIED"
    run = {"dir": rel(d), "arm": s["arm"], "model": s["model"], "planner": None, "mode": "repair",
           "usd_cap": s["budget_usd"], "wall_cap_s": s["budget_wall_s"],
           "list_usd": r4(m["usd_list"]), "charged_usd": r4(m["usd_actual"]), "wall_s": s["elapsed_s"],
           "stop": s["stop"] if s["stop"] in ("usd", "wall") else s["stop"], "verified": verified, "status": st,
           "req_total": nt, "evidence": {"passport": rel(pdir / "passport.json"), "passport_sha256": sha}}
    if verified:
        run["req_proved"], run["req_source"] = nt, "Passport"
    elif (d / "last_compiling.json").exists():
        lc = load(d / "last_compiling.json")
        run["req_proved"], run["req_source"] = lc["proved"], f"last_compiling.json ({lc['snapshot']})"
    elif (d / "ledger.json").exists():
        best = load(d / "ledger.json").get("best_candidate") or {}
        run["req_proved"], run["req_source"] = len(best.get("proved_required") or []), f"ledger.json best_candidate ({best.get('version')})"
    else:
        run["req_proved"], run["req_source"] = s.get("requirements_proved_in_run", 0), "summary.json requirements_proved_in_run"
    run["first_verified_s"], run["first_verified_method"] = None, None
    if verified:
        first = None
        for e in events(d / "mcp-calls.jsonl"):
            if e.get("tool") == "check_candidate" and not e.get("error"):
                try:
                    if json.loads(e["result"]).get("status") == "VERIFIED":
                        first = e["t"]
                        break
                except (json.JSONDecodeError, TypeError):
                    if '"status": "VERIFIED"' in str(e.get("result")):
                        first = e["t"]
                        break
        if first is not None:
            run["first_verified_s"] = round(first - epoch(s["started"]), 1)
            run["first_verified_method"] = "end of the first check_candidate call returning VERIFIED (mcp-calls.jsonl)"
        elif s.get("ended_by") == "accepted":
            run["first_verified_s"] = s["elapsed_s"]
            run["first_verified_method"] = "end of run: the runner's judge accepted the candidate (summary.json elapsed_s)"
    return run


# Arms and comparisons

def arm(name, runs, label=None, price_basis="list"):
    v = [r for r in runs if r["verified"]]
    lt = sum(r["list_usd"] for r in runs)
    caps = sorted({(r["usd_cap"], r["wall_cap_s"]) for r in runs})
    return {
        "arm": name, "label": label or ARM_LABEL.get(name, name), "price_basis": price_basis,
        "runs": len(runs), "verified": len(v),
        "caps": [{"usd": c[0], "wall_s": c[1]} for c in caps],
        "list_usd_total": r2(lt), "list_usd_per_verified": r2(lt / len(v)) if v else None,
        "charged_usd_total": r4(sum(r["charged_usd"] for r in runs)),
        "wall_s_mean": r2(mean([r["wall_s"] for r in runs])), "wall_s_total": r2(sum(r["wall_s"] for r in runs)),
        "wall_s_mean_verified": r2(mean([r["wall_s"] for r in v])),
        "wall_s_per_run": [r["wall_s"] for r in runs],
        "first_verified_s": [r["first_verified_s"] for r in v],
        "first_verified_s_mean": r2(mean([r["first_verified_s"] for r in v])),
        "cap_stops": {"usd": sum(r["stop"] == "usd" for r in runs), "wall": sum(r["stop"] == "wall" for r in runs)},
        "req_total": max((r["req_total"] for r in runs), default=0),
        "req_proved_per_run": [r["req_proved"] for r in runs],
        "req_proved_mean": r2(mean([r["req_proved"] for r in runs])),
        "passports": [r["evidence"]["passport_sha256"][:16] for r in v if r.get("evidence") and r["evidence"].get("passport_sha256")],
        "judge_records": [r["evidence"]["judge_record"] for r in v if r.get("evidence") and r["evidence"].get("judge_record")],
        "run_dirs": [r["dir"] for r in runs],
        "_runs": runs,
    }


def lower_is_better(pf, al):
    if pf is None or al is None:
        return "n/a", None
    if al == 0 and pf == 0:
        return "tie", None
    if pf == 0:
        return "win", None
    f = al / pf
    if abs(pf - al) <= TIE_BAND * max(pf, al):
        return "tie", round(f, 2)
    return ("win" if pf < al else "loss"), round(f, 2)


def higher_is_better(pf, al):
    if pf is None or al is None:
        return "n/a"
    return "win" if pf > al else "loss" if pf < al else "tie"


def classify(al, pf):
    c, f = {}, {}
    c["verification"] = higher_is_better(pf["verified"] / pf["runs"], al["verified"] / al["runs"])
    if pf["verified"] and al["verified"]:
        c["cost"], f["cost"] = lower_is_better(pf["list_usd_per_verified"], al["list_usd_per_verified"])
        c["time"], f["time"] = lower_is_better(pf["wall_s_mean_verified"], al["wall_s_mean_verified"])
    elif pf["verified"]:
        c["cost"], c["time"] = "win", "n/a"
    elif al["verified"]:
        c["cost"], c["time"] = "loss", "n/a"
    else:
        c["cost"], c["time"] = "n/a", "n/a"
    c["requirements"] = higher_is_better(pf["req_proved_mean"], al["req_proved_mean"])
    sa, sp = sum(al["cap_stops"].values()) / al["runs"], sum(pf["cap_stops"].values()) / pf["runs"]
    c["cap_stops"] = "win" if sp < sa else "loss" if sp > sa else "tie"
    return c, f


def comparison(cid, experiment, task, model, al, pf, scope="task", test=None, caveats=(), sources=(), flags=(), time_mode="task", pairs=None):
    """time_mode: 'task' compares the mean wall time of verified runs of one task; 'paired' compares it on the
    paired tasks both arms verified (E1 aggregates); 'none' leaves time out (aggregates over several tasks
    with unpaired runs, where the verified runs are of different tasks)."""
    c, f = classify(al, pf)
    paired = None
    if time_mode == "paired":
        both = [(a, b) for a, b in pairs if a["verified"] and b["verified"]]
        paired = {"tasks_both_verified": len(both),
                  "alone_wall_s_mean": r2(mean([a["wall_s"] for a, _ in both])), "proofforge_wall_s_mean": r2(mean([b["wall_s"] for _, b in both])),
                  "alone_list_usd_mean": r4(mean([a["list_usd"] for a, _ in both])), "proofforge_list_usd_mean": r4(mean([b["list_usd"] for _, b in both]))}
        if both:
            c["time"], f["time"] = lower_is_better(paired["proofforge_wall_s_mean"], paired["alone_wall_s_mean"])
        else:
            c["time"], f["time"] = "n/a", None
    elif time_mode == "none":
        c["time"] = "n/a"
        f.pop("time", None)
    equal = al["caps"] == pf["caps"]
    flags = list(flags)
    if not equal:
        flags.append("different budgets")
    if pf["arm"] == "A2" or "A2" in pf["arm"]:
        flags.append("second model in the ProofForge arm (Muse Wonder planner)")
    return {"id": cid, "experiment": experiment, "task": task, "model": model, "scope": scope,
            "alone": al, "proofforge": pf, "equal_caps": equal, "test": test,
            "time_basis": {"task": "mean wall time of the verified runs", "paired": "mean wall time on the paired tasks both arms verified",
                           "none": "not compared: the verified runs are of different tasks"}[time_mode], "paired_both_verified": paired,
            "classification": c, "factors": f, "flags": flags, "caveats": list(caveats),
            "sources": sorted(set(sources) | set(al["run_dirs"]) | set(pf["run_dirs"]))}


# Experiments

def muse_code_1():
    base = RES / "muse-code-1"
    out, alls, pfs = [], [], []
    cav = ["The ProofForge arm's in-run time includes its own official checks (check_candidate and verify_passport, 50 to 236 s each); Muse Code alone sees only Lean (results/muse-code-1/README.md).",
           "Up to four runs ran at once and shared four Lean container slots with other work, so wall times include waiting for a slot.",
           "Every unverified run stopped on the dollar rule with $2.06 to $3.02 of the $10 unspent: the next call's worst-case byte bound no longer fit.",
           "The demonstration runs (demo-balancer-1, demo-balancer-2) and smoke runs are not part of the comparison.",
           "Muse Code alone was faster on Knight and Cetus and cheaper on Knight; those rows are losses for ProofForge in the table."]
    for task in ("rw-balancer-upscale", "rc-knight-router", "rw-cetus-shlw", "rw-compound-comp"):
        al = [muse_code_run(d) for d in sorted((base / task).glob("alone-*"))]
        pf = [muse_code_run(d) for d in sorted((base / task).glob("proofforge-*"))]
        alls += al
        pfs += pf
        test = None
        if task == "rw-balancer-upscale":
            test = {"name": "one-sided Fisher exact", "p": rp(fisher_one_sided(sum(r["verified"] for r in pf), len(pf), sum(r["verified"] for r in al), len(al))),
                    "preregistered": False, "stated_in": "results/muse-code-1/README.md", "significant_at_0_05": False}
        out.append(comparison(f"muse-code-1/{task}", "muse-code-1", task, SPARK, arm("alone", al), arm("proofforge", pf),
                              test=test, caveats=cav, sources=["results/muse-code-1/README.md"]))
    out.append(comparison("muse-code-1/all-four", "muse-code-1", "all four tasks", SPARK, arm("alone", alls), arm("proofforge", pfs),
                          scope="aggregate", time_mode="none", caveats=cav,
                          sources=["results/muse-code-1/README.md"]))
    return out


def hard_task_runs(base, task):
    runs = {}
    for a in ("alone", "proofforge-full"):
        runs[a] = [muse_code_run(d, base / "judged" / task / d.name) for d in sorted((base / "runs" / task).glob(f"{a}-*"))
                   if (base / "judged" / task / d.name / "passport.json").exists()]
    return runs


def hard_task_1():
    base = RES / "hard-task-1"
    out, pooled = [], {"alone": [], "proofforge-full": []}
    cav = ["Preregistered (results/hard-task-1/PREREGISTRATION.md, plan commit 54bf8cc): 5 runs per arm per task, one-sided Fisher exact test, alpha 0.05; with 5 runs per arm only a difference of four reaches p < 0.05.",
           "ProofForgeFin.Sqrt was written by the build team knowing both tasks; a gap between the arms is the contribution of ProofForge including this module.",
           "Final candidates judged again outside the budget from commit baa38a0 (judged/<task>/<run>/passport.json); no run set aside, none rerun."]
    for task in ("rw-vyper-sqrt", "rw-oz-sqrt"):
        runs = hard_task_runs(base, task)
        al, pf = runs["alone"], runs["proofforge-full"]
        pooled["alone"] += al
        pooled["proofforge-full"] += pf
        p = fisher_one_sided(sum(r["verified"] for r in pf), len(pf), sum(r["verified"] for r in al), len(al))
        test = {"name": "one-sided Fisher exact", "p": rp(p), "preregistered": True, "alpha": 0.05,
                "stated_in": "results/hard-task-1/PREREGISTRATION.md", "significant_at_0_05": p < 0.05}
        extra = []
        if task == "rw-oz-sqrt":
            extra = ["On rw-oz-sqrt the alone arm kept more required theorems proved in its last compiling version, and four of five ProofForge final candidates do not build (results/hard-task-1/README.md)."]
        out.append(comparison(f"hard-task-1/{task}", "hard-task-1", task, SPARK, arm("alone", al), arm("proofforge-full", pf),
                              test=test, caveats=cav + extra, sources=["results/hard-task-1/README.md", "results/hard-task-1/PREREGISTRATION.md"]))
    p = fisher_one_sided(sum(r["verified"] for r in pooled["proofforge-full"]), len(pooled["proofforge-full"]),
                         sum(r["verified"] for r in pooled["alone"]), len(pooled["alone"]))
    out.append(comparison("hard-task-1/both-tasks", "hard-task-1", "rw-vyper-sqrt and rw-oz-sqrt", SPARK,
                          arm("alone", pooled["alone"]), arm("proofforge-full", pooled["proofforge-full"]), scope="aggregate", time_mode="none",
                          test={"name": "one-sided Fisher exact (secondary, pooled)", "p": rp(p), "preregistered": True, "alpha": 0.05,
                                "stated_in": "results/hard-task-1/PREREGISTRATION.md", "significant_at_0_05": p < 0.05},
                          caveats=cav, sources=["results/hard-task-1/README.md"]))
    return out, pooled


def vyper_replication_1(hard_pooled):
    base = RES / "vyper-replication-1"
    task = "rw-vyper-sqrt"
    if not (base / "runs" / task).is_dir():
        return [], {"source": "results/vyper-replication-1", "found": False,
                    "note": "only PREREGISTRATION.md is on this branch; the runs are being measured; the comparison is added when runs/ and judged/ land"}
    runs = hard_task_runs(base, task)
    al, pf = runs["alone"], runs["proofforge-full"]
    if not al or not pf:
        return [], {"source": "results/vyper-replication-1", "found": False, "note": "runs/ present but no judged run of both arms"}
    complete = len(al) == 10 and len(pf) == 10
    cav = ["Preregistered (results/vyper-replication-1/PREREGISTRATION.md): 10 runs per arm, one-sided Fisher exact test on this experiment's 20 runs alone, alpha 0.05.",
           "rw-vyper-sqrt was chosen after the hard-task-1 results; the pooled comparison includes the runs that motivated this experiment and is secondary."]
    if not complete:
        cav.append(f"Incomplete: {len(al)} alone and {len(pf)} ProofForge runs judged of the 10 per arm preregistered.")
    p = fisher_one_sided(sum(r["verified"] for r in pf), len(pf), sum(r["verified"] for r in al), len(al))
    mw = mann_whitney_less([r["list_usd"] for r in pf], [r["list_usd"] for r in al])
    out = [comparison(f"vyper-replication-1/{task}", "vyper-replication-1", task, SPARK, arm("alone", al), arm("proofforge-full", pf),
                      test={"name": "one-sided Fisher exact", "p": rp(p), "preregistered": True, "alpha": 0.05,
                            "stated_in": "results/vyper-replication-1/PREREGISTRATION.md", "significant_at_0_05": p < 0.05,
                            "secondary": {"name": "one-sided Mann-Whitney U, ProofForge spends fewer list dollars per run", "p": rp(mw)}},
                      caveats=cav, flags=[] if complete else ["incomplete"], sources=["results/vyper-replication-1/README.md", "results/vyper-replication-1/PREREGISTRATION.md"])]
    hv = [r for r in hard_pooled["alone"] if "rw-vyper-sqrt" in r["dir"]]
    hp = [r for r in hard_pooled["proofforge-full"] if "rw-vyper-sqrt" in r["dir"]]
    al2, pf2 = al + hv, pf + hp
    p2 = fisher_one_sided(sum(r["verified"] for r in pf2), len(pf2), sum(r["verified"] for r in al2), len(al2))
    out.append(comparison(f"vyper-replication-1/{task}+hard-task-1", "vyper-replication-1", task, SPARK, arm("alone", al2), arm("proofforge-full", pf2),
                          scope="aggregate", test={"name": "one-sided Fisher exact (secondary, includes the motivating hard-task-1 runs)", "p": rp(p2),
                                                   "preregistered": True, "stated_in": "results/vyper-replication-1/PREREGISTRATION.md", "significant_at_0_05": p2 < 0.05},
                          caveats=cav, flags=["includes the runs that motivated the experiment"], sources=["results/vyper-replication-1/README.md", "results/vyper-replication-1/PREREGISTRATION.md"]))
    return out, {"source": "results/vyper-replication-1", "found": True, "complete": complete}


def frontier_2():
    base = RES / "frontier-2"
    out, pooled = [], {"alone": [], "proofforge-full": []}
    src = ["results/frontier-2/README.md", "results/frontier-2/PREREGISTRATION.md"]
    cav = ["Preregistered (results/frontier-2/PREREGISTRATION.md, commit 995ee6e): 10 runs per arm per task, one-sided Fisher exact test per task, alpha 0.025 per task (two tasks).",
           "The ProofForgeFin modules the ProofForge arm imports (SqrtIter, WordBridge, NatSqrt, Accumulator) were written after earlier runs on these two tasks failed; a gap between the arms measures ProofForge including that library work.",
           "Final candidates judged again outside the budget from commit 995ee6e (judged/<task>/<run>/passport.json); every Passport reproduced; no run set aside, none rerun."]
    for task in ("rw-oz-sqrt", "rw-compound-comp"):
        runs = hard_task_runs(base, task)
        al, pf = runs["alone"], runs["proofforge-full"]
        if not al or not pf:
            continue
        pooled["alone"] += al
        pooled["proofforge-full"] += pf
        p = fisher_one_sided(sum(r["verified"] for r in pf), len(pf), sum(r["verified"] for r in al), len(al))
        test = {"name": "one-sided Fisher exact", "p": rp(p), "preregistered": True, "alpha": 0.025,
                "stated_in": "results/frontier-2/PREREGISTRATION.md", "significant_at_0_05": p < 0.05}
        if task == "rw-oz-sqrt":
            test["secondary"] = {"name": "one-sided Mann-Whitney U, ProofForge spends fewer list dollars per run",
                                 "p": rp(mann_whitney_less([r["list_usd"] for r in pf], [r["list_usd"] for r in al]))}
        out.append(comparison(f"frontier-2/{task}", "frontier-2", task, SPARK, arm("alone", al), arm("proofforge-full", pf),
                              test=test, caveats=cav, sources=src))
    if not out:
        return [], {"source": "results/frontier-2", "found": False, "note": "no judged run of both arms"}
    p = fisher_one_sided(sum(r["verified"] for r in pooled["proofforge-full"]), len(pooled["proofforge-full"]),
                         sum(r["verified"] for r in pooled["alone"]), len(pooled["alone"]))
    out.append(comparison("frontier-2/both-tasks", "frontier-2", "rw-oz-sqrt and rw-compound-comp", SPARK,
                          arm("alone", pooled["alone"]), arm("proofforge-full", pooled["proofforge-full"]), scope="aggregate", time_mode="none",
                          test={"name": "one-sided Fisher exact (secondary, pooled)", "p": rp(p), "preregistered": True,
                                "stated_in": "results/frontier-2/PREREGISTRATION.md", "significant_at_0_05": p < 0.05},
                          caveats=cav, sources=src))
    return out, {"source": "results/frontier-2", "found": True, "complete": all(c["alone"]["runs"] == 10 and c["proofforge"]["runs"] == 10 for c in out if c["scope"] == "task")}


def frontier_3():
    base = RES / "frontier-3"
    task = "rw-compound-comp"
    src = ["results/frontier-3/README.md", "results/frontier-3/PREREGISTRATION.md"]
    cav = ["Preregistered (results/frontier-3/PREREGISTRATION.md, commit a3a1307): 10 runs per arm, one-sided Fisher exact test, alpha 0.05; with 0 verified on its own, p < 0.05 needs at least 4 verified with ProofForge.",
           "ProofForgeFin.Accumulator.Market was written after the frontier-2 runs on this task stopped at 5 of 8 requirements; a gap between the arms measures ProofForge including that library work.",
           "Final candidates judged again outside the budget from commit a3a1307 (judged/<task>/<run>/passport.json); every Passport reproduced; no run set aside, none rerun."]
    if not (base / "judged" / task).is_dir():
        return [], {"source": "results/frontier-3", "found": False, "note": "no judged run"}
    runs = hard_task_runs(base, task)
    al, pf = runs["alone"], runs["proofforge-full"]
    if not al or not pf:
        return [], {"source": "results/frontier-3", "found": False, "note": "no judged run of both arms"}
    p = fisher_one_sided(sum(r["verified"] for r in pf), len(pf), sum(r["verified"] for r in al), len(al))
    out = [comparison(f"frontier-3/{task}", "frontier-3", task, SPARK, arm("alone", al), arm("proofforge-full", pf),
                      test={"name": "one-sided Fisher exact", "p": rp(p), "preregistered": True, "alpha": 0.05,
                            "stated_in": "results/frontier-3/PREREGISTRATION.md", "significant_at_0_05": p < 0.05},
                      caveats=cav, sources=src)]
    f2 = hard_task_runs(RES / "frontier-2", task)["alone"]
    if f2:
        pooled = al + f2
        p = fisher_one_sided(sum(r["verified"] for r in pf), len(pf), sum(r["verified"] for r in pooled), len(pooled))
        out.append(comparison(f"frontier-3+frontier-2/{task}", "frontier-3", task, SPARK, arm("alone", pooled), arm("proofforge-full", pf),
                              scope="aggregate", test={"name": "one-sided Fisher exact (secondary, frontier-2 and frontier-3 runs on its own pooled)", "p": rp(p),
                                                       "preregistered": True, "stated_in": "results/frontier-3/PREREGISTRATION.md", "significant_at_0_05": p < 0.05},
                              caveats=cav + ["The runs on its own pool frontier-2 (commit 995ee6e) and frontier-3 (commit a3a1307); the alone arm is the same in both."],
                              sources=src + ["results/frontier-2/README.md"]))
    return out, {"source": "results/frontier-3", "found": True, "complete": len(al) == 10 and len(pf) == 10}


def frontier_4():
    base = RES / "frontier-4"
    task = "rw-compound-comp"
    src = ["results/frontier-4/README.md", "results/frontier-4/PREREGISTRATION.md"]
    cav = ["Preregistered (results/frontier-4/PREREGISTRATION.md, commit dbc2c01): 10 runs per arm, one-sided Fisher exact test, alpha 0.05.",
           "The full toolset's build feedback, the skill's steps and the ProofForgeFin additions were built from the frontier-3 ProofForge runs on this task; a gap between the arms measures ProofForge including that work. The alone arm has none of it.",
           "Final candidates judged again outside the budget from commit dbc2c01 (judged/<task>/<run>/passport.json); every Passport reproduced; no run set aside, none rerun."]
    if not (base / "judged" / task).is_dir():
        return [], {"source": "results/frontier-4", "found": False, "note": "no judged run"}
    runs = hard_task_runs(base, task)
    al, pf = runs["alone"], runs["proofforge-full"]
    if not al or not pf:
        return [], {"source": "results/frontier-4", "found": False, "note": "no judged run of both arms"}
    k = sum(r["verified"] for r in pf)
    p = fisher_one_sided(k, len(pf), sum(r["verified"] for r in al), len(al))
    f3 = hard_task_runs(RES / "frontier-3", task)
    f3pf = f3["proofforge-full"]
    test = {"name": "one-sided Fisher exact", "p": rp(p), "preregistered": True, "alpha": 0.05,
            "stated_in": "results/frontier-4/PREREGISTRATION.md", "significant_at_0_05": p < 0.05}
    if f3pf:
        test["secondary"] = {"name": "one-sided Fisher exact, this ProofForge arm against the frontier-3 ProofForge arm (two versions of ProofForge run at different times)",
                             "p": rp(fisher_one_sided(k, len(pf), sum(r["verified"] for r in f3pf), len(f3pf)))}
    out = [comparison(f"frontier-4/{task}", "frontier-4", task, SPARK, arm("alone", al), arm("proofforge-full", pf),
                      test=test, caveats=cav, sources=src)]
    pooled = al + f3["alone"] + hard_task_runs(RES / "frontier-2", task)["alone"]
    if len(pooled) > len(al):
        p = fisher_one_sided(k, len(pf), sum(r["verified"] for r in pooled), len(pooled))
        out.append(comparison(f"frontier-4+frontier-3+frontier-2/{task}", "frontier-4", task, SPARK, arm("alone", pooled), arm("proofforge-full", pf),
                              scope="aggregate", test={"name": "one-sided Fisher exact (secondary, frontier-2, frontier-3 and frontier-4 runs on its own pooled)", "p": rp(p),
                                                       "preregistered": True, "stated_in": "results/frontier-4/PREREGISTRATION.md", "significant_at_0_05": p < 0.05},
                              caveats=cav + ["The runs on its own pool frontier-2 (commit 995ee6e), frontier-3 (commit a3a1307) and frontier-4 (commit dbc2c01); the alone arm is the same in all three."],
                              sources=src + ["results/frontier-3/README.md", "results/frontier-2/README.md"]))
    return out, {"source": "results/frontier-4", "found": True, "complete": len(al) == 10 and len(pf) == 10}


def hard_task_2():
    base = RES / "hard-task-2"
    task = "rw-kyber-swapstep"
    src = ["results/hard-task-2/README.md", "results/hard-task-2/PREREGISTRATION.md"]
    cav = ["Preregistered (results/hard-task-2/PREREGISTRATION.md, frozen at commit 0b70403): 10 runs per arm, one-sided Fisher exact test, alpha 0.05.",
           "ProofForgeFin.QuadRoot was written for this task by the build team before any model call on it; a gap between the arms measures ProofForge including that library work.",
           "Final candidates judged again outside the budget from commit 0b70403 (judged/<task>/<run>/passport.json); every Passport reproduced; no run set aside, none rerun."]
    if not (base / "judged" / task).is_dir():
        return [], {"source": "results/hard-task-2", "found": False, "note": "no judged run"}
    runs = hard_task_runs(base, task)
    al, pf = runs["alone"], runs["proofforge-full"]
    if not al or not pf:
        return [], {"source": "results/hard-task-2", "found": False, "note": "no judged run of both arms"}
    p = fisher_one_sided(sum(r["verified"] for r in pf), len(pf), sum(r["verified"] for r in al), len(al))
    out = [comparison(f"hard-task-2/{task}", "hard-task-2", task, SPARK, arm("alone", al), arm("proofforge-full", pf),
                      test={"name": "one-sided Fisher exact", "p": rp(p), "preregistered": True, "alpha": 0.05,
                            "stated_in": "results/hard-task-2/PREREGISTRATION.md", "significant_at_0_05": p < 0.05},
                      caveats=cav, sources=src)]
    return out, {"source": "results/hard-task-2", "found": True, "complete": len(al) == 10 and len(pf) == 10}


E1 = {
    "e1-test-1": {"pf_arms": ("A1", "A2"), "price": "list", "caveats": [
        "The 30 test tasks are 9 base specifications with 3 or 4 variants each, so the tasks are not independent problems.",
        "McNemar exact p as computed by the experiment's evaluator (eval/e1.py) and reported in results/e1-test-1/e1.md; not preregistered in a committed document.",
        "Run from an isolated checkout under results/test-freeze.json; all 90 runs completed, none set aside (results/README.md)."]},
    "e1-test-open-1": {"pf_arms": ("A1",), "price": "list", "caveats": [
        "Meta's open-weight Muse Spark Open (meta-models/muse-spark-open-1026) through Baseten Model APIs; run from an isolated checkout at commit 36fc8d3; the directory has no README (results/README.md describes it).",
        "The 30 test tasks are 9 base specifications with variants, not independent problems.",
        "McNemar exact p from eval/e1.py (results/e1-test-open-1/e1.md); not preregistered in a committed document."]},
    "e1-test-open-2": {"pf_arms": ("A1",), "price": "list", "rerun": "e1-test-open-2-rerun",
                       "preregistered": True, "caveats": [
        "Meta's open-weight Muse Spark Open through Baseten Model APIs: 18 tasks on meta-models/muse-spark-open-1026 from a worktree at commit 57d1ed5; the other 12 rerun on meta-models/muse-spark-open from a worktree at b81133a after the provider refused the first runs with HTTP 402 (Addenda 1 to 3 of results/e1-test-open-2/PREREGISTRATION.md). Both arms of each task use the same model ID.",
        "The 30 test tasks are 9 base specifications with variants, not independent problems.",
        "The repair-agent changes measured here were made knowing these test tasks and A1's failures on them in e1-test-open-1 (PREREGISTRATION.md).",
        "Primary analysis as preregistered: two-sided exact McNemar on the 30 paired tasks (results/e1-test-open-2/e1.md). The 24 refused runs stay in results/e1-test-open-2 and are not scored."]},
    "e1-test-glimmer-1": {"pf_arms": ("A1",), "price": "GPU-cost price per token (agents/budget.py), not a list price",
                          "outage": {("permissions-grants-b1", "A1"), ("permissions-grants-b2", "A1"), ("permissions-grants-b3", "A1")},
                          "caveats": [
        "Incomplete: Modal paused the workspace at 12:33 UTC after 31 of 60 runs were scored; 27 runs never started (results/e1-test-glimmer-1/README.md).",
        "Excluded as the README states: permissions-grants-b1, -b2 and -b3 A1 (ended by the outage) and permissions-grants-b3 and -b4 A0 (interrupted, no summary). Only tasks with both arms scored and neither excluded are paired.",
        "Dollars are at a GPU-cost price per token derived from measured throughput, not list prices.",
        "No A0 version compiled in any run; 13 of 15 A0 runs ended at the baseline's 200-turn limit before either cap."]},
    "e1-dev-2": {"pf_arms": ("A1", "A2"), "price": "list", "caveats": [
        "Development tasks: the harness was developed on this split and these runs were used to set the test-run caps; not held out.",
        "Caps $3 and 2,700 s per run; McNemar exact p from eval/e1.py (results/e1-dev-2/e1.md)."]},
    "e1-dev-1": {"pf_arms": ("A1", "A2"), "price": "list", "caveats": [
        "Development tasks, before the repair-agent fix in commit f8e0e6d; two runs lost to network timeouts (results/README.md).",
        "The run found a defect in the A1 repair loop: each of the 11 scored A1 runs that did not verify ended by itself, with no cap reached, after $0.39 to $0.88 of the $3 budget, 4 of them with a final file that does not build. Commit f8e0e6d (transactional theorem banking, restore of the last compiling version, progress rounds, a whole-file phase for the remaining budget) fixed it; on the same 23 tasks after the fix (e1-dev-2) A1 verified 20 and A0 19, with no task verified by A0 alone.",
        "Caps $3 and 2,700 s per run; McNemar exact p from eval/e1.py (results/e1-dev-1/e1.md)."]},
}


def e1(label):
    spec = E1[label]
    base = RES / label
    cfg = load(base / "config.json")
    model = cfg["model"]
    runs, lost, totals = {}, [], {}
    dirs = sorted(base.glob("*/*"))
    if "rerun" in spec:       # the rerun's runs replace the original runs of its tasks
        rr = sorted((RES / spec["rerun"]).glob("*/*"))
        redo = {d.parent.name for d in rr if (d / "eval.json").exists()}
        dirs = [d for d in dirs if d.parent.name not in redo] + rr
    for d in dirs:
        if not (d.is_dir() and (d / "eval.json").exists()):
            continue
        ev = load(d / "eval.json")
        key = (d.parent.name, d.name)
        if key not in spec.get("outage", set()):
            tot = totals.setdefault(d.name, {"scored": 0, "completed": 0})
            tot["scored"] += 1
            tot["completed"] += bool(ev["completed"])
        if ev["judge"] == "MISSING" or not (d / "summary.json").exists():
            lost.append(rel(d))       # lost to infrastructure: no summary, no verdict
            continue
        if key in spec.get("outage", set()):
            continue
        runs[key] = agent_run(d, "eval")
    tasks = sorted({t for t, _ in runs})
    models = sorted({r["model"] for r in runs.values()})
    report = spec.get("report", label)
    out = []
    if lost:
        spec = dict(spec, caveats=spec["caveats"] + [f"Set aside here, lost to network timeouts with no verdict (eval.json judge MISSING, no summary.json): {', '.join(lost)}. eval/e1.py counts them as not completed."])
    flags = ["incomplete"] if label == "e1-test-glimmer-1" else []
    if label.startswith("e1-dev"):
        flags.append("development tasks")
    if label == "e1-dev-1":
        flags.append("repair-loop defect fixed in f8e0e6d; rerun on the same tasks as e1-dev-2")
    for pa in spec["pf_arms"]:
        paired = [t for t in tasks if (t, "A0") in runs and (t, pa) in runs]
        cav = spec["caveats"] + ([A2_NOTE] if pa == "A2" else [])
        for t in paired:
            src = pathlib.Path(runs[(t, pa)]["dir"]).parts[1]
            out.append(comparison(f"{label}/{t}/{pa}-vs-A0", label, t, runs[(t, pa)]["model"], arm("A0", [runs[(t, "A0")]], price_basis=spec["price"]),
                                  arm(pa, [runs[(t, pa)]], price_basis=spec["price"]), caveats=cav, flags=flags,
                                  sources=[f"results/{src}/e1.json"]))
        b = sum(runs[(t, pa)]["verified"] and not runs[(t, "A0")]["verified"] for t in paired)
        c = sum(runs[(t, "A0")]["verified"] and not runs[(t, pa)]["verified"] for t in paired)
        stated = load(RES / report / "e1.json")["summary"]["pairs"].get(f"{pa}-A0", {}).get("mcnemar_p")
        test = {"name": "two-sided exact McNemar on paired tasks", "p": rp(mcnemar_exact(b, c)), "discordant": {"proofforge_only": b, "alone_only": c},
                "preregistered": spec.get("preregistered", False), "stated_in": f"results/{report}/e1.md", "computed_by": "eval/e1.py", "stated_p": rp(stated),
                "significant_at_0_05": mcnemar_exact(b, c) < 0.05}
        out.append(comparison(f"{label}/all/{pa}-vs-A0", label, f"{len(paired)} paired tasks", " and ".join(models) if len(models) > 1 else model,
                              arm("A0", [runs[(t, "A0")] for t in paired], price_basis=spec["price"]),
                              arm(pa, [runs[(t, pa)] for t in paired], price_basis=spec["price"]),
                              scope="aggregate", test=test, caveats=cav, flags=flags, sources=[f"results/{report}/e1.md", f"results/{report}/e1.json"],
                              time_mode="paired", pairs=[(runs[(t, "A0")], runs[(t, pa)]) for t in paired]))
    return out, {"runs": runs, "lost": lost, "totals": totals}


def e1_open_pooled(r2, r1):
    """e1-test-open-2 (scored as its primary analysis) and e1-test-open-1 pooled per task: a secondary analysis of e1-test-open-2."""
    pairs = [(r["runs"][(t, "A0")], r["runs"][(t, "A1")]) for r in (r2, r1)
             for t in sorted({t for t, _ in r["runs"]}) if (t, "A0") in r["runs"] and (t, "A1") in r["runs"]]
    b = sum(y["verified"] and not x["verified"] for x, y in pairs)
    c = sum(x["verified"] and not y["verified"] for x, y in pairs)
    p = mcnemar_exact(b, c)
    test = {"name": "two-sided exact McNemar on paired task runs (secondary, e1-test-open-1 and e1-test-open-2 pooled)", "p": rp(p),
            "discordant": {"proofforge_only": b, "alone_only": c}, "preregistered": True,
            "stated_in": "results/e1-test-open-2/PREREGISTRATION.md", "significant_at_0_05": p < 0.05}
    models = sorted({r["model"] for x, y in pairs for r in (x, y)})
    return [comparison("e1-test-open-2+e1-test-open-1/all/A1-vs-A0", "e1-test-open-2", f"{len(pairs)} paired task runs (30 tasks, two experiments)",
                       " and ".join(models), arm("A0", [x for x, _ in pairs], price_basis="list"), arm("A1", [y for _, y in pairs], price_basis="list"),
                       scope="aggregate", test=test, flags=["includes the runs that motivated the repair-agent changes"],
                       caveats=E1["e1-test-open-2"]["caveats"] + ["Each task appears twice, once per experiment; the two runs of a task are not independent. e1-test-open-1 ran from commit 36fc8d3, before the repair-agent changes."],
                       sources=["results/e1-test-open-2/README.md", "results/e1-test-open-1/e1.md"], time_mode="paired", pairs=pairs)]


def flagship_pairs():
    """baseline-flagships-1 (A0) against the repair runs on the same six real-world tasks."""
    bl = {}
    for d in sorted((RES / "baseline-flagships-1").glob("*/A0-*")):
        bl.setdefault(d.parent.name, []).append(agent_run(d, "passport"))
    pairs = [
        ("rw-cetus-shlw", "cetus-1", "A1", [RES / "cetus-1/repair-A1-1"]),
        ("rw-euler-donate", "euler-1", "A1", [RES / "euler-1/rw-euler-donate/repair-A1-1"]),
        ("rw-hundred-vault", "vault-1", "A1", [RES / "vault-1/repair-A1-1"]),
        ("rw-balancer-upscale", "balancer-1", "A1", [RES / "balancer-1/repair-A1-1", RES / "balancer-1/repair-A1-2"]),
        ("rw-balancer-upscale", "balancer-1", "A2", [RES / "balancer-1/repair-A2-1"]),
        ("rc-knight-router", "knight-1", "A1", [RES / "knight-1/A1-1", RES / "knight-1/A1-2"]),
        ("rc-knight-router", "knight-1", "A2", [RES / "knight-1/A2-1", RES / "knight-1/A2-2"]),
        ("rw-compound-comp", "compound-1", "A1", [RES / "compound-1/repair-A1-1", RES / "compound-1/repair-A1-2"]),
        ("rw-compound-comp", "compound-1", "A2", [RES / "compound-1/repair-A2-1", RES / "compound-1/repair-A2-2"]),
    ]
    base_cav = [
        "Cross-experiment pairing by task: A0 from results/baseline-flagships-1 (two attempts decided in advance) against the repair runs of the task's own experiment.",
        "The repair arms were run adaptively: a second A1 attempt or an A2 run only after a failure, and no further attempt after a success, so the arms are not equal-size samples.",
        "Implement-mode runs are a different mode and are not paired with A0.",
    ]
    out = []
    for task, exp, pa, dirs in pairs:
        pf = [agent_run(d, "passport") for d in dirs]
        cav = list(base_cav)
        if task == "rw-compound-comp":
            cav.append("Both Compound A0 runs ended early when one model call reached its 600 s per-attempt timeout, treated as the run's wall stop; they did not use their full budget (results/baseline-flagships-1/README.md).")
        if pa == "A2":
            cav.append(A2_NOTE)
        out.append(comparison(f"baseline-flagships-1+{exp}/{task}/{pa}-vs-A0", f"baseline-flagships-1 + {exp}", task, SPARK,
                              arm("A0", bl[task]), arm(pa, pf), caveats=cav,
                              sources=["results/baseline-flagships-1/README.md"] + ([f"results/{exp}/README.md"] if (RES / exp / "README.md").exists() else [])))
    return out, bl


def library_1(bl):
    lib = RES / "library-1"
    run = lambda p: agent_run(lib / p, "passport")
    cav = ["A2 here is agents/repair.py with the Muse Wonder planner and the ProofForgeFin library (--library on), library version f2fbb0d3610136fa (results/library-1/README.md).", A2_NOTE]
    out = []
    a0 = [run("rw-balancer-upscale/A0-1"), run("rw-balancer-upscale/A0-2"), run("rw-balancer-upscale/A0-3")]
    a2 = [run("rw-balancer-upscale/A2-1"), run("rw-balancer-upscale/A2-2")]
    out.append(comparison("library-1/rw-balancer-upscale/A2-vs-A0", "library-1", "rw-balancer-upscale", SPARK, arm("A0", a0), arm("A2", a2),
                          caveats=cav, sources=["results/library-1/README.md"]))
    a0p = a0 + bl["rw-balancer-upscale"]
    a2p = a2 + [agent_run(RES / "balancer-1/repair-A2-1", "passport")]
    p = fisher_one_sided(sum(r["verified"] for r in a2p), len(a2p), sum(r["verified"] for r in a0p), len(a0p))
    out.append(comparison("library-1/rw-balancer-upscale/all-measured/A2-vs-A0", "library-1", "rw-balancer-upscale (all measured runs at these caps)", SPARK,
                          arm("A0", a0p), arm("A2", a2p), scope="aggregate",
                          test={"name": "one-sided Fisher exact", "p": rp(p), "preregistered": False, "stated_in": "results/library-1/README.md",
                                "significant_at_0_05": p < 0.05},
                          caveats=cav + ["Pools runs as results/library-1/README.md does: A0 from library-1 and baseline-flagships-1, A2 from library-1 and balancer-1 repair-A2-1 (run before the library existed, so library on in 2 of the 3 A2 runs). These runs also appear in other comparisons."],
                          flags=["pools runs across experiments"], sources=["results/library-1/README.md"]))
    a0c = [run("rw-compound-comp/A0-1"), run("rw-compound-comp/A0-2")]
    a2c = [run("rw-compound-comp/A2-1"), run("rw-compound-comp/A2-2")]
    a2t = [run("rw-compound-comp/A2-topdown-1"), run("rw-compound-comp/A2-topdown-2"), run("rw-compound-comp/A2-topdown-3")]
    out.append(comparison("library-1/rw-compound-comp/A2-vs-A0", "library-1", "rw-compound-comp", SPARK, arm("A0", a0c), arm("A2", a2c),
                          caveats=cav, sources=["results/library-1/README.md"]))
    out.append(comparison("library-1/rw-compound-comp/A2-topdown-vs-A0", "library-1", "rw-compound-comp", SPARK, arm("A0", a0c),
                          arm("A2-topdown", a2t, label="A2 with the top-down loop (three runs at commits 2960943, 17e31c1, b581535)"),
                          caveats=cav + ["The three top-down runs used three different commits of the --loop topdown code; 17e31c1 was dropped (tag topdown-fill-probe)."],
                          flags=["harness changed between runs"], sources=["results/library-1/README.md"]))
    a2k = [run("rc-knight-router/A2-1"), run("rc-knight-router/A2-2")]
    out.append(comparison("library-1+baseline-flagships-1/rc-knight-router/A2-vs-A0", "library-1 + baseline-flagships-1", "rc-knight-router", SPARK,
                          arm("A0", bl["rc-knight-router"]), arm("A2", a2k),
                          caveats=cav + ["library-1 has no Knight A0 run; A0 is the two baseline-flagships-1 runs at the same caps."],
                          flags=["pools runs across experiments"], sources=["results/library-1/README.md", "results/baseline-flagships-1/README.md"]))
    return out


def frontier_1(bl):
    fr = RES / "frontier-1"
    cav = ["Experimental harness on branch experiment/architect-harness (frozen at 624796d), not the default harness; it regressed on the development check and was not adopted (results/frontier-1/README.md).", A2_NOTE]
    out = []
    for task in ("rc-knight-router", "rw-compound-comp"):
        extra = []
        if task == "rw-compound-comp":
            extra = ["The Compound run is recorded as a wall stop but was ended by one request's 600 s timeout (the defect also in the baseline Compound A0 runs)."]
        pf = [agent_run(fr / task / "A2-1", "passport")]
        out.append(comparison(f"frontier-1+baseline-flagships-1/{task}/A2-vs-A0", "frontier-1 + baseline-flagships-1", task, SPARK,
                              arm("A0", bl[task]), arm("A2", pf, label="A2 with the experimental frontier-1 harness"), caveats=cav + extra,
                              flags=["experimental harness, not the default"], sources=["results/frontier-1/README.md"]))
    return out


def feedback_measure_1():
    cands = [RES / "feedback-measure-1", ROOT / ".claude/worktrees/measure-2/results/feedback-measure-1"]
    if ROOT.parent.name == "worktrees" and ROOT.parent.parent.name == ".claude":
        cands.append(ROOT.parent / "measure-2/results/feedback-measure-1")
    base = next((c for c in cands if (c / "rw-compound-comp").is_dir()), None)
    if base is None:
        return [], {"source": "feedback-measure-1", "found": False, "note": "neither results/feedback-measure-1 nor the measure-2 worktree is present"}
    on_branch = base == RES / "feedback-measure-1"
    src = "results/feedback-measure-1" if on_branch else ".claude/worktrees/measure-2/results/feedback-measure-1"
    t = base / "rw-compound-comp"
    a0r = [agent_run(t / "A0-resume-1", "passport")]
    a2r = [agent_run(t / "A2-resume-1", "passport")]
    a2f = [agent_run(t / "A2-full-1", "passport")]
    for r in a0r + a2r + a2f:
        r["dir"] = f"{src}/rw-compound-comp/{pathlib.Path(r['dir']).name}"
    cav = ([] if on_branch else ["Read from the measure-2 worktree, which is not on main: these files are not committed on this branch, and the directory has no README."]) + [
        "No Passport was issued for these runs; requirements proved are the run's ledger.json best candidate.",
        "Library version 5552fae3 with the portfolio, the goal tool and refutation by sampling on; variants off.", A2_NOTE]
    out = [comparison("feedback-measure-1/rw-compound-comp/A2-resume-vs-A0-resume", "feedback-measure-1", "rw-compound-comp", SPARK,
                      arm("A0-resume", a0r, label="A0 resumed from library-1 A0-1 and A0-2 (base proves 5 of 8)"),
                      arm("A2-resume", a2r, label="A2 resumed from the five library-1 A2 runs (base proves 4 of 8)"),
                      caveats=cav + ["Both runs start from earlier runs' candidates: A0 from a base that already proves 5 of 8, A2 from a base that proves 4 of 8."],
                      flags=["resumed runs with different starting points"] + ([] if on_branch else ["not committed on main"]), sources=[src]),
           comparison("feedback-measure-1+library-1/rw-compound-comp/A2-full-vs-A0", "feedback-measure-1 + library-1", "rw-compound-comp", SPARK,
                      arm("A0", [agent_run(RES / "library-1/rw-compound-comp/A0-1", "passport"), agent_run(RES / "library-1/rw-compound-comp/A0-2", "passport")]),
                      arm("A2-full", a2f, label="A2 with every feedback feature (fresh start)"),
                      caveats=cav + ["Cross-experiment pairing: the fresh A2 run against the two library-1 A0 runs at the same caps."],
                      flags=["pools runs across experiments"] + ([] if on_branch else ["not committed on main"]), sources=[src, "results/library-1/README.md"])]
    return out, {"source": src, "found": True, "on_branch": on_branch}


def e2_all_1():
    rows = load(RES / "e2-all-1/e2.json")["rows"]
    bad = [r for r in rows if r["label"] == "bad"]
    good = [r for r in rows if r["label"] == "good"]
    rec = {
        "id": "e2-all-1/catches", "experiment": "e2-all-1", "task": "59 tasks", "scope": "aggregate", "kind": "catches",
        "bad_cases": len(bad), "bad_cases_with_complete_proofs": sum(bool(r.get("complete")) for r in bad), "good_cases": len(good),
        "bad_accepted": {"ordinary": sum(r["ordinary"]["accepted"] for r in bad),
                         "rebuild_and_tests": sum(r["proofforge"]["binary"] == "PASS" for r in bad),
                         "proofforge": sum(r["proofforge"]["accepted"] for r in bad)},
        "good_rejected": {"ordinary": sum(not r["ordinary"]["accepted"] for r in good),
                          "rebuild_and_tests": sum(r["proofforge"]["binary"] != "PASS" for r in good),
                          "proofforge": sum(not r["proofforge"]["accepted"] for r in good)},
        "passed_rebuild_and_tests": [f"{r['task']} {r['case']}" for r in bad if r["proofforge"]["binary"] == "PASS"],
        "caveats": ["Every bad case is a seeded test written by the build team; the results describe this suite, not repairs in general (results/e2-all-1/e2.md).",
                    "Tasks that share a base specification reuse artifacts, so cases are not independent examples.",
                    "No model is involved: the same artifacts are checked three ways."],
        "sources": ["results/e2-all-1/e2.json", "results/e2-all-1/e2.md"],
    }
    rec["classification"] = {"catches_vs_ordinary": "win" if rec["bad_accepted"]["proofforge"] < rec["bad_accepted"]["ordinary"] else "tie",
                             "catches_vs_rebuild_and_tests": "win" if rec["bad_accepted"]["proofforge"] < rec["bad_accepted"]["rebuild_and_tests"] else "tie",
                             "false_rejections": "tie" if rec["good_rejected"]["proofforge"] == rec["good_rejected"]["ordinary"] else "loss"}
    return rec


NOT_COMPARISONS = [
    ("results/feedback-1", "Tactic portfolio replayed on recorded goals, no model calls: it closed 92 of 420 goals the model spent turns on (286 of 3,342 recorded turns, $6.31 of $63.65), none of them a required theorem. It measures a tool on recordings, not the model alone against the model with ProofForge."),
    ("results/feedback-2", "Goal tool, refutation by sampling and parallel variants replayed on recordings, no model calls: the persistent session cut Lean time for 40 snippets from 205 s to 127 s; sampling refuted 0 of 374 introduced lemmas; variants were not shown to save dollars at list price. No model-alone arm."),
    ("results/feedback-library-1", "Failure mining into ProofForgeFin and retrieval by goal shape, no model calls: 0 of 529 held-out open goals close only with the new library; goal-aware retrieval improves recall at 5 and 10 on every set. No model-alone arm."),
    ("results/implement-1", "Implement mode on the 30 test tasks, one arm (A1): 30 of 30 accepted. No model-alone arm in implement mode."),
    ("results/implement-flagships-1", "Implement mode on the real-world tasks, ProofForge arms only. No model-alone arm."),
    ("results/realworld-1", "Real library code checked against proved components; no model-alone arm."),
    ("results/counterexamples-1", "Kernel-checked refutations generated from failing property cases; no model runs."),
    ("results/natural-1", "Behavior search and static findings on intermediate candidates; no model calls."),
    ("results/e2-dev-flagship", "E2 on the flagship task before the complete-proof attacks were added; superseded by results/e2-all-1."),
    ("results/frontier-1 dev-1974abd, dev-624796d", "Development regression check of the experimental harness against the earlier A2, with no A0 arm."),
]


# Claims stated in the experiment READMEs, checked against the computed values

def claims(L):
    by = {c["id"]: c for c in L["comparisons"]}
    g = lambda cid, side, key: by[cid][side][key] if cid in by else None
    e2 = L["catches"][0]
    out = []

    def claim(src, text, stated, computed, tol=0.0):
        ok = computed is not None and (abs(computed - stated) <= tol if isinstance(stated, float) else computed == stated)
        out.append({"source": src, "claim": text, "stated": stated, "computed": computed, "matches": ok})

    m = "results/muse-code-1/README.md"
    claim(m, "Muse Code alone verified 4 of 7", 4, g("muse-code-1/all-four", "alone", "verified"))
    claim(m, "Muse Code with ProofForge verified 5 of 7", 5, g("muse-code-1/all-four", "proofforge", "verified"))
    claim(m, "alone, list $ per verified run 9.50", 9.50, g("muse-code-1/all-four", "alone", "list_usd_per_verified"), 0.005)
    claim(m, "with ProofForge, list $ per verified run 7.02", 7.02, g("muse-code-1/all-four", "proofforge", "list_usd_per_verified"), 0.005)
    claim(m, "Balancer alone 1 of 3, $20.27 per verified run", 20.27, g("muse-code-1/rw-balancer-upscale", "alone", "list_usd_per_verified"), 0.005)
    claim(m, "Balancer with ProofForge 2 of 3, $7.34 per verified run", 7.34, g("muse-code-1/rw-balancer-upscale", "proofforge", "list_usd_per_verified"), 0.005)
    claim(m, "Knight: alone $4.69, with ProofForge $6.47 per verified run (ProofForge arm)", 6.47, g("muse-code-1/rc-knight-router", "proofforge", "list_usd_per_verified"), 0.005)
    claim(m, "Balancer one-sided Fisher p = 0.50", 0.50, (by.get("muse-code-1/rw-balancer-upscale") or {}).get("test", {}).get("p"), 0.005)
    h = "results/hard-task-1/README.md"
    claim(h, "rw-vyper-sqrt alone 2 of 5", 2, g("hard-task-1/rw-vyper-sqrt", "alone", "verified"))
    claim(h, "rw-vyper-sqrt with ProofForge 5 of 5", 5, g("hard-task-1/rw-vyper-sqrt", "proofforge", "verified"))
    claim(h, "rw-vyper-sqrt one-sided Fisher p = 0.083", 0.083, by["hard-task-1/rw-vyper-sqrt"]["test"]["p"], 0.0005)
    claim(h, "rw-oz-sqrt 0 of 5 in both arms (ProofForge arm)", 0, g("hard-task-1/rw-oz-sqrt", "proofforge", "verified"))
    claim(h, "both tasks pooled p = 0.175", 0.175, by["hard-task-1/both-tasks"]["test"]["p"], 0.0005)
    claim(h, "rw-vyper-sqrt alone list dollars $45.88", 45.88, g("hard-task-1/rw-vyper-sqrt", "alone", "list_usd_total"), 0.005)
    claim(h, "rw-vyper-sqrt ProofForge list dollars $27.46", 27.46, g("hard-task-1/rw-vyper-sqrt", "proofforge", "list_usd_total"), 0.005)
    claim(h, "rw-vyper-sqrt per verified run $22.94 alone", 22.94, g("hard-task-1/rw-vyper-sqrt", "alone", "list_usd_per_verified"), 0.005)
    claim(h, "rw-vyper-sqrt per verified run $5.49 with ProofForge", 5.49, g("hard-task-1/rw-vyper-sqrt", "proofforge", "list_usd_per_verified"), 0.005)
    if "vyper-replication-1/rw-vyper-sqrt" in by:
        vr, vg = "results/vyper-replication-1/README.md", "vyper-replication-1/rw-vyper-sqrt"
        claim(vr, "alone verified 8 of 10", 8, g(vg, "alone", "verified"))
        claim(vr, "with ProofForge verified 9 of 10", 9, g(vg, "proofforge", "verified"))
        claim(vr, "Fisher exact p = 0.50", 0.50, by[vg]["test"]["p"], 0.005)
        claim(vr, "Mann-Whitney on list dollars per run, exact p = 0.022", 0.022, by[vg]["test"]["secondary"]["p"], 0.0005)
        claim(vr, "list dollars per verified run $9.00 alone", 9.00, g(vg, "alone", "list_usd_per_verified"), 0.005)
        claim(vr, "list dollars per verified run $5.69 with ProofForge", 5.69, g(vg, "proofforge", "list_usd_per_verified"), 0.005)
        claim(vr, "list dollars total $71.99 alone", 71.99, g(vg, "alone", "list_usd_total"), 0.005)
        claim(vr, "list dollars total $51.22 with ProofForge", 51.22, g(vg, "proofforge", "list_usd_total"), 0.005)
        claim(vr, "pooled with hard-task-1: 10 of 15 alone", 10, g(vg + "+hard-task-1", "alone", "verified"))
        claim(vr, "pooled with hard-task-1: 14 of 15 with ProofForge", 14, g(vg + "+hard-task-1", "proofforge", "verified"))
        claim(vr, "pooled Fisher exact p = 0.084", 0.084, by[vg + "+hard-task-1"]["test"]["p"], 0.0005)
    if "frontier-2/rw-oz-sqrt" in by:
        fr, fo, fc = "results/frontier-2/README.md", "frontier-2/rw-oz-sqrt", "frontier-2/rw-compound-comp"
        claim(fr, "rw-oz-sqrt with ProofForge verified 10 of 10", 10, g(fo, "proofforge", "verified"))
        claim(fr, "rw-oz-sqrt on its own verified 0 of 10", 0, g(fo, "alone", "verified"))
        claim(fr, "rw-oz-sqrt one-sided Fisher exact p = 5.4e-6", 5.4e-6, by[fo]["test"]["p"], 5e-8)
        claim(fr, "rw-oz-sqrt Mann-Whitney exact one-sided p = 5.4e-6", 5.4e-6, by[fo]["test"]["secondary"]["p"], 5e-8)
        claim(fr, "rw-oz-sqrt list dollars total $95.45 on its own", 95.45, g(fo, "alone", "list_usd_total"), 0.005)
        claim(fr, "rw-oz-sqrt list dollars total $19.88 with ProofForge", 19.88, g(fo, "proofforge", "list_usd_total"), 0.005)
        claim(fr, "rw-oz-sqrt list dollars per verified run $1.99 with ProofForge", 1.99, g(fo, "proofforge", "list_usd_per_verified"), 0.005)
        claim(fr, "rw-compound-comp 0 of 10 with ProofForge", 0, g(fc, "proofforge", "verified"))
        claim(fr, "rw-compound-comp 0 of 10 on its own", 0, g(fc, "alone", "verified"))
        claim(fr, "rw-compound-comp list dollars total $90.78 on its own", 90.78, g(fc, "alone", "list_usd_total"), 0.005)
        claim(fr, "rw-compound-comp list dollars total $92.56 with ProofForge", 92.56, g(fc, "proofforge", "list_usd_total"), 0.005)
        claim(fr, "both tasks pooled p = 2.2e-4", 2.2e-4, by["frontier-2/both-tasks"]["test"]["p"], 5e-6)
    if "frontier-3/rw-compound-comp" in by:
        f3r, f3 = "results/frontier-3/README.md", "frontier-3/rw-compound-comp"
        claim(f3r, "with ProofForge verified 2 of 10", 2, g(f3, "proofforge", "verified"))
        claim(f3r, "on its own verified 0 of 10", 0, g(f3, "alone", "verified"))
        claim(f3r, "one-sided Fisher exact p = 0.24", 0.24, by[f3]["test"]["p"], 0.005)
        claim(f3r, "list dollars total $92.47 on its own", 92.47, g(f3, "alone", "list_usd_total"), 0.005)
        claim(f3r, "list dollars total $85.43 with ProofForge", 85.43, g(f3, "proofforge", "list_usd_total"), 0.005)
        claim(f3r, "list dollars per verified run $42.72 with ProofForge", 42.72, g(f3, "proofforge", "list_usd_per_verified"), 0.005)
        claim(f3r, "requirements per run 2.2 of 8 on its own", 2.2, g(f3, "alone", "req_proved_mean"), 0.005)
        claim(f3r, "requirements per run 4.5 of 8 with ProofForge", 4.5, g(f3, "proofforge", "req_proved_mean"), 0.005)
        claim(f3r, "pooled with frontier-2 on its own: 0 of 20", 0, g("frontier-3+frontier-2/rw-compound-comp", "alone", "verified"))
        claim(f3r, "pooled one-sided Fisher exact p = 0.10", 0.10, by["frontier-3+frontier-2/rw-compound-comp"]["test"]["p"], 0.005)
    if "frontier-4/rw-compound-comp" in by:
        f4r, f4 = "results/frontier-4/README.md", "frontier-4/rw-compound-comp"
        claim(f4r, "with ProofForge verified 8 of 10", 8, g(f4, "proofforge", "verified"))
        claim(f4r, "on its own verified 0 of 10", 0, g(f4, "alone", "verified"))
        claim(f4r, "one-sided Fisher exact p = 0.00036", 0.00036, by[f4]["test"]["p"], 0.000005)
        claim(f4r, "against frontier-3's ProofForge arm p = 0.012", 0.012, by[f4]["test"]["secondary"]["p"], 0.0005)
        claim(f4r, "list dollars total $91.74 on its own", 91.74, g(f4, "alone", "list_usd_total"), 0.005)
        claim(f4r, "list dollars total $55.76 with ProofForge", 55.76, g(f4, "proofforge", "list_usd_total"), 0.005)
        claim(f4r, "list dollars per verified run $6.97 with ProofForge", 6.97, g(f4, "proofforge", "list_usd_per_verified"), 0.005)
        claim(f4r, "requirements per run 3.8 of 8 on its own", 3.8, g(f4, "alone", "req_proved_mean"), 0.005)
        claim(f4r, "requirements per run 7.3 of 8 with ProofForge", 7.3, g(f4, "proofforge", "req_proved_mean"), 0.005)
        claim(f4r, "pooled frontier-2, frontier-3 and frontier-4 on its own: 0 of 30", 0, g("frontier-4+frontier-3+frontier-2/rw-compound-comp", "alone", "verified"))
        claim(f4r, "pooled one-sided Fisher exact p = 0.00000059", 5.9e-7, by["frontier-4+frontier-3+frontier-2/rw-compound-comp"]["test"]["p"], 5e-9)
    if "hard-task-2/rw-kyber-swapstep" in by:
        h2r, h2 = "results/hard-task-2/README.md", "hard-task-2/rw-kyber-swapstep"
        claim(h2r, "with ProofForge verified 0 of 10", 0, g(h2, "proofforge", "verified"))
        claim(h2r, "on its own verified 0 of 10", 0, g(h2, "alone", "verified"))
        claim(h2r, "one-sided Fisher exact p = 1", 1.0, by[h2]["test"]["p"], 0.005)
        claim(h2r, "list dollars total $94.66 on its own", 94.66, g(h2, "alone", "list_usd_total"), 0.005)
        claim(h2r, "list dollars total $90.61 with ProofForge", 90.61, g(h2, "proofforge", "list_usd_total"), 0.005)
        claim(h2r, "requirements per run 1.9 of 8 on its own", 1.9, g(h2, "alone", "req_proved_mean"), 0.005)
        claim(h2r, "requirements per run 3.1 of 8 with ProofForge", 3.1, g(h2, "proofforge", "req_proved_mean"), 0.005)
    claim(h, "rw-oz-sqrt alone list dollars $48.53", 48.53, g("hard-task-1/rw-oz-sqrt", "alone", "list_usd_total"), 0.005)
    claim(h, "rw-oz-sqrt ProofForge list dollars $46.06", 46.06, g("hard-task-1/rw-oz-sqrt", "proofforge", "list_usd_total"), 0.005)
    claim(h, "rw-vyper-sqrt runs stopped by the $10 cap: 3 of 5 alone", 3, by["hard-task-1/rw-vyper-sqrt"]["alone"]["cap_stops"]["usd"])
    claim(h, "rw-vyper-sqrt runs stopped by the $10 cap: 0 of 5 with ProofForge", 0, by["hard-task-1/rw-vyper-sqrt"]["proofforge"]["cap_stops"]["usd"])
    claim(h, "rw-oz-sqrt required theorems in last compiling versions: 13 alone over five runs", 13, sum(by["hard-task-1/rw-oz-sqrt"]["alone"]["req_proved_per_run"]))
    claim(h, "rw-oz-sqrt required theorems in last compiling versions: 5 with ProofForge", 5, sum(by["hard-task-1/rw-oz-sqrt"]["proofforge"]["req_proved_per_run"]))
    E = L["_e1_runs"]
    for lab, n, a0, a1, a2 in (("e1-test-1", 30, 28, 30, 30), ("e1-test-open-1", 30, 21, 24, None), ("e1-dev-2", 23, 19, 20, 21), ("e1-dev-1", 23, 20, 11, 17)):
        s = f"results/{lab}/e1.md"
        for a, v in (("A0", a0), ("A1", a1), ("A2", a2)):
            if v is not None:
                claim(s, f"{a} completed {v}/{n} (every scored run, a lost run counted as not completed)", v, E[lab]["totals"][a]["completed"])
    claim("results/README.md", "e1-dev-1: two runs lost to network timeouts", 2, len(E["e1-dev-1"]["lost"]))
    claim("results/e1-test-1/e1.md", "A0 list $ per completed repair 0.87", 0.87, g("e1-test-1/all/A1-vs-A0", "alone", "list_usd_per_verified"), 0.005)
    claim("results/e1-test-1/e1.md", "A1 list $ per completed repair 0.61", 0.61, g("e1-test-1/all/A1-vs-A0", "proofforge", "list_usd_per_verified"), 0.005)
    claim("results/e1-test-1/e1.md", "A2 list $ per completed repair 0.92", 0.92, g("e1-test-1/all/A2-vs-A0", "proofforge", "list_usd_per_verified"), 0.005)
    claim("results/e1-test-1/e1.md", "A1 vs A0 McNemar exact p = 0.5000", 0.5, by["e1-test-1/all/A1-vs-A0"]["test"]["p"], 0.00005)
    o = "results/README.md"
    claim(o, "e1-test-open-1: A0 21 of 30", 21, g("e1-test-open-1/all/A1-vs-A0", "alone", "verified"))
    claim(o, "e1-test-open-1: A1 24 of 30", 24, g("e1-test-open-1/all/A1-vs-A0", "proofforge", "verified"))
    claim(o, "e1-test-open-1: McNemar exact p = 0.51", 0.51, by["e1-test-open-1/all/A1-vs-A0"]["test"]["p"], 0.005)
    claim(o, "e1-test-open-1: all 9 A0 failures stopped at the dollar cap", 9, by["e1-test-open-1/all/A1-vs-A0"]["alone"]["cap_stops"]["usd"])
    o2, a2, p2 = "results/e1-test-open-2/README.md", "e1-test-open-2/all/A1-vs-A0", "e1-test-open-2+e1-test-open-1/all/A1-vs-A0"
    claim(o2, "A0 completed 22 of 30", 22, g(a2, "alone", "verified"))
    claim(o2, "A1 completed 24 of 30", 24, g(a2, "proofforge", "verified"))
    claim(o2, "discordant pairs 6 for A1 and 4 for A0", [6, 4], list(by[a2]["test"]["discordant"].values()))
    claim(o2, "two-sided exact McNemar p = 0.75", 0.75, by[a2]["test"]["p"], 0.005)
    claim(o2, "required theorems proved per run 6.0 with A0", 6.0, g(a2, "alone", "req_proved_mean"), 0.05)
    claim(o2, "required theorems proved per run 7.4 with A1", 7.4, g(a2, "proofforge", "req_proved_mean"), 0.05)
    claim(o2, "list dollars per completed repair $1.45 with A0", 1.45, g(a2, "alone", "list_usd_per_verified"), 0.005)
    claim(o2, "list dollars per completed repair $1.30 with A1", 1.30, g(a2, "proofforge", "list_usd_per_verified"), 0.005)
    claim(o2, "list dollars total $32.00 with A0", 32.00, g(a2, "alone", "list_usd_total"), 0.005)
    claim(o2, "list dollars total $31.13 with A1", 31.13, g(a2, "proofforge", "list_usd_total"), 0.005)
    claim(o2, "A0 runs stopped by the dollar cap: 7", 7, by[a2]["alone"]["cap_stops"]["usd"])
    claim(o2, "A1 runs stopped by the dollar or wall cap: 5 and 1", [5, 1], [by[a2]["proofforge"]["cap_stops"]["usd"], by[a2]["proofforge"]["cap_stops"]["wall"]])
    rr = [r for (t, a), r in E["e1-test-open-2"]["runs"].items() if r["model"] == "meta-models/muse-spark-open"]
    claim(o2, "rerun tasks alone: A0 8 of 12", 8, sum(r["verified"] for r in rr if r["arm"] == "A0"))
    claim(o2, "rerun tasks alone: A1 10 of 12", 10, sum(r["verified"] for r in rr if r["arm"] == "A1"))
    claim(o2, "pooled with e1-test-open-1: A0 43 of 60", 43, g(p2, "alone", "verified"))
    claim(o2, "pooled with e1-test-open-1: A1 48 of 60", 48, g(p2, "proofforge", "verified"))
    claim(o2, "pooled two-sided exact McNemar p = 0.36", 0.36, by[p2]["test"]["p"], 0.005)
    gl = "results/e1-test-glimmer-1/README.md"
    gr = L["_e1_runs"]["e1-test-glimmer-1"]["runs"]
    claim(gl, "excluding the outage runs, A0 completed 0 of 15", 15, sum(1 for (t, a) in gr if a == "A0"))
    claim(gl, "excluding the outage runs, A1 completed 3 of 13", 13, sum(1 for (t, a) in gr if a == "A1"))
    claim(gl, "A1 completed repairs: 3", 3, sum(r["verified"] for (t, a), r in gr.items() if a == "A1"))
    claim(gl, "McNemar exact p = 0.25 (paired tasks)", 0.25, by["e1-test-glimmer-1/all/A1-vs-A0"]["test"]["p"], 0.00005)
    b = "results/baseline-flagships-1/README.md"
    bl = L["_baseline"]
    for task, n in (("rw-cetus-shlw", 2), ("rw-euler-donate", 2), ("rw-hundred-vault", 2), ("rw-balancer-upscale", 1), ("rc-knight-router", 1), ("rw-compound-comp", 0)):
        claim(b, f"A0 accepted {n} of 2 on {task}, every accepted run VERIFIED", n, sum(r["verified"] for r in bl[task]))
    walls = sorted({c["wall_s"] for cid, cmp in by.items() if cid.startswith("baseline-flagships-1+") for c in cmp["proofforge"]["caps"]})
    claim(b, "A0 caps ($10, 14,400 s) are the same caps as the repair runs in cetus-1, euler-1, vault-1, balancer-1, knight-1 and compound-1 (wall caps of those repair runs, computed)",
          "14400.0", ", ".join(str(w) for w in walls))
    lb = "results/library-1/README.md"
    claim(lb, "Balancer, all measured runs: A0 verified 2 of 5", 2, g("library-1/rw-balancer-upscale/all-measured/A2-vs-A0", "alone", "verified"))
    claim(lb, "Balancer, all measured runs: A0 list $40.04", 40.04, g("library-1/rw-balancer-upscale/all-measured/A2-vs-A0", "alone", "list_usd_total"), 0.005)
    claim(lb, "Balancer, all measured runs: A2 verified 3 of 3, list $9.18", 9.18, g("library-1/rw-balancer-upscale/all-measured/A2-vs-A0", "proofforge", "list_usd_total"), 0.005)
    claim(lb, "Balancer, all measured runs: A2 $3.06 per verified run", 3.06, g("library-1/rw-balancer-upscale/all-measured/A2-vs-A0", "proofforge", "list_usd_per_verified"), 0.005)
    claim(lb, "Balancer one-sided Fisher exact p = 0.18", 0.18, by["library-1/rw-balancer-upscale/all-measured/A2-vs-A0"]["test"]["p"], 0.005)
    k = "results/knight-1/README.md"
    claim(k, "the four Knight runs cost $29.64 at list prices", 29.64,
          r2(by["baseline-flagships-1+knight-1/rc-knight-router/A1-vs-A0"]["proofforge"]["list_usd_total"] + by["baseline-flagships-1+knight-1/rc-knight-router/A2-vs-A0"]["proofforge"]["list_usd_total"]), 0.005)
    e = "results/e2-all-1/e2.md"
    claim(e, "ordinary checking accepts 233 of 247 bad cases", 233, e2["bad_accepted"]["ordinary"])
    claim(e, "rebuild and tests accept 1 of 247 bad cases", 1, e2["bad_accepted"]["rebuild_and_tests"])
    claim(e, "ProofForge accepts 0 of 247 bad cases", 0, e2["bad_accepted"]["proofforge"])
    claim(e, "ProofForge rejects 0 of 239 good cases", 0, e2["good_rejected"]["proofforge"])
    claim("README.md", "results/library-1 is running; no results are committed (section 'Muse alone and Muse with ProofForge')", 0,
          sum(1 for _ in (RES / "library-1").glob("*/*/summary.json")))
    return out


# Wins

def fmt_usd(x):
    return "n/a" if x is None else f"${x:,.2f}"


def fmt_s(x):
    return "n/a" if x is None else f"{x:,.0f} s"


def where(c):
    """Evidence for the ProofForge arm's verified runs: Passport ids, or E1 judge records."""
    pf = c["proofforge"]
    if pf["passports"]:
        ps = pf["passports"]
        return " Passports " + ", ".join(f"`{p}`" for p in ps) if len(ps) <= 6 else f" {len(ps)} Passports, listed in `ledger.json`"
    js = pf["judge_records"]
    if not js:
        return ""
    return " Judge record " + ", ".join(f"`{p}`" for p in js) if len(js) <= 2 else f" {len(js)} judge records, listed in `ledger.json`"


def time_vals(c):
    """(alone, ProofForge, wording) of the wall times the time classification compared."""
    pb = c.get("paired_both_verified")
    if pb:
        return pb["alone_wall_s_mean"], pb["proofforge_wall_s_mean"], f"mean wall time on the {pb['tasks_both_verified']} tasks both arms verified"
    if c["time_basis"].startswith("not compared"):
        return None, None, "not compared"
    return c["alone"]["wall_s_mean_verified"], c["proofforge"]["wall_s_mean_verified"], "mean wall time of verified runs"


def caps_text(a):
    return ", ".join("$%g and %s s" % (x["usd"], f"{x['wall_s']:,.0f}") for x in a["caps"])


def tag(c):
    t = []
    if "incomplete" in c["flags"]:
        t.append("incomplete experiment")
    if "different budgets" in c["flags"]:
        t.append(f"different budgets: alone {caps_text(c['alone'])}, with ProofForge {caps_text(c['proofforge'])}")
    if "development tasks" in c["flags"]:
        t.append("development tasks")
    for f in c["flags"]:
        if f in ("pools runs across experiments", "experimental harness, not the default", "not committed on main", "resumed runs with different starting points", "harness changed between runs"):
            t.append(f)
    if c.get("test"):
        p = c["test"]["p"]
        if c["test"].get("significant_at_0_05"):
            d = {"win": "in favour of ProofForge", "loss": "in favour of the model on its own"}.get(c["classification"]["verification"], "")
            t.append(f"{c['test']['name']} p = {p:.4g}, {d}".rstrip(", "))
        else:
            t.append(f"{c['test']['name']} p = {p:.4g}")
    return f" ({'; '.join(t)})" if t else ""


def wins(L):
    g1, g2, g3 = [], [], []
    for c in L["comparisons"]:
        al, pf, cl, fa = c["alone"], c["proofforge"], c["classification"], c["factors"]
        name = f"`{c['id']}`"
        ev = where(c)
        base = f"{name}: {c['model']}, {al['arm']} against {pf['arm']}"
        if cl["verification"] == "win" and al["verified"] == 0:
            stops = sum(al["cap_stops"].values())
            g1.append({"id": c["id"], "experiment": c["experiment"], "scope": c["scope"], "sentence":
                       f"{base}: alone verified 0 of {al['runs']} ({stops} stopped at a cap, mean {al['req_proved_mean']:g} of {al['req_total']} requirements proved); "
                       f"with ProofForge {pf['verified']} of {pf['runs']} verified at {fmt_usd(pf['list_usd_per_verified'])} per verified run "
                       f"({pf['price_basis'] if pf['price_basis'] != 'list' else 'list prices'}).{ev}{tag(c)}."})
        elif cl["verification"] == "win":
            g3.append({"id": c["id"], "experiment": c["experiment"], "scope": c["scope"], "kind": "verified more often", "sentence":
                       f"{base}: verified {pf['verified']} of {pf['runs']} with ProofForge against {al['verified']} of {al['runs']} alone; "
                       f"list $ per verified run {fmt_usd(pf['list_usd_per_verified'])} against {fmt_usd(al['list_usd_per_verified'])}.{ev}{tag(c)}."})
        if al["verified"] and pf["verified"] and ("win" in (cl["cost"], cl["time"])):
            parts = []
            if cl["cost"] == "win":
                parts.append(f"{fa['cost']:.2f}x cheaper ({fmt_usd(pf['list_usd_per_verified'])} against {fmt_usd(al['list_usd_per_verified'])} list per verified run)")
            if cl["time"] == "win":
                ta, tp, basis = time_vals(c)
                parts.append(f"{fa['time']:.2f}x faster ({basis} {fmt_s(tp)} against {fmt_s(ta)})")
            g2.append({"id": c["id"], "experiment": c["experiment"], "scope": c["scope"],
                       "cost_factor": fa.get("cost") if cl["cost"] == "win" else None, "time_factor": fa.get("time") if cl["time"] == "win" else None,
                       "sentence": f"{base}: both verified ({al['verified']} of {al['runs']} alone, {pf['verified']} of {pf['runs']} with ProofForge); ProofForge "
                                   + " and ".join(parts) + f".{ev}{tag(c)}."})
        if cl["verification"] != "win":
            if cl["requirements"] == "win":
                g3.append({"id": c["id"], "experiment": c["experiment"], "scope": c["scope"], "kind": "more requirements proved", "sentence":
                           f"{base}: more requirements proved with ProofForge, mean {pf['req_proved_mean']:g} of {pf['req_total']} per run "
                           f"(per run {pf['req_proved_per_run']}) against {al['req_proved_mean']:g} (per run {al['req_proved_per_run']}); "
                           f"verified {pf['verified']} of {pf['runs']} against {al['verified']} of {al['runs']}{tag(c)}."})
            if cl["cap_stops"] == "win":
                g3.append({"id": c["id"], "experiment": c["experiment"], "scope": c["scope"], "kind": "fewer runs stopped by a cap", "sentence":
                           f"{base}: {sum(pf['cap_stops'].values())} of {pf['runs']} ProofForge runs stopped at a cap against "
                           f"{sum(al['cap_stops'].values())} of {al['runs']} alone{tag(c)}."})
    for e in L["catches"]:
        ba = e["bad_accepted"]
        g3.append({"id": e["id"], "experiment": e["experiment"], "scope": "aggregate", "kind": "bad candidates caught", "sentence":
                   f"`{e['id']}`: on the same {e['bad_cases']} seeded bad cases ({e['bad_cases_with_complete_proofs']} with complete proofs), ordinary checking accepted "
                   f"{ba['ordinary']}, the rebuild with property tests accepted {ba['rebuild_and_tests']} ({', '.join(e['passed_rebuild_and_tests'])}), and ProofForge accepted "
                   f"{ba['proofforge']}; ProofForge rejected {e['good_rejected']['proofforge']} of {e['good_cases']} good cases (seeded suite written by the build team; "
                   f"`results/e2-all-1/e2.json`)."})
    return {"1_alone_did_not_verify_proofforge_did": g1, "2_both_verified_proofforge_faster_or_cheaper": g2, "3_other": g3}


def build():
    # The strongest preregistered results first: OpenZeppelin Math.sqrt, Compound, then Vyper sqrt().
    h, hard_pooled = hard_task_1()
    v, vinfo = vyper_replication_1(hard_pooled)
    f2, f2info = frontier_2()
    f3, f3info = frontier_3()
    f4, f4info = frontier_4()
    h2, h2info = hard_task_2()
    comps = f2 + f4 + h + v + f3 + h2
    comps += muse_code_1()
    f, bl = flagship_pairs()
    comps += f
    comps += library_1(bl)
    comps += frontier_1(bl)
    fm, finfo = feedback_measure_1()
    comps += fm
    e1_runs = {}
    for lab in ("e1-test-1", "e1-test-open-2", "e1-test-open-1", "e1-test-glimmer-1", "e1-dev-2", "e1-dev-1"):
        c, runs = e1(lab)
        comps += c
        e1_runs[lab] = runs
    comps += e1_open_pooled(e1_runs["e1-test-open-2"], e1_runs["e1-test-open-1"])
    L = {"schema": 1, "generator": "eval/wins.py",
         "rules": {"verified": "Passport status VERIFIED from bin/proofforge check on the final candidate; for E1 runs, eval.json completed (judge ACCEPT and binary PASS on 2,000 property cases)",
                   "verification": "win when the ProofForge arm's verified fraction is higher, loss when lower",
                   "cost": "list $ per verified run (all list dollars of an arm divided by its verified runs); a difference under 5% is a tie; win when only ProofForge verified",
                   "time": "mean wall time of the verified runs, compared only when both arms verified; on E1 aggregates the mean on the paired tasks both arms verified; not compared on aggregates over several tasks with unpaired runs (muse-code-1 all four, hard-task-1 both tasks); a difference under 5% is a tie",
                   "requirements": "mean required theorems proved per run: the Passport count for a verified run, else the last compiling version where the run records it (last_compiling.json, ledger.json best_candidate), else the run's own check of its final snapshot",
                   "cap_stops": "fraction of runs stopped by the dollar or wall cap",
                   "first_verified_s": "A0, A1, A2: first accepted judge event in events.jsonl; Muse Code with ProofForge: end of the first check_candidate call returning VERIFIED; Muse Code alone: end of run, when the runner's judge accepted"},
         "optional_sources": {"vyper-replication-1": vinfo, "frontier-2": f2info, "frontier-3": f3info, "frontier-4": f4info, "hard-task-2": h2info, "feedback-measure-1": finfo},
         "comparisons": comps, "catches": [e2_all_1()],
         "not_comparisons": [{"source": s, "why": w} for s, w in NOT_COMPARISONS],
         "_e1_runs": e1_runs, "_baseline": bl}
    L["e1_runs_set_aside"] = {lab: v["lost"] for lab, v in e1_runs.items() if v["lost"]}
    L["e1_arm_totals"] = {lab: v["totals"] for lab, v in e1_runs.items()}
    L["claims"] = claims(L)
    L["wins"] = wins(L)
    del L["_e1_runs"], L["_baseline"]
    runs = {}
    for c in comps:
        for side in ("alone", "proofforge"):
            for r in c[side].pop("_runs"):
                runs[r["dir"]] = r
    L["runs"] = dict(sorted(runs.items()))
    L["counts"] = {"comparisons": len(comps), "runs": len(runs), "wins_group_1": len(L["wins"]["1_alone_did_not_verify_proofforge_did"]),
                   "wins_group_2": len(L["wins"]["2_both_verified_proofforge_faster_or_cheaper"]),
                   "wins_group_3": len(L["wins"]["3_other"]),
                   "classification": {dim: {k: sum(c["classification"][dim] == k for c in comps) for k in ("win", "tie", "loss", "n/a")}
                                      for dim in ("verification", "cost", "time", "requirements", "cap_stops")},
                   "claims_checked": len(L["claims"]), "claims_differing": sum(not c["matches"] for c in L["claims"])}
    return L


# README

def readme(L):
    W = L["wins"]
    lines = ["# Wins: a Meta model alone against the same model with ProofForge", "",
             "Generated by `python3 eval/wins.py` from `ledger.json` in this directory; do not edit by hand. Every number is computed from the raw run files "
             "(summary.json, eval.json, passport.json, events.jsonl, mcp-calls.jsonl, last_compiling.json, ledger.json, e1.json, e2.json); no model calls. "
             "The ledger keeps every comparison, ties and losses included. The wins come first, then [every comparison](#every-comparison), "
             "the [rules](#rules), the [statistics and methods](#statistics-and-methods) and the [README claims checked against the data](#readme-claims-checked-against-the-raw-data). "
             "Real-world tasks are listed before the E1 benchmark.", ""]
    cnt = L["counts"]
    lines += [f"{cnt['comparisons']} comparisons over {cnt['runs']} runs. Wins: {cnt['wins_group_1']} where the model alone did not verify and ProofForge did; "
              f"{cnt['wins_group_2']} where both verified and ProofForge was faster or cheaper; {cnt['wins_group_3']} of other kinds. "
              "A comparison ID names the experiment, the task and the arms; its runs, files and Passports are in `ledger.json`."]

    def section(title, items, intro=None):
        out = ["", f"## {title}", ""]
        if intro:
            out += [intro, ""]
        if not items:
            return out + ["None."]
        for exp in dict.fromkeys(i["experiment"] for i in items):
            out += [f"### {exp}", ""]
            for i in items:
                if i["experiment"] == exp:
                    out.append(f"- {i['sentence']}")
            out.append("")
        return out

    lines += section("Wins (1): the model alone did not verify, ProofForge did", W["1_alone_did_not_verify_proofforge_did"],
                     "Task-level comparisons and aggregates. In E1 one run per arm per task.")
    lines += section("Wins (2): both verified, ProofForge faster or cheaper", W["2_both_verified_proofforge_faster_or_cheaper"],
                     "The factor is the alone arm's value divided by the ProofForge arm's: list $ per verified run, or mean wall time of the verified runs.")
    lines += section("Wins (3): other kinds", W["3_other"],
                     "Verified more often where the model alone also verified some runs; more requirements proved or fewer cap stops where verification did not differ; bad candidates caught.")

    lines += ["", "## Every comparison", "", "| Dimension | Win | Tie | Loss | n/a |", "|---|---|---|---|---|"]
    for dim, v in cnt["classification"].items():
        lines.append(f"| {dim} | {v['win']} | {v['tie']} | {v['loss']} | {v['n/a']} |")
    lines += ["",
              "V verification, C cost, T time, R requirements, S cap stops: W win, T tie, L loss, - not applicable, for ProofForge. "
              "List $ per verified run and wall time are given alone / with ProofForge; the wall time is the mean of the verified runs, "
              "on E1 aggregates the mean on the tasks both arms verified, and n/a on aggregates over several tasks with unpaired runs.", ""]
    head = ["| Comparison | Model | Alone | ProofForge | Verified | List $ per verified | Wall time | Req. proved, mean | Cap stops | Test | V C T R S |",
            "|---|---|---|---|---|---|---|---|---|---|---|"]
    ab = {"win": "W", "tie": "T", "loss": "L", "n/a": "-"}

    def row(c):
        al, pf, cl = c["alone"], c["proofforge"], c["classification"]
        t = c.get("test")
        ts = f"{t['p']:.4g}" if t else ""
        ta, tp, _ = time_vals(c)
        return (f"| `{c['id']}` | {c['model']} | {al['arm']}, {al['runs']} | {pf['arm']}, {pf['runs']} | {al['verified']} / {pf['verified']} | "
                f"{fmt_usd(al['list_usd_per_verified'])} / {fmt_usd(pf['list_usd_per_verified'])} | {fmt_s(ta)} / {fmt_s(tp)} | "
                f"{al['req_proved_mean']:g} / {pf['req_proved_mean']:g} of {max(al['req_total'], pf['req_total'])} | {sum(al['cap_stops'].values())} / {sum(pf['cap_stops'].values())} | {ts} | "
                + " ".join(ab[cl[d]] for d in ("verification", "cost", "time", "requirements", "cap_stops")) + " |")
    lines += ["### Aggregates and real-world tasks", ""] + head
    for c in L["comparisons"]:
        if not c["experiment"].startswith("e1-") or c["scope"] == "aggregate":
            lines.append(row(c))
    for exp in dict.fromkeys(c["experiment"] for c in L["comparisons"] if c["experiment"].startswith("e1-")):
        lines += ["", f"### {exp}, per task", ""] + head
        for c in L["comparisons"]:
            if c["experiment"] == exp and c["scope"] == "task":
                lines.append(row(c))
    e = L["catches"][0]
    lines += ["", "### Catches (`e2-all-1`)", "", "| Checking | Bad cases accepted | Good cases rejected |", "|---|---|---|"]
    for k, n in (("ordinary", "Ordinary checking"), ("rebuild_and_tests", "Rebuild and property tests"), ("proofforge", "ProofForge")):
        lines.append(f"| {n} | {e['bad_accepted'][k]} of {e['bad_cases']} | {e['good_rejected'][k]} of {e['good_cases']} |")

    lines += ["", "## Rules", ""]
    for k, v in L["rules"].items():
        lines.append(f"- **{k}**: {v}.")
    lines += ["", "## Statistics and methods", "", "### Stated tests", ""]
    for c in L["comparisons"]:
        t = c.get("test")
        if t and not t.get("significant_at_0_05"):
            pre = "preregistered" if t.get("preregistered") else "not preregistered"
            lines.append(f"- `{c['id']}`: {t['name']}, p = {t['p']:.4g} ({pre}; stated in `{t['stated_in']}`).")
    sig = [c for c in L["comparisons"] if c.get("test") and c["test"].get("significant_at_0_05")]
    if sig:
        lines += ["", "p below 0.05:", ""]
        for c in sig:
            d = "in favour of ProofForge" if c["classification"]["verification"] == "win" else "in favour of the model on its own" if c["classification"]["verification"] == "loss" else ""
            lines.append(f"- `{c['id']}`: {c['test']['name']}, p = {c['test']['p']:.4g}, {d}.")
    lines += ["", "### Different budgets", ""]
    for c in L["comparisons"]:
        if not c["equal_caps"]:
            lines.append(f"- `{c['id']}`: alone {caps_text(c['alone'])}; with ProofForge {caps_text(c['proofforge'])}.")
    lines += ["", "### Incomplete or optional sources", ""]
    for k, v in L["optional_sources"].items():
        lines.append(f"- {k}: " + ("found at `" + v["source"] + "`" if v.get("found") else "not found") + (f"; {v['note']}" if v.get("note") else "")
                     + ("; not committed on main" if v.get("found") and v.get("on_branch") is False else "") + ".")
    lines.append("- e1-test-glimmer-1: incomplete, 31 of 60 runs scored before the host paused the workspace; outage runs excluded as its README states.")
    lines += ["", "### Per experiment", ""]
    seen = {}
    for c in L["comparisons"]:
        for cv in c["caveats"]:
            seen.setdefault(c["experiment"], [])
            if cv not in seen[c["experiment"]]:
                seen[c["experiment"]].append(cv)
    for exp, cvs in seen.items():
        lines += [f"{exp}:", ""] + [f"- {cv}" for cv in cvs] + [""]
    lines += ["e2-all-1:", ""] + [f"- {cv}" for cv in e["caveats"]] + [""]
    lines += ["### Measured, but not a comparison of the model alone with ProofForge", ""]
    for n in L["not_comparisons"]:
        lines.append(f"- `{n['source']}`: {n['why']}")
    lines += ["", "## README claims checked against the raw data", "",
              f"{L['counts']['claims_checked']} claims, {L['counts']['claims_differing']} differ.", "",
              "| Source | Claim | Stated | Computed | Matches |", "|---|---|---|---|---|"]
    for c in L["claims"]:
        lines.append(f"| `{c['source']}` | {c['claim']} | {c['stated']} | {c['computed']} | {'yes' if c['matches'] else 'no'} |")
    lines += ["", "## Reproduce", "", "```sh", "python3 eval/wins.py", "python3 tests/test_wins.py", "```", ""]
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true", help="compare the committed files with a fresh build; write nothing")
    a = ap.parse_args()
    L = build()
    js = json.dumps(L, indent=1, ensure_ascii=False) + "\n"
    md = readme(L)
    if a.check:
        same = (OUT / "ledger.json").exists() and (OUT / "ledger.json").read_text() == js and (OUT / "README.md").read_text() == md
        print("up to date" if same else "differs")
        sys.exit(0 if same else 1)
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "ledger.json").write_text(js)
    (OUT / "README.md").write_text(md)
    c = L["counts"]
    print(f"{c['comparisons']} comparisons; wins {c['wins_group_1']} / {c['wins_group_2']} / {c['wins_group_3']}; "
          f"claims {c['claims_checked']}, {c['claims_differing']} differ")


if __name__ == "__main__":
    main()
