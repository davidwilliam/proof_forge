#!/usr/bin/env python3
"""Can parallel short variants (agents/variants.py) win at list price? A simulation on the token
counts of recorded runs; no model calls, no Lean.

From each recorded run: every goal's dialogs in order (turn events labelled `<phase>:<goal>`, a
dialog starting at turn 0), each turn's list-price dollars from its recorded usage, and whether the
dialog ended with the goal proved (the `obligation` event after it). The goals that matter are the
ones still open after their first dialog. For each of them the recording also gives what the run
spent on it afterwards: its later dialogs, the planner calls for it (`plan` events) and, recursively,
the dialogs on the lemmas of those plans; and whether it was proved in the end.

The variants arm is simulated per goal: K variants of at most T turns each start after the first
dialog. A variant is modelled by a recorded later dialog (a dialog on a goal that was still open
after its first dialog, other than the goal's own first dialog), drawn at random from all runs: it
succeeds at turn j if that dialog ended with its goal proved after j <= T turns, and turn i costs
what that dialog's turn i cost. The variants run in lockstep and stop when the first one succeeds,
each charged the turns it started (a request in flight is charged). If none succeeds the run goes on
as recorded. Treating the later dialogs as draws for a fresh variant is optimistic in two ways: they
came with the first dialog's failure notes and, in A2, after a planner decomposition had proved
helper lemmas for them; and the K draws are independent, while variants on one goal share its
difficulty. The result is therefore an upper bound on what variants save.

Usage: variants_replay.py RUN_DIR [RUN_DIR ...] --out DIR [--k 2,3] [--turns 2,4,6] [--draws N]
"""
import argparse, json, pathlib, random, statistics, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness")]
import budget, ledger  # noqa: E402


def dialogs(events):
    """Per goal, its dialogs in order: {label, turns: [usd], ok}; and plan children per goal with
    the planner's dollars."""
    per, cur, plans, planned = {}, {}, {}, set()
    for e in events:
        k = e.get("kind")
        if k == "turn":
            g = ledger.goal_label(e.get("label"))
            if not g or e.get("variant"):
                continue
            try:
                usd = budget.list_cost(e.get("model"), e.get("usage") or {})
            except KeyError:
                usd = 0.0
            if e.get("turn") == 0 or g not in cur:
                cur[g] = {"label": e["label"], "turns": [], "ok": False, "after_plan": g in planned}
                per.setdefault(g, []).append(cur[g])
            cur[g]["turns"].append(usd)
        elif k == "obligation" and e.get("theorem") in cur and e.get("by") is None:
            cur[e["theorem"]]["ok"] = bool(e.get("ok"))
        elif k == "plan":
            planned.add(e.get("theorem"))
            p = plans.setdefault(e.get("theorem"), {"lemmas": [], "usd": 0.0, "calls": 0})
            p["lemmas"] += e.get("lemmas") or []
            p["usd"] += e.get("usd_list") or 0.0
            p["calls"] += 1
    return per, plans


def rest_cost(goal, per, plans, seen=None):
    """Dollars and turns a recording spent on `goal` after its first dialog: its later dialogs, its
    planner calls and everything spent on the lemmas of its plans."""
    seen = seen if seen is not None else set()
    if goal in seen:
        return 0.0, 0
    seen.add(goal)
    ds = per.get(goal, [])
    usd = sum(sum(d["turns"]) for d in ds[1:])
    turns = sum(len(d["turns"]) for d in ds[1:])
    p = plans.get(goal)
    if p:
        usd += p["usd"]
        for l in p["lemmas"]:
            u, t = all_cost(l, per, plans, seen)
            usd += u
            turns += t
    return usd, turns


def all_cost(goal, per, plans, seen):
    if goal in seen:
        return 0.0, 0
    ds = per.get(goal, [])
    u0 = sum(d["turns"][i] for d in ds[:1] for i in range(len(d["turns"])))
    t0 = sum(len(d["turns"]) for d in ds[:1])
    u, t = rest_cost(goal, per, plans, seen)
    return u0 + u, t0 + t


def load(run_dirs):
    goals, pool = [], []
    for d in run_dirs:
        d = pathlib.Path(d)
        ev = ledger._events(d)
        summ = json.loads((d / "summary.json").read_text())
        per, plans = dialogs(ev)
        final = summ.get("final_status") or {}
        ever = {g for g, ds in per.items() if any(x["ok"] for x in ds)}
        for g, ds in per.items():
            if ds[0]["ok"]:
                continue
            usd, turns = rest_cost(g, per, plans)
            proved = g in ever or final.get(g) == "PROVED"
            later = [{"turns": x["turns"], "ok": x["ok"], "after_plan": x["after_plan"]} for x in ds[1:]]
            goals.append({"run": str(d), "goal": g, "first_turns": len(ds[0]["turns"]), "first_usd": sum(ds[0]["turns"]),
                          "rest_usd": usd, "rest_turns": turns, "proved": proved,
                          "planner_calls": (plans.get(g) or {}).get("calls", 0), "later": later})
            pool += later
    return goals, pool


def simulate(goals, pool, k, t, draws, rng, model="pooled"):
    """Expected dollars and proofs of the recorded path and of K variants of T turns before it.
    `pooled` (and `pooled-no-plan`, called with the later dialogs that no planner decomposition of
    their goal preceded): each variant is a draw from `pool`; `same-goal`: a draw from the goal's
    own later dialogs, and a goal with none gets variants that fail after T turns at the pool's
    median cost per turn (nothing is credited); `same-goal-no-plan`: the same with only the goal's
    later dialogs that no decomposition preceded (the most conservative)."""
    base_usd = sum(g["rest_usd"] for g in goals)
    base_proved = sum(g["proved"] for g in goals)
    var_usd = var_proved = var_spent = won = 0.0
    med = statistics.median([u for v in pool for u in v["turns"]]) if pool else 0.0
    for g in goals:
        own = [x for x in g["later"] if model != "same-goal-no-plan" or not x["after_plan"]]
        for _ in range(draws):
            if model.startswith("same-goal"):
                vs = [rng.choice(own) for _ in range(k)] if own else [{"turns": [med] * t, "ok": False}] * k
            else:
                vs = [rng.choice(pool) for _ in range(k)]
            wins = [len(v["turns"]) for v in vs if v["ok"] and len(v["turns"]) <= t]
            stop = min(wins) if wins else t
            spent = sum(sum(v["turns"][:min(stop, len(v["turns"]))]) for v in vs)
            var_spent += spent / draws
            if wins:
                won += 1 / draws
                var_usd += spent / draws
                var_proved += 1 / draws
            else:
                var_usd += (spent + g["rest_usd"]) / draws
                var_proved += g["proved"] / draws
    return {"model": model, "k": k, "turns": t, "goals": len(goals), "recorded_usd": round(base_usd, 2),
            "variants_usd": round(var_usd, 2), "delta_usd": round(var_usd - base_usd, 2),
            "variants_spent_usd": round(var_spent, 2), "goals_won_by_variants": round(won, 1),
            "recorded_proved": base_proved, "variants_proved": round(var_proved, 1)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("runs", nargs="+")
    ap.add_argument("--out", required=True)
    ap.add_argument("--k", default="2,3")
    ap.add_argument("--turns", default="2,4,6")
    ap.add_argument("--draws", type=int, default=2000)
    a = ap.parse_args()
    goals, pool = load(a.runs)
    rng = random.Random(0)
    ts, ks = list(map(int, a.turns.split(","))), list(map(int, a.k.split(",")))
    noplan = [v for v in pool if not v["after_plan"]]

    def rate(vs, t):
        return round(sum(1 for v in vs if v["ok"] and len(v["turns"]) <= t) / max(1, len(vs)), 3)
    turn_usd = [u for v in pool for u in v["turns"]]
    rows = [simulate(goals, pool, k, t, a.draws, rng, "pooled") for k in ks for t in ts]
    rows += [simulate(goals, noplan, k, t, a.draws, rng, "pooled-no-plan") for k in ks for t in ts]
    rows += [simulate(goals, pool, k, t, a.draws, rng, "same-goal") for k in ks for t in ts]
    rows += [simulate(goals, pool, k, t, a.draws, rng, "same-goal-no-plan") for k in ks for t in ts]
    report = {"runs": a.runs, "goals_open_after_first_dialog": len(goals), "later_dialogs": len(pool),
              "later_dialogs_without_plan": len(noplan),
              "later_dialog_success_within_turns": {str(t): rate(pool, t) for t in ts},
              "later_dialog_without_plan_success_within_turns": {str(t): rate(noplan, t) for t in ts},
              "goals_with_later_dialogs": sum(1 for g in goals if g["later"]),
              "later_dialog_turn_usd_median": round(statistics.median(turn_usd), 4) if turn_usd else None,
              "recorded_rest_usd": round(sum(g["rest_usd"] for g in goals), 2),
              "recorded_proved": sum(g["proved"] for g in goals), "simulation": rows, "goals": goals}
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "variants-sim.json").write_text(json.dumps(report, indent=1))
    print(json.dumps({k: v for k, v in report.items() if k != "goals"}, indent=1))


if __name__ == "__main__":
    main()
