#!/usr/bin/env python3
"""Per-run figures of the proofforge-full runs of results/frontier-3 on rw-compound-comp, from the
committed run records only (summary.json, calls.jsonl, mcp-calls.jsonl, events.jsonl.gz,
ledger.json). No model calls, no Lean.

For each run: the required theorems of the final candidate; when the five per-call requirements
were all proved in one lean_build (minutes from the first model call, list dollars of the calls
made up to then); when the run first wrote `ProofForgeFin.Accumulator.Market` glue (an edit or
snippet with `M.Settle`, `M.Act` or `Market.`); lean_build calls, failed ones, failed ones whose
result began inside a Lean message, the longest streak of failed builds in a row and the list
dollars spent in streaks of three or more; check_snippet_fast calls; and which list helpers the
run proved itself (ledger.json).

Usage: python3 results/library-compound-gaps-1/diagnose.py [--json]
"""
import bisect, collections, gzip, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = ROOT / "results/frontier-3/runs/rw-compound-comp"
PER_CALL = {"req_calls_succeed", "req_supply_hook", "req_borrow_hook", "req_claim", "req_set_speeds"}
SHORT = {"req_calls_succeed": "CS", "req_supply_hook": "SH", "req_borrow_hook": "BH", "req_claim": "CL",
         "req_set_speeds": "SP", "req_rewards_bounded": "RB", "req_account_bounded": "AB", "req_no_backdated": "NB"}
MARKET = re.compile(r"M\.Settle|M\.Act|M\.Inv|Market\.(?:Settle|Act|Reach|Step|Inv)|Market St\b")
HELPERS = {
    "modify_congr": re.compile(r"modify_?congr|modCongr", re.I),
    "getD_of_forall": re.compile(r"rec_?(sup|bor|le)|Rec_?le|RecLe|acct_(rec|supplier|borrower|supply|borrow)_le", re.I),
    "getD_modify_of_keeps": re.compile(r"keep", re.I),
}


def run_figures(run):
    s = json.loads((run / "summary.json").read_text())
    calls = [json.loads(l) for l in open(run / "calls.jsonl")]
    ct = [c["t"] for c in calls]
    cum, a = [], 0.0
    for c in calls:
        a += c.get("usd_list") or 0
        cum.append(a)
    t0 = ct[0]

    def usd(t):
        i = bisect.bisect_right(ct, t) - 1
        return round(cum[i], 2) if i >= 0 else 0.0

    def mins(t):
        return round((t - t0) / 60, 1)
    mcp = [json.loads(l) for l in open(run / "mcp-calls.jsonl")]
    proved, per_call_done, market_at = set(), None, None
    builds = []
    for r in mcp:
        if r["tool"] == "lean_build":
            builds.append(r)
            m = re.search(r"proved in this build: \d+ of 8: ([^.]*)\.", r["result"])
            if m:
                proved |= {x.strip() for x in m.group(1).split(",")}
                if per_call_done is None and PER_CALL <= proved:
                    per_call_done = {"minutes": mins(r["t"]), "usd_list": usd(r["t"])}
        if market_at is None and r["tool"] in ("check_snippet_fast", "try_snippet") and MARKET.search(r["args"].get("code", "")):
            market_at = {"minutes": mins(r["t"]), "usd_list": usd(r["t"])}
    # Results as the model received them (the log keeps only their first 4,000 characters).
    texts = []
    kind, edits = {}, []
    for line in gzip.open(run / "events.jsonl.gz", "rt"):
        e = json.loads(line)
        p = e.get("payload") or {}
        if e.get("payload_type") == "tool.result":
            t = p.get("text") or ""
            if t.startswith("$ lake build Solution"):
                texts.append(t)
        elif e.get("payload_type") == "task.lifecycle.proposed":
            kind[p["task_id"]] = p["event"].get("task_kind")
        elif e.get("payload_type") == "task.lifecycle.output" and kind.get(p.get("task_id")) == "tool.edit_file":
            edits.append(p["event"].get("chunk") or "")
    failed = [t for t in texts if re.search(r"exit code [1-9]", t[:80])]
    mid = [t for t in failed if not re.match(r"\$ lake build Solution\nexit code \d+ \(\d+ ms\)\n(error|warning|\[\.\.\.)", t)]
    streaks, cur, longest = [], [], 0
    for b in builds:
        if re.search(r"exit code [1-9]", b["result"][:80]):
            cur.append(b)
            longest = max(longest, len(cur))
        else:
            if len(cur) >= 3:
                streaks.append((cur[0]["t"], b["t"]))
            cur = []
    if len(cur) >= 3:
        streaks.append((cur[0]["t"], ct[-1]))
    in_streaks = round(sum(usd(b) - usd(a) for a, b in streaks), 2)
    if market_at is None and any(MARKET.search(x) for x in edits):
        market_at = {"minutes": None, "usd_list": None, "note": "in an edit of the file only"}
    names = [d["name"] for d in json.loads((run / "ledger.json").read_text())["proved"]]
    helpers = {k: sorted(n for n in names if rx.search(n)) for k, rx in HELPERS.items()}
    st = s["final_theorem_status"]
    return {
        "run": run.name,
        "final": " ".join(SHORT[k] + ("+" if v == "PROVED" else "-") for k, v in st.items()),
        "proved": sum(v == "PROVED" for v in st.values()),
        "usd_list": round(s["meter"]["usd_list"], 2),
        "minutes": round(s["elapsed_s"] / 60, 1),
        "ended_by": s["ended_by"],
        "model_calls": s["model_calls"],
        "per_call_requirements_done": per_call_done,
        "market_glue_from": market_at,
        "lean_build": len(builds),
        "failed_builds": len(failed),
        "failed_builds_beginning_inside_a_message": len(mid),
        "longest_failed_streak": longest,
        "usd_list_in_failed_streaks_of_3_or_more": in_streaks,
        "check_snippet_fast": sum(r["tool"] == "check_snippet_fast" for r in mcp),
        "search_library": sum(r["tool"] == "search_library" for r in mcp),
        "own_list_helpers": helpers,
    }


def main():
    rows = [run_figures(BASE / f"proofforge-full-{n}") for n in range(1, 11)]
    if "--json" in sys.argv:
        print(json.dumps(rows, indent=1, ensure_ascii=False))
        return
    for r in rows:
        pc = r["per_call_requirements_done"]
        mk = r["market_glue_from"]
        print(f"{r['run']:<19} {r['final']}  ${r['usd_list']:5.2f} {r['minutes']:5.1f} min  "
              f"per-call done: {'no' if not pc else str(pc['minutes']) + ' min $' + str(pc['usd_list'])}  "
              f"Market glue from: {'no' if not mk else 'an edit only' if mk['minutes'] is None else str(mk['minutes']) + ' min $' + str(mk['usd_list'])}  "
              f"builds {r['lean_build']} failed {r['failed_builds']} mid {r['failed_builds_beginning_inside_a_message']} "
              f"streak {r['longest_failed_streak']} ${r['usd_list_in_failed_streaks_of_3_or_more']} in streaks  "
              f"snippets {r['check_snippet_fast']}")


if __name__ == "__main__":
    main()
