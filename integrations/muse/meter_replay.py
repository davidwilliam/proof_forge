#!/usr/bin/env python3
"""Replay recorded Muse Code call logs through the meter under the byte bound and the prefix bound.

A run's `calls.jsonl` records, per model call, the caller (role and the opening of its
instructions), the reasoning effort, the request's size in bytes and in input items, and the
reported usage; it holds no message contents. The replay rebuilds a request body per call that has
the recorded size and item count, and the prefix relation inferred from the log: a call extends
the previous call of the same caller and effort when it has more items and at least as many bytes
(its new items then carry exactly the byte difference); any other call starts a new conversation.
Each body goes through Meter.admit and is settled with the recorded usage, one call at a time
(the recorded calls that overlapped in time are replayed in the order they settled).

For each rule it reports whether the recorded calls all fit the cap, the largest reservation
held, whether any reported input exceeded the bound used (`input_bound_violations`, which must
stay 0), and for a run stopped by the dollar rule, the spend at which its final request (the one
refused) would have stopped the run: the cap minus that request's worst case with the minimum
output allowance. That is how much of the cap the run could have used before the rule stopped it.

The inferred prefix relation is a reconstruction: the live meter compares the actual items.

Usage: meter_replay.py RUN_DIR... [--cap 10] [--out FILE]
"""
import argparse, json, pathlib, sys, tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import meter as metermod  # noqa: E402
from budget import BudgetExceeded, list_cost, _list_prices  # noqa: E402


def item_of(conv, i, n):
    """A synthetic input item whose JSON is `n` bytes long (at least its minimal length)."""
    base = {"type": "message", "role": "user", "content": f"{conv}:{i}:"}
    pad = n - len(json.dumps(base))
    if pad > 0:
        base["content"] += "x" * pad
    return base


def bodies(calls):
    """(body, recorded call) per call with usage or a refusal, in log order."""
    state, out, nconv = {}, [], 0
    for c in calls:
        if not c.get("usage") and not c.get("refused"):
            continue
        key = (c.get("role"), c.get("instructions_head"), c.get("effort"), c.get("model"))
        prev = state.get(key)
        n = int(c.get("items") or 0)
        if prev and n > len(prev["input"]) and c["bytes"] >= prev["bytes"]:
            k = n - len(prev["input"])
            extra = c["bytes"] - prev["bytes"]
            conv = prev["conv"]
            new = [item_of(conv, len(prev["input"]) + j, extra // k + (1 if j < extra % k else 0)) for j in range(k)]
            items = prev["input"] + new
        else:
            nconv += 1
            conv = f"c{nconv}"
            items = [item_of(conv, j, max(1, c["bytes"] // max(1, n) // 2)) for j in range(n)]
        body = {"model": c.get("model"), "instructions": f"{c.get('instructions_head')}|{c.get('role')}",
                "reasoning": {"effort": c.get("effort")}, "input": items,
                "max_output_tokens": c.get("max_output_tokens_requested") or metermod.MAX_OUTPUT}
        if c.get("usage"):   # as in the meter, only a settled call is a prefix for later ones
            state[key] = {"input": items, "bytes": c["bytes"], "conv": conv}
        out.append((body, c))
    return out


def replay(calls, cap=10.0, prefix=True):
    m = metermod.Meter(tempfile.mkdtemp(prefix="pf-meter-replay-"), usd_cap=cap, prefix=prefix)
    rec = {"rule": "prefix" if prefix else "bytes", "calls": 0, "refused_at": None, "max_reserved_usd": 0.0,
           "over_cap": False, "bounds": {"prefix": 0, "bytes": 0}}
    final = None
    for i, (body, c) in enumerate(bodies(calls)):
        info = {}
        if c.get("refused"):
            final = (body, c)
            continue
        try:
            tok, _ = m.admit(body, c["bytes"], info)
        except BudgetExceeded:
            rec["refused_at"] = i
            break
        rec["max_reserved_usd"] = max(rec["max_reserved_usd"], round(m.budget.usd_list, 4))
        rec["over_cap"] = rec["over_cap"] or m.budget.usd_list > cap + 1e-9
        rec["bounds"][info["bound"]] += 1
        m.settle(tok, c.get("usage"), {"role": c.get("role") or "main"})
        rec["calls"] += 1
        final = (body, c)
    rec["usd_list"] = round(m.budget.usd_list, 4)
    rec["input_bound_violations"] = m.budget.bound_violations
    if final is not None:
        body, c = final
        with m.lock:
            bound, kind, _ = m.input_bound(body, c["bytes"])
        p, _, o = _list_prices(body["model"])
        worst = bound * p / 1e6 + metermod.MIN_OUTPUT * o / 1e6
        rec["final_request"] = {"bytes": c["bytes"], "input_bound": bound, "bound": kind,
                                "worst_case_usd": round(worst, 4), "usable_usd": round(cap - worst, 4)}
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("runs", nargs="+")
    ap.add_argument("--cap", type=float, default=10.0)
    ap.add_argument("--out")
    a = ap.parse_args()
    rows = []
    for d in map(pathlib.Path, a.runs):
        calls = [json.loads(l) for l in (d / "calls.jsonl").read_text().splitlines() if l.strip()]
        s = json.loads((d / "summary.json").read_text()) if (d / "summary.json").is_file() else {}
        row = {"run": "/".join(d.parts[-2:]), "ended_by": s.get("ended_by"),
               "recorded_usd_list": (s.get("meter") or {}).get("usd_list"),
               "bytes": replay(calls, a.cap, prefix=False), "prefix": replay(calls, a.cap, prefix=True)}
        rows.append(row)
        print(json.dumps({"run": row["run"], "ended_by": row["ended_by"], "recorded": row["recorded_usd_list"],
                          "usable_bytes": row["bytes"].get("final_request", {}).get("usable_usd"),
                          "usable_prefix": row["prefix"].get("final_request", {}).get("usable_usd"),
                          "violations": [row["bytes"]["input_bound_violations"], row["prefix"]["input_bound_violations"]],
                          "over_cap": [row["bytes"]["over_cap"], row["prefix"]["over_cap"]]}), flush=True)
    if a.out:
        pathlib.Path(a.out).write_text(json.dumps(rows, indent=1) + "\n")


if __name__ == "__main__":
    main()
