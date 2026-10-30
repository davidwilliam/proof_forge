#!/usr/bin/env python3
"""Throughput of the Glimmer endpoint on agent-shaped requests, for its per-token price.

Each request is the A0 prompt of a dev task (task brief, protected spec, buggy candidate)
at the reasoning level the agents use (medium), so the output is reasoning plus a complete
Lean file, the content the drafter is accepted on in E1. Measured:
  prefill: prompt tokens / latency of a 1-token completion with a fresh cache salt
           (no prefix-cache hits), median of the runs;
  decode at concurrency 1 and 2: completion tokens of all requests in flight / wall time
           from the first send to the last response, with a fresh cache salt per request.
Writes JSON with the raw per-request numbers.

Usage: bench_glimmer.py [--model glimmer/muse-glimmer-30b] [--tasks id,id] [--rounds 2]
                        [--max-tokens 8192] [--out FILE]
"""
import argparse, json, pathlib, secrets, statistics, sys, time
from concurrent.futures import ThreadPoolExecutor

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "agents"))
sys.path.insert(0, str(ROOT / "harness"))
import baseline, repair, task as taskmod  # noqa: E402
from meta_client import chat  # noqa: E402


def messages_for(t):
    system = repair.task_brief(t, "repair") + baseline.PROTOCOL
    spec = "\n\n".join(f"=== {p} ===\n{(t.root / p).read_text()}" for p in t.readable[:-1])
    user = spec + "\n\n=== candidate/Solution.lean (current, buggy) ===\n" + t.start.read_text()
    return [{"role": "system", "content": system}, {"role": "user", "content": user}]


def one(model, msgs, max_tokens, purpose):
    t0 = time.monotonic()
    r = chat(model, msgs, purpose, max_tokens=max_tokens, timeout=1800, retries=0,
             reasoning_effort="medium", cache_salt=secrets.token_hex(8))
    dt = time.monotonic() - t0
    u = r.get("usage") or {}
    return {"t0": t0, "t1": t0 + dt, "latency_s": round(dt, 3), "prompt_tokens": u.get("prompt_tokens"),
            "completion_tokens": u.get("completion_tokens"), "finish": r["choices"][0].get("finish_reason")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="glimmer/muse-glimmer-30b")
    ap.add_argument("--tasks", default="transfers-overdraft-b1,rate-limiters-window-b1")
    ap.add_argument("--rounds", type=int, default=2)
    ap.add_argument("--max-tokens", type=int, default=8192)
    ap.add_argument("--out", type=pathlib.Path)
    a = ap.parse_args()
    prompts = [messages_for(taskmod.load(x)) for x in a.tasks.split(",")]
    out = {"model": a.model, "tasks": a.tasks.split(","), "max_tokens": a.max_tokens, "prefill": [], "decode": {}}
    for m in prompts:   # warm-up, not counted
        one(a.model, m, 16, "bench:warmup")
    for _ in range(a.rounds):
        for m in prompts:
            out["prefill"].append(one(a.model, m, 1, "bench:prefill"))
    for conc in (1, 2):
        runs = []
        for _ in range(a.rounds):
            for i in range(len(prompts)):
                batch = [prompts[(i + k) % len(prompts)] for k in range(conc)]
                with ThreadPoolExecutor(conc) as ex:
                    rs = list(ex.map(lambda m: one(a.model, m, a.max_tokens, f"bench:decode{conc}"), batch))
                wall = max(r["t1"] for r in rs) - min(r["t0"] for r in rs)
                runs.append({"requests": rs, "wall_s": round(wall, 3),
                             "completion_tokens": sum(r["completion_tokens"] or 0 for r in rs)})
        out["decode"][str(conc)] = runs
    pf = [r["prompt_tokens"] / r["latency_s"] for r in out["prefill"]]
    out["prefill_tok_s_median"] = round(statistics.median(pf), 1)
    for conc, runs in out["decode"].items():
        out[f"decode_tok_s_conc{conc}"] = round(sum(r["completion_tokens"] for r in runs) / sum(r["wall_s"] for r in runs), 2)
    for r in out["prefill"] + [q for runs in out["decode"].values() for x in runs for q in x["requests"]]:
        r.pop("t0"), r.pop("t1")
    text = json.dumps(out, indent=2) + "\n"
    if a.out:
        a.out.write_text(text)
    print(json.dumps({k: v for k, v in out.items() if k.endswith("median") or k.startswith("decode_tok")}))


if __name__ == "__main__":
    main()
