#!/usr/bin/env python3
"""Build the payout-sidecar executable from a candidate in a fresh container, then run
requirement-derived property tests and regression attacks against the binary.

Usage: binary_check.py <workspace-dir | candidate.lean> [--cases N] [--seed S] [--json out]
"""
import argparse, json, pathlib, random, shutil, sys, tempfile, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import judge, oracle  # noqa: E402

FLAGSHIP = {
    "state": {"balances": [[1, 1000], [2, 0], [3, 0], [4, 0]], "auth": [[1, 1]], "applied": [3]},
    "request": {"txId": 7, "requester": 1, "source": 1, "recipients": [2, 3, 4], "amount": 100},
}


def gen_case(rng):
    n_acc = rng.randint(2, 6)
    accts = rng.sample(range(1, 50), n_acc)
    balances = [[a, rng.choice([0, rng.randint(0, 50), rng.randint(0, 5000)])] for a in accts]
    auth = [[q, s] for q in accts for s in accts if rng.random() < 0.3]
    applied = rng.sample(range(1, 30), rng.randint(0, 4))
    src = rng.choice(accts)
    others = [a for a in accts if a != src]
    rec = rng.sample(others, rng.randint(1, len(others)))
    bal = dict(balances)
    amount = rng.randint(1, max(1, bal[src])) if bal[src] > 0 else rng.randint(1, 10)
    req = {"txId": rng.choice([rng.randint(30, 99)] * 3 + applied[:1]), "requester": src,
           "source": src, "recipients": rec, "amount": amount}
    if [src, src] not in auth and rng.random() < 0.8:
        auth.append([src, src])
    # Mutate into an invalid request about 30% of the time.
    m = rng.random()
    if m < 0.05: req["amount"] = 0
    elif m < 0.10: req["recipients"] = []
    elif m < 0.15 and rec: req["recipients"] = rec + [rec[0]]
    elif m < 0.20: req["recipients"] = rec + [src]
    elif m < 0.25: req["amount"] = bal[src] + rng.randint(1, 100)
    elif m < 0.30: req["requester"] = rng.choice(accts + [99])
    return {"state": {"balances": balances, "auth": auth, "applied": applied}, "request": req}


def check_binary(arg, n_cases=2000, seed=0):
    t0 = time.monotonic()
    ws = judge.load_workspace(arg)
    files = judge.candidate_files(ws)
    project = judge.fresh_project(ws, files)
    rng = random.Random(seed)
    cases = [FLAGSHIP] + [gen_case(rng) for _ in range(n_cases)]
    (project / "tests.jsonl").write_text("\n".join(json.dumps(c) for c in cases) + "\n")
    build = judge.in_container(project,
        "lake build payout-sidecar >/tmp/build.log 2>&1 || { tail -20 /tmp/build.log; exit 3; }; "
        "sha256sum .lake/build/bin/payout-sidecar | cut -d' ' -f1 > binary.sha256; "
        ".lake/build/bin/payout-sidecar < tests.jsonl > out.jsonl")
    result = {"candidate": str(arg), "build": {k: build[k] for k in ("exit_code", "elapsed_ms")},
              "cases": len(cases), "violations": {}, "witnesses": []}
    if build["exit_code"] not in (0, 2):
        result["build"]["output_tail"] = build["output_tail"]
        result["status"] = "BUILD_FAILED"
        return result
    result["binary_sha256"] = (project / "binary.sha256").read_text().strip()
    outs = [json.loads(l) for l in (project / "out.jsonl").read_text().splitlines()]
    resubmits = []
    for c, o in zip(cases, outs):
        for rid, msg in oracle.check(c["state"], c["request"], o):
            result["violations"][rid] = result["violations"].get(rid, 0) + 1
            if len(result["witnesses"]) < 5 or c is FLAGSHIP:
                result["witnesses"].append({"requirement": rid, "message": msg, "input": c, "output": o})
        if o.get("outcome") == "ok":
            resubmits.append({"state": o["state"], "request": c["request"]})
    # Phase 2: resubmitting a successful request must be rejected with no state change.
    (project / "tests2.jsonl").write_text("\n".join(json.dumps(c) for c in resubmits) + "\n")
    run2 = judge.in_container(project, ".lake/build/bin/payout-sidecar < tests2.jsonl > out2.jsonl")
    outs2 = [json.loads(l) for l in (project / "out2.jsonl").read_text().splitlines()] if run2["exit_code"] in (0, 2) else []
    for c, o in zip(resubmits, outs2):
        if o.get("outcome") != "rejected" or o.get("state", {}).get("applied") != c["state"]["applied"] \
                or dict(o["state"]["balances"]) != dict(c["state"]["balances"]):
            result["violations"]["REQ-IDEMPOTENCY"] = result["violations"].get("REQ-IDEMPOTENCY", 0) + 1
            if len(result["witnesses"]) < 6:
                result["witnesses"].append({"requirement": "REQ-IDEMPOTENCY",
                                            "message": "resubmitted request was not rejected cleanly",
                                            "input": c, "output": o})
    result["resubmit_cases"] = len(resubmits)
    result["flagship_output"] = outs[0]
    result["status"] = "PASS" if not result["violations"] else "REFUTED"
    result["elapsed_ms"] = int((time.monotonic() - t0) * 1000)
    shutil.rmtree(project, ignore_errors=True)
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("candidate")
    ap.add_argument("--cases", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--json")
    a = ap.parse_args()
    r = check_binary(a.candidate, a.cases, a.seed)
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(r, indent=2) + "\n")
    fb = r.get("flagship_output", {}).get("state", {}).get("balances")
    print(f"{r['status']}  {a.candidate}  cases={r['cases']}+{r.get('resubmit_cases', 0)}  "
          f"violations={r['violations']}  flagship={fb}")
    sys.exit(0 if r["status"] == "PASS" else 1)
