#!/usr/bin/env python3
"""Host smoke test of a deployed ProofForge API: the judge accepts a recorded repair and
rejects attacks on the target host, with Comparator's sandbox enabled.

Usage: smoke.py BASE_URL [--out reports/host-smoke/<name>.json]
Reads PF_JUDGE_KEY from the environment or .env (the judge quota); makes no model calls.
"""
import argparse, json, pathlib, time, urllib.error, urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
KERNELS = 6


def judge_key():
    import os
    if os.environ.get("PF_JUDGE_KEY"):
        return os.environ["PF_JUDGE_KEY"]
    env = ROOT / ".env"
    for line in env.read_text().splitlines() if env.exists() else []:
        if line.startswith("PF_JUDGE_KEY="):
            return line.split("=", 1)[1].strip()
    return ""


class Client:
    def __init__(self, base):
        self.base, self.key = base.rstrip("/"), judge_key()

    def call(self, method, path, body=None, timeout=600):
        data = json.dumps(body).encode() if body is not None else None
        req = urllib.request.Request(self.base + path, data=data, method=method,
                                     headers={"Content-Type": "application/json", "X-Judge-Key": self.key})
        t0 = time.monotonic()
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.status, json.loads(r.read()), time.monotonic() - t0
        except urllib.error.HTTPError as e:
            return e.code, {"detail": e.read().decode(errors="replace")[:500]}, time.monotonic() - t0

    def events(self, job, timeout=900):
        """Read a job's event stream until a terminal job event."""
        req = urllib.request.Request(f"{self.base}/api/jobs/{job}/events")
        out, end = [], time.monotonic() + timeout
        with urllib.request.urlopen(req, timeout=timeout) as r:
            for raw in r:
                line = raw.decode().strip()
                if line.startswith("data: "):
                    e = json.loads(line[6:])
                    out.append(e)
                    if e.get("kind") == "job" and e.get("state") in ("COMPLETE", "PARTIAL", "FAILED", "TIMEOUT", "BUDGET_STOP"):
                        return out
                if time.monotonic() > end:
                    break
        return out


def verify_case(c, name, path, expect):
    status, p, secs = c.call("POST", "/api/verify", {"task": "payout-flagship", "source": (ROOT / path).read_text()})
    if status != 200:
        return {"case": name, "passed": False, "http": status, "detail": p, "seconds": round(secs, 1)}
    got = {"status": p["status"], "proof_accepted": p["proof_check"]["accepted"],
           "executable": p["executable"]["status"], "kernels": len(p["checks"]["comparator_kernels"]),
           "reasons": p["proof_check"]["reasons"][:3], "passport_sha256": p["passport_sha256"],
           "judge_image": p["toolchain"]["judge_image"],
           "requirements": {r["id"]: r["status"] for r in p["requirements"]}}
    return {"case": name, "candidate": path, "seconds": round(secs, 1), **got,
            "passed": all(got[k] == v for k, v in expect.items())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("--out")
    a = ap.parse_args()
    c = Client(a.base)
    results = []

    status, h, _ = c.call("GET", "/api/health")
    results.append({"case": "health", "passed": status == 200 and h.get("in_image") and h.get("ready"), **h})

    results.append(verify_case(c, "accepted repair", "formal/evidence/muse-repair-002/Solution.lean",
                               {"status": "VERIFIED", "proof_accepted": True, "executable": "PASS", "kernels": KERNELS}))
    results.append(verify_case(c, "seeded tests-pass attack", "formal/attacks/g2_bulk_rounding.lean",
                               {"status": "UNRESOLVED", "proof_accepted": False, "executable": "PASS"}))
    results.append(verify_case(c, "complete-proof attack", "formal/attacks/d2_clear_auth.lean",
                               {"status": "REFUTED", "proof_accepted": False, "executable": "REFUTED"}))
    results.append(verify_case(c, "code override attack", "formal/attacks/c_implemented_by.lean",
                               {"proof_accepted": False, "executable": "REFUTED"}))

    status, j, _ = c.call("POST", "/api/jobs", {"mode": "replay", "recording": "flagship-a2-run7", "speed": 100})
    if status == 200:
        t0 = time.monotonic()
        ev = c.events(j["id"])
        pp = [e for e in ev if e.get("kind") == "passport"]
        results.append({"case": "replay with fresh check", "job": j["id"], "seconds": round(time.monotonic() - t0, 1),
                        "events": len(ev), "final": ev[-1] if ev else None,
                        "passport": pp[-1] if pp else None,
                        "passed": bool(pp) and pp[-1]["status"] == "VERIFIED" and ev[-1].get("state") == "COMPLETE"})
    else:
        results.append({"case": "replay with fresh check", "passed": False, "http": status, "detail": j})

    status, ch, secs = c.call("POST", "/api/challenge", {"variant": "payouts-flagship-h1"})
    results.append({"case": "hidden challenge", "http": status, "seconds": round(secs, 1),
                    "status": ch.get("status"), "witness": (ch.get("witness") or {}).get("message"),
                    "passed": status == 200 and ch.get("status") == "REFUTED" and secs < 45})

    state = {"balances": [[1, 100], [2, 0], [3, 0], [4, 0]], "auth": [[1, 1]], "applied": []}
    req = {"txId": 1, "requester": 1, "source": 1, "recipients": [2, 3, 4], "amount": 100}
    paid = {}
    for build in ("buggy", "repaired"):
        status, r, secs = c.call("POST", "/api/payout", {"build": build, "state": state, "request": req})
        paid[build] = {"http": status, "seconds": round(secs, 1), "result": r.get("result"),
                       "passport_sha256": r.get("passport_sha256")}
    results.append({"case": "payout sidecar", **paid,
                    "passed": all(v["http"] == 200 for v in paid.values())})

    report = {"base": a.base, "recorded_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
              "passed": all(r["passed"] for r in results), "results": results}
    for r in results:
        print(f"{'PASS' if r['passed'] else 'FAIL'}  {r['case']}  {r.get('seconds', '')}")
    if a.out:
        pathlib.Path(a.out).parent.mkdir(parents=True, exist_ok=True)
        pathlib.Path(a.out).write_text(json.dumps(report, indent=2) + "\n")
    raise SystemExit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
