#!/usr/bin/env python3
"""Demo reliability check of the deployed stack: N consecutive demo sessions, then failure
drills. Each session does what the demo shows: open the web pages, replay the accepted
recording to a fresh check, run the hidden challenge, call both payout builds and fetch the
Passport. No model calls.

Usage: reliability.py API_BASE WEB_BASE [--sessions 20] [--drills] [--app proofforge]
       [--out reports/reliability/<name>.json]
Drills need PF_ADMIN_KEY (environment or .env) and, for the restart drill, flyctl.
"""
import argparse, json, pathlib, subprocess, sys, threading, time, urllib.error, urllib.request

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import smoke  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
PAGES = ["/", "/forge", "/results", "/app", "/challenge"]
STATE = {"balances": [[1, 100], [2, 0], [3, 0], [4, 0]], "auth": [[1, 1]], "applied": []}
REQ = {"txId": 1, "requester": 1, "source": 1, "recipients": [2, 3, 4], "amount": 100}


def env_value(name):
    import os
    if os.environ.get(name):
        return os.environ[name]
    for line in (ROOT / ".env").read_text().splitlines():
        if line.startswith(name + "="):
            return line.split("=", 1)[1].strip()
    return ""


def get(url, timeout=30):
    t0 = time.monotonic()
    try:
        with urllib.request.urlopen(url, timeout=timeout) as r:
            r.read()
            return r.status, time.monotonic() - t0
    except urllib.error.HTTPError as e:
        return e.code, time.monotonic() - t0
    except Exception:
        return 0, time.monotonic() - t0


def session(c, web, i):
    steps, t0 = {}, time.monotonic()
    for p in PAGES:
        status, secs = get(web + p)
        steps[f"page {p}"] = {"ok": status == 200, "seconds": round(secs, 2)}
    status, j, _ = c.call("POST", "/api/jobs", {"mode": "replay", "recording": "flagship-a2-run7", "speed": 100})
    if status == 200:
        s0 = time.monotonic()
        ev = c.events(j["id"])
        pp = [e for e in ev if e.get("kind") == "passport"]
        ok = bool(pp) and pp[-1]["status"] == "VERIFIED" and ev[-1].get("state") == "COMPLETE"
        steps["replay and fresh check"] = {"ok": ok, "seconds": round(time.monotonic() - s0, 1),
                                           "passport_sha256": pp[-1]["passport_sha256"] if pp else None}
        if pp:
            st, _, secs = c.call("GET", f"/api/passports/{pp[-1]['passport_sha256']}")
            steps["passport fetch"] = {"ok": st == 200, "seconds": round(secs, 2)}
    else:
        steps["replay and fresh check"] = {"ok": False, "http": status, "detail": j.get("detail")}
    status, ch, secs = c.call("POST", "/api/challenge", {"variant": "payouts-flagship-h1"})
    steps["hidden challenge"] = {"ok": status == 200 and ch.get("status") == "REFUTED", "seconds": round(secs, 2)}
    for build in ("buggy", "repaired"):
        status, r, secs = c.call("POST", "/api/payout", {"build": build, "state": STATE, "request": REQ})
        steps[f"payout {build}"] = {"ok": status == 200, "seconds": round(secs, 2)}
    return {"session": i, "ok": all(s["ok"] for s in steps.values()),
            "seconds": round(time.monotonic() - t0, 1), "steps": steps}


def admin(c, mode, stop_live=False):
    req = urllib.request.Request(c.base + "/api/admin/mode", method="POST",
                                 data=json.dumps({"mode": mode, "stop_live": stop_live}).encode(),
                                 headers={"Content-Type": "application/json", "X-Admin-Key": env_value("PF_ADMIN_KEY")})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.loads(r.read())


def drill_kill_switch(c):
    before = c.call("GET", "/api/health")[1]["mode"]
    admin(c, "replay")
    status, body, _ = c.call("POST", "/api/jobs", {"task": "payout-flagship", "mode": "live"})
    st2, j, _ = c.call("POST", "/api/jobs", {"mode": "replay", "recording": "flagship-a2-run7", "speed": 100})
    ev = c.events(j["id"]) if st2 == 200 else []
    admin(c, before)
    return {"drill": "kill switch", "live_refused": status == 503, "detail": body.get("detail"),
            "replay_still_works": bool(ev) and ev[-1].get("state") == "COMPLETE", "mode_restored": before,
            "ok": status == 503 and bool(ev) and ev[-1].get("state") == "COMPLETE"}


def drill_saturation(c):
    """More simultaneous verifications than check slots: the excess is refused with 503 and
    Retry-After, the rest complete, and nothing is left running."""
    src = (ROOT / "formal/evidence/muse-repair-002/Solution.lean").read_text()
    out = []

    def one():
        out.append(c.call("POST", "/api/verify", {"task": "payout-flagship", "source": src}))
    threads = [threading.Thread(target=one) for _ in range(5)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    codes = sorted(s for s, _, _ in out)
    verified = sum(1 for s, p, _ in out if s == 200 and p.get("status") == "VERIFIED")
    gates = c.call("GET", "/api/health")[1]["gates"]
    return {"drill": "saturation", "codes": codes, "verified": verified, "gates_after": gates,
            "ok": verified >= 1 and all(s in (200, 503) for s in codes) and gates["check"]["active"] == 0}


def drill_restart(c, app):
    """Restart the machine while a job runs: the job ends with a stated reason, its stream
    closes, and a new session works after the restart."""
    st, j, _ = c.call("POST", "/api/jobs", {"mode": "replay", "recording": "flagship-a2-run7", "speed": 1})
    time.sleep(5)
    subprocess.run(["fly", "apps", "restart", app], capture_output=True, text=True, timeout=300)
    t0 = time.monotonic()
    while time.monotonic() - t0 < 600:
        st_h, h, _ = c.call("GET", "/api/health", timeout=10)
        if st_h == 200 and h.get("ready"):
            break
        time.sleep(5)
    recovered = round(time.monotonic() - t0, 1)
    ev = c.events(j["id"], timeout=60) if st == 200 else []
    after = session(c, c.web, "after restart")
    return {"drill": "restart during a job", "recovered_seconds": recovered,
            "interrupted_job_final": ev[-1] if ev else None, "session_after": after["ok"],
            "ok": bool(ev) and ev[-1].get("state") == "FAILED" and after["ok"]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("api")
    ap.add_argument("web")
    ap.add_argument("--sessions", type=int, default=20)
    ap.add_argument("--drills", action="store_true")
    ap.add_argument("--app", default="proofforge")
    ap.add_argument("--out")
    a = ap.parse_args()
    c = smoke.Client(a.api)
    c.web = a.web.rstrip("/")
    sessions = []
    for i in range(1, a.sessions + 1):
        s = session(c, c.web, i)
        sessions.append(s)
        print(f"{'PASS' if s['ok'] else 'FAIL'}  session {i}  {s['seconds']} s", flush=True)
    drills = []
    if a.drills:
        for d in (drill_kill_switch, drill_saturation, lambda c: drill_restart(c, a.app)):
            r = d(c)
            drills.append(r)
            print(f"{'PASS' if r['ok'] else 'FAIL'}  drill {r['drill']}", flush=True)
    secs = sorted(s["seconds"] for s in sessions)
    report = {"api": a.api, "web": a.web, "recorded_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
              "sessions_passed": sum(s["ok"] for s in sessions), "sessions": len(sessions),
              "session_seconds": {"min": secs[0], "median": secs[len(secs) // 2], "max": secs[-1]} if secs else None,
              "drills_passed": sum(d["ok"] for d in drills), "drills": drills, "session_records": sessions}
    if a.out:
        pathlib.Path(a.out).parent.mkdir(parents=True, exist_ok=True)
        pathlib.Path(a.out).write_text(json.dumps(report, indent=2) + "\n")
    ok = report["sessions_passed"] == len(sessions) and report["drills_passed"] == len(drills)
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
