"""Regression tests for the API's admission, quotas, spending, deadlines and kill switch.
No model calls and no Docker.

Run: .venv/bin/python tests/test_server_controls.py
"""
import json, os, pathlib, sys, tempfile, threading, time
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
DATA = pathlib.Path(tempfile.mkdtemp(prefix="pf-server-test-"))
os.environ.update(PF_DATA=str(DATA), PF_PREWARM="0", PF_ADMIN_KEY="admin-test", PF_JUDGE_KEY="judge-test")
os.environ.pop("PF_MODE", None)
sys.path[:0] = [str(ROOT), str(ROOT / "harness")]

from fastapi import HTTPException  # noqa: E402
from starlette.requests import Request  # noqa: E402
import binary_check, judge, passport, task as taskmod  # noqa: E402
from server import app as api, controls  # noqa: E402


def request(ip="203.0.113.7", **headers):
    return Request({"type": "http", "method": "POST", "path": "/", "client": (ip, 5000),
                    "headers": [(k.replace("_", "-").encode(), v.encode()) for k, v in headers.items()]})


def raises(status, fn, *a, **kw):
    try:
        fn(*a, **kw)
    except HTTPException as e:
        assert e.status_code == status, (e.status_code, e.detail)
        return e
    raise AssertionError(f"expected HTTP {status}")


def fresh_store():
    return controls.Store(pathlib.Path(tempfile.mkdtemp()) / "server.db")


def test_quota_survives_restart_and_is_per_client():
    path = pathlib.Path(tempfile.mkdtemp()) / "server.db"
    c = controls.Controls(controls.Store(path))
    c.quota(request(), "live")
    c.quota(request(), "live")
    raises(429, c.quota, request(), "live")
    c.quota(request(ip="198.51.100.1"), "live")
    restarted = controls.Controls(controls.Store(path))
    raises(429, restarted.quota, request(), "live")
    restarted.quota(request(x_judge_key="judge-test"), "live")      # judge quota is separate


def test_client_address_from_the_configured_proxy_header():
    c = controls.Controls(fresh_store())
    with patch.dict(os.environ, {"PF_CLIENT_IP_HEADER": "fly-client-ip"}):
        assert c.client(request(ip="10.0.0.2", fly_client_ip="192.0.2.9")) == "192.0.2.9"
        assert c.client(request(ip="10.0.0.2")) == "10.0.0.2"
    assert c.client(request(ip="10.0.0.2", fly_client_ip="192.0.2.9")) == "10.0.0.2"


def test_daily_live_spending_reserves_the_full_job_cap():
    store = fresh_store()
    assert store.reserve("a", 3.0, 7.0) and store.reserve("b", 3.0, 7.0)
    assert not store.reserve("c", 3.0, 7.0)         # 6 reserved + 3 > 7
    store.settle("a", 0.4)
    assert abs(store.spent_today() - 3.4) < 1e-9
    assert store.reserve("c", 3.0, 7.0)             # 0.4 + 3 + 3 <= 7
    store.settle("b", None)                         # no record: the reservation stays
    assert abs(store.spent_today() - 6.4) < 1e-9


def test_gate_refuses_when_full_and_frees_on_release():
    g = controls.Gate("check", 1)
    with g.hold():
        e = raises(503, g.acquire)
        assert e.headers["Retry-After"]
        t0 = time.monotonic()
        raises(503, g.acquire, 0.3)
        assert time.monotonic() - t0 >= 0.25
    with g.hold():
        assert g.state() == {"active": 1, "slots": 1}


def test_time_limit_stops_a_run_and_is_per_thread():
    t0 = time.monotonic()
    with judge.time_limit(0.5):
        r = judge.run(["sleep", "5"])
    assert r["exit_code"] == 124 and judge.TIMEOUT_MARK in r["output_tail"]
    assert time.monotonic() - t0 < 2
    other = {}
    with judge.time_limit(0.2):
        th = threading.Thread(target=lambda: other.update(r=judge.run(["sleep", "0.5"])))
        th.start()
        th.join()
    assert other["r"]["exit_code"] == 0                # another thread has no limit
    assert judge.deadline() is None


def test_waiting_for_a_container_slot_ends_at_the_deadline():
    with patch.object(judge, "SLOT_DIR", pathlib.Path(tempfile.mkdtemp())), patch.object(judge, "SLOTS", 1):
        got = {}
        with judge.container_slot() as held:
            assert held == 0

            def waiter():
                with judge.time_limit(0.3), judge.container_slot() as slot:
                    got["slot"] = slot
            th = threading.Thread(target=waiter)
            t0 = time.monotonic()
            th.start()
            th.join(3)
            assert not th.is_alive() and got["slot"] is None and time.monotonic() - t0 < 1.5


def test_binary_timeout_is_not_a_refutation():
    t = taskmod.load()
    stopped = {"exit_code": 124, "elapsed_ms": 1, "output_tail": judge.TIMEOUT_MARK}
    with patch.object(judge, "in_container", return_value=stopped):
        b = binary_check.property_tests(pathlib.Path(tempfile.mkdtemp()), t, 5, 0, {})
    assert b["status"] == "TIMEOUT" and not b["violations"]


def test_timed_out_check_gives_an_unresolved_passport_with_the_reason():
    t = taskmod.load()
    stopped = {"command": ["x"], "exit_code": 124, "elapsed_ms": 1, "output_tail": judge.TIMEOUT_MARK}
    j = {"accepted": False, "elapsed_ms": 1, "solution_tree_sha256": "x",
         "checks": {"tree": {"passed": True, "problems": []}, "impl_scan": {"passed": True, "problems": []},
                    "comparator": stopped}}
    b = {"status": "TIMEOUT", "cases": 0, "followup_cases": 0, "violations": {}}
    with patch.object(judge, "image_id", return_value="test-image"):
        p = passport.build(t, ROOT / "formal/candidate/Solution.lean", j, b)
    assert p["status"] == "UNRESOLVED"
    assert all(r["status"] == "UNRESOLVED" for r in p["requirements"])
    assert any("time limit" in r for r in p["proof_check"]["reasons"])


def test_requests_cannot_reach_hidden_variants_or_paths():
    raises(404, api.public_task, "payouts-flagship-h1")
    raises(404, api.public_task, str(ROOT / "hidden/payouts-flagship-h1"))
    raises(404, api.public_task, "../hidden/payouts-flagship-h1")
    assert api.public_task("payout-flagship").id == "payout-flagship"


def live_request():
    return api.ForgeRequest(task="payout-flagship", mode="live")


def test_live_admission_kill_switch_and_operator_stop():
    store = fresh_store()
    gate = threading.Event()
    with patch.object(api, "CTRL", controls.Controls(store)), \
            patch.object(api, "run_live", lambda d, t, arm: gate.wait(5)):
        j = api.create_job(live_request(), request())
        raises(503, api.create_job, live_request(), request(ip="198.51.100.2"))   # one live job at a time
        assert store.used("198.51.100.2", "live") == 0                            # refused before counting
        gate.set()
        for _ in range(50):
            if api.CTRL.live.active == 0:
                break
            time.sleep(0.05)
        assert api.CTRL.live.active == 0 and api.CTRL.jobs.active == 0
        raises(403, api.admin_mode, api.ModeRequest(mode="replay"), request())
        api.admin_mode(api.ModeRequest(mode="replay"), request(x_admin_key="admin-test"))
        raises(503, api.create_job, live_request(), request(ip="198.51.100.3"))
        assert controls.Controls(store).mode() == "replay"                        # survives a restart
        assert j["mode"] == "live"


def test_daily_cap_refuses_live_jobs():
    store = fresh_store()
    with patch.dict(os.environ, {"PF_DAILY_LIVE_USD": "5", "PF_JOB_BUDGET_USD": "3", "PF_MAX_LIVE": "3"}), \
            patch.object(api, "CTRL", controls.Controls(store)), \
            patch.object(api, "run_live", lambda d, t, arm: None):
        api.create_job(live_request(), request(ip="192.0.2.1"))
        raises(503, api.create_job, live_request(), request(ip="192.0.2.2"))


def test_live_job_runs_the_contributor_tier_and_settles_actual_spend():
    store = fresh_store()
    seen = {}

    class Agent:
        def __init__(self, cmd, **kw):
            seen["cmd"] = cmd
            out = pathlib.Path(cmd[cmd.index("--out") + 1])
            (out / "summary.json").write_text(json.dumps({"budget": {"usd_list": 2.7, "usd_actual": 0.4}}))

        def wait(self, timeout=None):
            return 0
    with patch.object(api, "CTRL", controls.Controls(store)), patch.object(api.subprocess, "Popen", Agent), \
            patch.object(api, "verify_job", lambda d, t, label: None):
        d = api.JOBS / "settle000001"
        d.mkdir(parents=True, exist_ok=True)
        api.write_json(d / "job.json", {"id": d.name, "state": "CREATED"})
        assert store.reserve(d.name, 6.0, 30.0)
        api.run_live(d, taskmod.load(), "A2")
    cmd = seen["cmd"]
    assert cmd[cmd.index("--model") + 1] == "muse-spark-1.3-contributor"
    assert abs(store.spent_today() - 0.4) < 1e-9


def test_operator_stop_kills_the_agent_and_fails_the_job():
    store = fresh_store()
    proc = api.subprocess.Popen(["sleep", "30"], start_new_session=True)
    with patch.object(api, "CTRL", controls.Controls(store)):
        d = api.JOBS / "stoptest0001"
        d.mkdir(parents=True, exist_ok=True)
        (d / "job.json").write_text(json.dumps({"id": d.name, "state": "DIAGNOSING"}))
        api.LIVE[d.name] = proc
        out = api.admin_mode(api.ModeRequest(mode="replay", stop_live=True), request(x_admin_key="admin-test"))
        assert out["stopped"] == [d.name] and proc.poll() is not None
        assert json.loads((d / "job.json").read_text())["stopped"] is True
    api.LIVE.pop(d.name, None)


def test_restart_ends_unfinished_jobs():
    d = api.JOBS / "restart00001"
    d.mkdir(parents=True, exist_ok=True)
    (d / "job.json").write_text(json.dumps({"id": d.name, "state": "CHECKING"}))
    api.recover_jobs()
    assert json.loads((d / "job.json").read_text())["state"] == "FAILED"
    last = json.loads((d / "events.jsonl").read_text().splitlines()[-1])
    assert last["state"] == "FAILED" and "restarted" in last["reason"]


def test_job_thread_error_still_ends_the_stream():
    store = fresh_store()

    def boom(d, t, src, speed):
        raise RuntimeError("synthetic")
    with patch.object(api, "CTRL", controls.Controls(store)), patch.object(api, "run_replay", boom):
        rec = sorted(p.parent.name for p in api.RECORDINGS.glob("*/events.jsonl"))[0]
        j = api.create_job(api.ForgeRequest(mode="replay", recording=rec), request())
        d = api.JOBS / j["id"]
        for _ in range(50):
            if json.loads((d / "job.json").read_text())["state"] == "FAILED":
                break
            time.sleep(0.05)
        assert json.loads((d / "job.json").read_text())["state"] == "FAILED"
        assert api.CTRL.jobs.active == 0


def test_job_records_are_never_read_half_written():
    """Reliability run 1, session 10: job creation read job.json while the job thread
    rewrote it, and returned HTTP 500."""
    d = api.JOBS / "atomic000001"
    d.mkdir(parents=True, exist_ok=True)
    api.write_json(d / "job.json", {"id": d.name, "state": "CREATED", "pad": "x" * 50_000})
    stop, errors = threading.Event(), []

    def writer():
        i = 0
        while not stop.is_set():
            api.set_job(d, state=f"S{i}")
            i += 1
    th = threading.Thread(target=writer)
    th.start()
    try:
        for _ in range(3000):
            try:
                json.loads((d / "job.json").read_text())
            except ValueError as e:
                errors.append(e)
    finally:
        stop.set()
        th.join()
    assert not errors, f"{len(errors)} partial reads"
    assert not list(d.glob(".*.tmp"))


def test_concurrent_job_updates_are_not_lost():
    d = api.JOBS / "atomic000002"
    d.mkdir(parents=True, exist_ok=True)
    api.write_json(d / "job.json", {"id": d.name})
    threads = [threading.Thread(target=lambda k=k: [api.set_job(d, **{f"k{k}": n}) for n in range(200)])
               for k in range(4)]
    for th in threads:
        th.start()
    for th in threads:
        th.join()
    j = json.loads((d / "job.json").read_text())
    assert all(j[f"k{k}"] == 199 for k in range(4)), j


def test_unhandled_errors_are_recorded_on_the_data_volume():
    import asyncio

    async def boom(req):
        raise RuntimeError("synthetic failure")
    req = Request({"type": "http", "method": "POST", "path": "/api/jobs", "headers": [], "query_string": b"",
                   "server": ("test", 80), "scheme": "http", "client": ("192.0.2.1", 1)})
    try:
        asyncio.run(api.record_errors(req, boom))
        raise AssertionError("the error was swallowed")
    except RuntimeError:
        pass
    log = (api.DATA / "errors.log").read_text()
    assert "POST /api/jobs" in log and "synthetic failure" in log


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
