"""Failure drills for the model API: rate limiting, server errors, malformed bodies,
rejected keys and malformed tool arguments. A local HTTP server stands in for the Meta
Model API; no model calls and no Lean runs.

Run: python3 tests/test_model_failures.py
"""
import http.server, json, os, pathlib, sys, tempfile, threading
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness")]
os.environ.setdefault("META_API_KEY", "test-key-not-used")
import budget, meta_client, repair, task as taskmod  # noqa: E402

MODEL = "muse-spark-1.3-contributor"


class FakeAPI(http.server.BaseHTTPRequestHandler):
    """Answers every request according to the class attribute `mode`."""
    mode, requests = "429", []

    def do_POST(self):
        self.rfile.read(int(self.headers["Content-Length"]))
        FakeAPI.requests.append(self.mode)
        if self.mode in ("429", "500", "401"):
            body, code = b'{"error": "drill"}', int(self.mode)
        elif self.mode == "garbage":
            body, code = b"<html>not json", 200
        else:   # bad tool arguments on the first call, then plain text
            call = {"id": "c1", "type": "function", "function": {"name": "read_file", "arguments": "{bad json"}}
            msg = {"content": "", "tool_calls": [call]} if len(FakeAPI.requests) == 1 else {"content": "done"}
            body, code = json.dumps({"choices": [{"message": msg}], "usage": {"prompt_tokens": 10, "completion_tokens": 5}}).encode(), 200
        self.send_response(code)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, *a):
        pass


def session(cap):
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-drill-"))
    t = taskmod.load()
    return repair.Session(t, MODEL, t.start, out, budget.Budget(cap, None))


def run_dialog(mode, cap=0.5, turns=3):
    FakeAPI.mode, FakeAPI.requests = mode, []
    srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), FakeAPI)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    s = session(cap)
    outcome = None
    with patch.object(meta_client, "BASE_URL", f"http://127.0.0.1:{srv.server_address[1]}"), \
            patch.object(meta_client, "LOG", s.out / "model_calls.jsonl"), \
            patch.object(repair.Session, "pause", lambda self, seconds: None):
        try:
            outcome = repair.dialog(s, MODEL, "default", "system", "user", {"read_file"}, turns, lambda: False, "drill")[0]
        except budget.BudgetExceeded as e:
            outcome = f"budget stop: {e}"
    srv.shutdown()
    return s, outcome


def test_persistent_rate_limiting_ends_at_the_budget_cap():
    s, outcome = run_dialog("429", cap=0.3, turns=50)
    assert str(outcome).startswith("budget stop"), outcome
    assert s.budget.lost_attempts == len(FakeAPI.requests) and 0 < s.budget.usd_list <= 0.3
    assert any(e["kind"] == "api_error" and e["status"] == 429 for e in s.events)


def test_server_errors_are_retried_and_charged():
    s, outcome = run_dialog("500", cap=100.0, turns=2)
    assert outcome is False
    assert len(FakeAPI.requests) == 10                       # 5 attempts per turn, 2 turns
    assert s.budget.lost_attempts == 10 and s.budget.usd_list > 0


def test_malformed_response_body_is_a_transient_failure():
    s, outcome = run_dialog("garbage", cap=100.0, turns=1)
    assert outcome is False and len(FakeAPI.requests) == 5
    assert all(e["status"] == 0 for e in s.events if e["kind"] == "api_error")


def test_rejected_key_stops_the_dialog_without_retrying():
    s, outcome = run_dialog("401", cap=100.0, turns=5)
    assert outcome is False and len(FakeAPI.requests) == 1


def test_malformed_tool_arguments_return_an_error_to_the_model():
    s, outcome = run_dialog("badargs", cap=100.0, turns=2)
    tools = [e for e in s.events if e["kind"] == "tool"]
    assert tools and tools[0]["name"] == "read_file" and tools[0]["result"].startswith("error")
    assert s.budget.lost_attempts == 0 and s.version == 0     # nothing written


def timed_session(wall):
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-drill-"))
    t = taskmod.load()
    return repair.Session(t, MODEL, t.start, out, budget.Budget(5.0, wall))


OK_REPLY = {"choices": [{"message": {"content": "done"}}], "usage": {"prompt_tokens": 10, "completion_tokens": 5}}


def test_attempt_timeout_before_the_deadline_is_retried_not_a_wall_stop():
    s = timed_session(3600)
    replies = [meta_client.DeadlineReached("no complete response within 600.0 s"), OK_REPLY]
    def fake_chat(*a, **k):
        r = replies.pop(0)
        if isinstance(r, Exception):
            raise r
        return r
    with patch.object(repair, "chat", fake_chat):
        r, u = s.call(MODEL, [{"role": "user", "content": "x"}], "drill")
    assert r is OK_REPLY and s.budget.stop is None
    assert s.budget.lost_attempts == 1   # the timed-out attempt keeps its worst-case charge
    assert any(e["kind"] == "api_error" and "attempt timeout" in e["body"] for e in s.events)


def test_persistent_attempt_timeouts_raise_a_transient_error():
    s = timed_session(3600)
    def fake_chat(*a, **k):
        raise meta_client.DeadlineReached("no complete response within 600.0 s")
    with patch.object(repair, "chat", fake_chat):
        try:
            s.call(MODEL, [{"role": "user", "content": "x"}], "drill", attempts=2)
            raise AssertionError("expected an APIError")
        except budget.BudgetExceeded:
            raise AssertionError("a per-attempt timeout must not be a wall stop")
        except meta_client.APIError as e:
            assert e.status == 0
    assert s.budget.stop is None and s.budget.lost_attempts == 2


def test_reaching_the_run_deadline_is_the_wall_stop():
    s = timed_session(3600)
    def fake_chat(*a, **k):
        s.budget.t0 -= 3600   # the run's deadline passes while the request is open
        raise meta_client.DeadlineReached()
    with patch.object(repair, "chat", fake_chat):
        try:
            s.call(MODEL, [{"role": "user", "content": "x"}], "drill")
            raise AssertionError("expected the wall stop")
        except budget.BudgetExceeded as e:
            assert str(e) == "wall"
    assert s.budget.stop == "wall" and s.budget.lost_attempts == 1


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
