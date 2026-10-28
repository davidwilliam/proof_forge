"""Regression tests for the E1 budget controls. No model calls.

Run: python3 tests/test_budget_controls.py
"""
import http.server, json, os, pathlib, random, sys, tempfile, threading, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "eval")]
os.environ.setdefault("META_API_KEY", "test-key-not-used")
import budget, meta_client, repair, task as taskmod  # noqa: E402
import e1  # noqa: E402

MODEL = "muse-spark-1.3-contributor"


def settle_worst(b, prompt_bytes, n_messages, reported_prompt_tokens):
    mt, _ = b.call_limits(MODEL, prompt_bytes, n_messages, 32000, 600)
    tok = b.reserve(MODEL, prompt_bytes, n_messages, mt)
    b.settle(tok, {"prompt_tokens": reported_prompt_tokens, "completion_tokens": mt})
    return mt


def test_reviewer_case_stays_within_cap():
    """30,000 characters reported as 15,000 input tokens, with the full output allowance."""
    b = budget.Budget(0.08, None)
    settle_worst(b, 30_000, 2, 15_000)
    assert b.usd_list <= 0.08, b.usd_list


def test_multibyte_prompt_bound_uses_bytes():
    """Characters undercount tokens for non-ASCII text; the bound counts UTF-8 bytes."""
    text = "∀x, α → β " * 2000
    nbytes = len(json.dumps({"messages": [{"role": "user", "content": text}]}, ensure_ascii=False).encode())
    b = budget.Budget(0.05, None)
    settle_worst(b, nbytes, 1, nbytes)          # one token per byte: the tokenizer's worst case
    assert b.usd_list <= 0.05, b.usd_list


def test_worst_case_input_never_exceeds_cap():
    rng = random.Random(0)
    for _ in range(500):
        cap = rng.uniform(0.02, 3.0)
        b = budget.Budget(cap, None)
        try:
            while True:
                nbytes, n = rng.randint(100, 200_000), rng.randint(1, 40)
                settle_worst(b, nbytes, n, b.input_bound(nbytes, n))   # reported usage equal to the bound
        except budget.BudgetExceeded:
            pass
        assert b.usd_list <= cap + 1e-9, (cap, b.usd_list)


def test_lost_responses_stay_charged_and_capped():
    b = budget.Budget(0.30, None)
    lost = 0
    try:
        while True:
            mt, _ = b.call_limits(MODEL, 20_000, 3, 32000, 600)
            tok = b.reserve(MODEL, 20_000, 3, mt)
            b.lost(tok)
            lost += 1
    except budget.BudgetExceeded:
        pass
    assert lost >= 1 and b.lost_attempts == lost
    assert 0 < b.usd_list <= 0.30, b.usd_list


class Drip(http.server.BaseHTTPRequestHandler):
    """Sends a valid response body one byte every 0.2 s."""
    def do_POST(self):
        self.rfile.read(int(self.headers["Content-Length"]))
        body = json.dumps({"choices": [{"message": {"content": "x"}}], "usage": {"prompt_tokens": 1}}).encode()
        self.send_response(200)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        for i in range(len(body)):
            try:
                self.wfile.write(body[i:i + 1])
                self.wfile.flush()
            except BrokenPipeError:
                return
            time.sleep(0.2)

    def log_message(self, *a):
        pass


def test_slow_response_cannot_pass_the_deadline():
    srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Drip)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    old = meta_client.BASE_URL
    meta_client.BASE_URL = f"http://127.0.0.1:{srv.server_address[1]}"
    try:
        t0 = time.monotonic()
        try:
            meta_client.chat(MODEL, [{"role": "user", "content": "hi"}], "test", retries=0, deadline=t0 + 1.1)
            raise AssertionError("a response arrived after the deadline")
        except meta_client.DeadlineReached:
            pass
        assert time.monotonic() - t0 < 1.6, time.monotonic() - t0
    finally:
        meta_client.BASE_URL = old
        srv.shutdown()


def test_no_writes_or_tools_after_the_deadline():
    t = taskmod.load()
    out = pathlib.Path(tempfile.mkdtemp())
    s = repair.Session(t, MODEL, t.start, out, budget.Budget(None, 0.5))
    before = s._source()
    time.sleep(0.6)
    try:
        s.write_solution(before + "\n-- late edit\n")
        raise AssertionError("a write was accepted after the deadline")
    except budget.BudgetExceeded:
        pass
    assert s._source() == before
    try:
        s.call(MODEL, [{"role": "user", "content": "hi"}], "test")
        raise AssertionError("a model call was made after the deadline")
    except budget.BudgetExceeded:
        pass
    repair.judge.DEADLINE = None


def test_resume_ledger_counts_summary_only_runs():
    """Reviewer's reproduction: a summary with $2.90 spent, no eval.json, batch cap $3."""
    out = pathlib.Path(tempfile.mkdtemp())
    t = taskmod.load()
    d = out / t.id / "A0"
    d.mkdir(parents=True)
    (d / "summary.json").write_text(json.dumps({"budget": {"usd_list": 2.90}}))
    cap = e1.BatchCap(3.0, 3.0)
    cap.rebuild(out, [t], ["A0", "A1"])
    assert abs(cap.spent - 2.90) < 1e-9, cap.spent
    assert not cap.admit(1)


def test_resume_ledger_counts_interrupted_runs_at_the_cap():
    out = pathlib.Path(tempfile.mkdtemp())
    t = taskmod.load()
    d = out / t.id / "A1"
    d.mkdir(parents=True)
    (d / "events.jsonl").write_text("{}\n")      # started, no summary
    cap = e1.BatchCap(10.0, 3.0)
    cap.rebuild(out, [t], ["A0", "A1"])
    assert cap.spent == 3.0
    e1.set_aside_interrupted(d)
    assert not d.exists() and (out / t.id / "A1.interrupted-1").exists()


def test_task_admission_reserves_all_remaining_arms():
    cap = e1.BatchCap(8.0, 3.0)
    assert cap.admit(2)          # 6 reserved
    assert not cap.admit(1)      # 6 + 3 > 8
    cap.done(1.0)                # one run finished at $1
    assert not cap.admit(2)      # 1 spent + 3 reserved + 6 > 8
    assert cap.admit(1)          # 1 + 3 + 3 <= 8


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
