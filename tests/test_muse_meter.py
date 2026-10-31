"""The metering proxy for Muse Code (integrations/muse/meter.py) against a local stand-in for the
Meta Model API. No model calls.

Run: python3 tests/test_muse_meter.py
"""
import http.client, http.server, json, pathlib, socketserver, sys, tempfile, threading

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "integrations" / "muse"), str(ROOT / "agents")]
import meter  # noqa: E402
import budget  # noqa: E402

MODEL = "muse-spark-1.3-contributor"
USAGE = {"input_tokens": 20000, "input_tokens_details": {"cached_tokens": 5000}, "output_tokens": 300,
         "output_tokens_details": {"reasoning_tokens": 100}, "total_tokens": 20300}


class Upstream:
    """Answers POST /v1/responses with an SSE stream; records what it received."""

    def __init__(self, usage=USAGE, sse=True):
        self.seen = []
        up = self

        class H(http.server.BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.0"

            def log_message(self, *a):
                pass

            def do_POST(self):
                body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
                up.seen.append({"path": self.path, "body": body, "auth": self.headers.get("Authorization")})
                if sse:
                    events = [{"type": "response.created", "response": {"id": "r1"}},
                              {"type": "response.output_text.delta", "delta": "ok"},
                              {"type": "response.completed", "response": {"id": "r1", **({"usage": usage} if usage else {})}}]
                    data = "".join(f"event: {e['type']}\ndata: {json.dumps(e)}\n\n" for e in events) + "data: [DONE]\n\n"
                    self.send_response(200)
                    self.send_header("Content-Type", "text/event-stream")
                    self.end_headers()
                    self.wfile.write(data.encode())
                else:
                    data = json.dumps({"id": "r1", "usage": usage}).encode()
                    self.send_response(200)
                    self.send_header("Content-Type", "application/json")
                    self.send_header("Content-Length", str(len(data)))
                    self.end_headers()
                    self.wfile.write(data)

        class S(socketserver.ThreadingMixIn, http.server.HTTPServer):
            daemon_threads = True
        self.server = S(("127.0.0.1", 0), H)
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        self.url = f"http://127.0.0.1:{self.server.server_address[1]}/v1"


def post(port, body, key="sk-test-secret"):
    c = http.client.HTTPConnection("127.0.0.1", port, timeout=30)
    raw = json.dumps(body).encode()
    c.request("POST", "/v1/responses", body=raw, headers={"Authorization": f"Bearer {key}",
                                                         "Content-Type": "application/json"})
    r = c.getresponse()
    return r.status, r.read().decode()


def request(max_out=128000, instructions="You are Muse Code, an agentic coding CLI"):
    return {"model": MODEL, "instructions": instructions, "input": [{"role": "user", "content": "hi"}],
            "max_output_tokens": max_out, "stream": True}


def calls(m):
    return [json.loads(l) for l in (m.out / "calls.jsonl").read_text().splitlines()]


def test_settles_reported_usage_at_list_price():
    up = Upstream()
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10, wall_cap=600, upstream=up.url)
    port = m.start()
    status, text = post(port, request())
    assert status == 200 and "response.completed" in text, (status, text[:200])
    s = m.summary()
    usage = {"prompt_tokens": 20000, "prompt_tokens_details": {"cached_tokens": 5000}, "completion_tokens": 300}
    assert abs(s["usd_list"] - round(budget.list_cost(MODEL, usage), 4)) < 1e-4, s
    assert abs(s["usd_actual"] - round(budget.actual_cost(MODEL, usage), 4)) < 1e-4, s
    assert s["calls"] == 1 and s["unknown_usage_calls"] == 0 and s["lost_attempts"] == 0
    assert up.seen[0]["path"] == "/v1/responses" and up.seen[0]["auth"] == "Bearer sk-test-secret"
    m.stop()


def test_key_and_contents_are_not_logged():
    up = Upstream()
    out = tempfile.mkdtemp()
    m = meter.Meter(out, usd_cap=10, wall_cap=600, upstream=up.url)
    port = m.start()
    post(port, request())
    log = (pathlib.Path(out) / "calls.jsonl").read_text()
    assert "sk-test-secret" not in log and "Bearer" not in log
    assert '"hi"' not in log   # message contents
    m.stop()


def test_roles_separate_main_and_helper_agents():
    up = Upstream()
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10, wall_cap=600, upstream=up.url)
    port = m.start()
    post(port, request())
    post(port, request(instructions="You are a goal reminder: you are NOT the agent"))
    s = m.summary()
    assert s["by_role"]["main"]["calls"] == 1 and s["by_role"]["helper"]["calls"] == 1, s["by_role"]
    m.stop()


def test_output_allowance_is_lowered_to_fit_the_cap():
    up = Upstream()
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=0.10, wall_cap=600, upstream=up.url)
    port = m.start()
    post(port, request(max_out=128000))
    granted = up.seen[0]["body"]["max_output_tokens"]
    _, _, o = budget.STANDARD["muse-spark-1.3"]
    assert granted < 128000 and granted * o / 1e6 <= 0.10, granted
    assert calls(m)[0]["max_output_tokens_granted"] == granted
    m.stop()


def test_output_allowance_is_at_most_32000():
    up = Upstream()
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10, wall_cap=600, upstream=up.url)
    port = m.start()
    post(port, request(max_out=128000))
    post(port, request(max_out=4000))
    assert [x["body"]["max_output_tokens"] for x in up.seen] == [32000, 4000]
    assert m.in_flight() == 0
    m.stop()


def test_refuses_when_the_cap_cannot_fit_and_sets_stop():
    up = Upstream()
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=0.001, wall_cap=600, upstream=up.url)
    port = m.start()
    status, text = post(port, request())
    assert status == 400 and "budget_exhausted" in text, (status, text)
    assert m.stopped == "usd" and not up.seen
    status, _ = post(port, request())
    assert status == 400
    m.stop()


def test_call_waits_for_calls_in_flight_before_refusing():
    """Near the cap, a call that fits only after another call settles waits instead of stopping the run."""
    import time as _time
    up = Upstream()
    usd = budget.list_cost(MODEL, {"prompt_tokens": 2600, "completion_tokens": 20000}) * 1.03
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=usd, wall_cap=600, upstream=up.url)
    first = m.admit(request(max_out=20000), 200)         # an open reservation holding most of the cap
    out = {}
    t = threading.Thread(target=lambda: out.update(r=m.admit(request(max_out=20000), 200)))
    t.start()
    _time.sleep(1.0)
    assert t.is_alive() and not m.stopped               # waiting, not refused
    m.settle(first[0], {"prompt_tokens": 100, "completion_tokens": 10}, {"role": "main"})
    t.join(5)
    assert "r" in out and not m.stopped, (out, m.stopped)
    m.stop()


def test_response_without_usage_stays_at_worst_case():
    up = Upstream(usage=None)
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10, wall_cap=600, upstream=up.url)
    port = m.start()
    post(port, request(max_out=4000))
    s = m.summary()
    worst = budget.list_cost(MODEL, {"prompt_tokens": calls(m)[0]["bytes"] + 64 * 2 + 2048, "completion_tokens": 4000})
    assert s["lost_attempts"] == 1 and abs(s["usd_list"] - round(worst, 4)) < 1e-4, (s, worst)
    m.stop()


def test_json_response_usage_is_read():
    up = Upstream(sse=False)
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10, wall_cap=600, upstream=up.url)
    port = m.start()
    post(port, {**request(), "stream": False})
    assert m.summary()["unknown_usage_calls"] == 0 and m.summary()["lost_attempts"] == 0
    m.stop()


def test_unpriced_model_is_refused():
    up = Upstream()
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10, wall_cap=600, upstream=up.url)
    port = m.start()
    status, text = post(port, {**request(), "model": "some-other-model"})
    assert status == 400 and "unpriced_model" in text and not up.seen
    m.stop()


def test_wall_cap_refuses():
    up = Upstream()
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10, wall_cap=0.0, upstream=up.url)
    port = m.start()
    status, _ = post(port, request())
    assert status == 400 and m.stopped == "wall"
    m.stop()


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
