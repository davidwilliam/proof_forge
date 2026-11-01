"""The metering proxy for Muse Code (integrations/muse/meter.py) against a local stand-in for the
Meta Model API. No model calls.

The input bound: a request that extends an earlier settled request (same context, its items as a
prefix) is bounded by that request's reported prompt_tokens plus the bytes of the new items and
the overheads; a compacted or rewritten history, other instructions, or a request with no settled
predecessor gets the byte bound; the smaller bound is used. The recorded call logs of
results/muse-code-1 replayed through the meter (integrations/muse/meter_replay.py) never exceed the
cap or the bound under either rule.

Run: python3 tests/test_muse_meter.py
"""
import http.client, http.server, json, pathlib, socketserver, sys, tempfile, threading

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "integrations" / "muse"), str(ROOT / "agents")]
import meter  # noqa: E402
import meter_replay  # noqa: E402
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


# The input bound

ITEM = lambda i, n=200: {"type": "message", "role": "user", "content": f"m{i} " + "x" * n}
CTX = {"model": MODEL, "instructions": "You are Muse Code, an agentic coding CLI", "tools": [{"type": "function", "name": "t"}],
       "reasoning": {"effort": "medium"}, "stream": True}


def body(items, **kw):
    return {**CTX, **kw, "input": items, "max_output_tokens": 128000}


def admit(m, b):
    info = {}
    raw = json.dumps(b).encode()
    tok, granted = m.admit(b, len(raw), info)
    return tok, info, len(raw)


def settle(m, tok, prompt_tokens):
    m.settle(tok, {"prompt_tokens": prompt_tokens, "prompt_tokens_details": {"cached_tokens": 0}, "completion_tokens": 10},
             {"role": "main"})


def test_prefix_extension_is_bounded_by_the_reported_prompt_plus_the_new_bytes():
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10)
    first = [ITEM(0, 5000), ITEM(1, 5000)]
    tok, info, nbytes = admit(m, body(first))
    assert info["bound"] == "bytes" and info["input_bound"] == m.budget.input_bound(nbytes, 3)
    settle(m, tok, 1500)
    new = [ITEM(2), ITEM(3)]
    tok, info, nbytes = admit(m, body(first + new))
    want = 1500 + sum(len(json.dumps(x)) for x in new) + budget.PER_MESSAGE_TOKENS * 3 + budget.FIXED_TOKENS
    assert info == {"input_bound": want, "bound": "prefix", "prefix_items": 2}, info
    assert want < m.budget.input_bound(nbytes, 5)
    assert tok["worst"]["prompt_tokens"] == want                         # the reservation uses it
    settle(m, tok, 1700)
    # The longest settled prefix is the one used.
    tok, info, _ = admit(m, body(first + new + [ITEM(4)]))
    assert info["prefix_items"] == 4 and info["input_bound"] == 1700 + len(json.dumps(ITEM(4))) + 64 * 2 + 2048, info
    settle(m, tok, 1800)
    # The same request again (a retry) is bounded by its own earlier usage plus the overheads.
    tok, info, _ = admit(m, body(first + new + [ITEM(4)]))
    assert info["bound"] == "prefix" and info["input_bound"] == 1800 + 64 + 2048, info
    assert m.summary()["input_bounds"] == {"prefix": 3, "bytes": 1}


def test_compaction_or_a_changed_prefix_falls_back_to_the_byte_bound():
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10)
    first = [ITEM(0, 5000), ITEM(1, 5000)]
    tok, _, _ = admit(m, body(first))
    settle(m, tok, 1500)
    cases = {
        "compacted history": body([{"type": "message", "role": "user", "content": "summary of the session"}, ITEM(2)]),
        "an earlier item changed": body([ITEM(0, 5000), ITEM(9, 5000), ITEM(2)]),
        "items dropped from the start": body([ITEM(1, 5000), ITEM(2)]),
        "other instructions": body(first + [ITEM(2)], instructions="You are a summarizer"),
        "other tools": body(first + [ITEM(2)], tools=[]),
        "other reasoning effort": body(first + [ITEM(2)], reasoning={"effort": "low"}),
        "input as a string": {**CTX, "input": "hi", "max_output_tokens": 2000},
    }
    for why, b in cases.items():
        _, info, nbytes = admit(m, b)
        assert info["bound"] == "bytes", (why, info)
        assert info["input_bound"] == m.budget.input_bound(nbytes, len(b["input"]) + 1), why   # as admit counts items
    # A call that never settled is no prefix: its usage is unknown.
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10)
    tok, _, _ = admit(m, body(first))
    m.settle(tok, None, {"role": "main"})
    assert admit(m, body(first + [ITEM(2)]))[1]["bound"] == "bytes"
    # The byte bound wins when it is smaller (a predecessor that reported more tokens than bytes).
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10)
    tok, _, _ = admit(m, body([ITEM(0, 10)]))
    settle(m, tok, 10 ** 6)
    _, info, nbytes = admit(m, body([ITEM(0, 10), ITEM(1, 10)]))
    assert info["bound"] == "bytes" and info["input_bound"] == m.budget.input_bound(nbytes, 3)
    # With the prefix bound off (the rule of results/muse-code-1) every request gets the byte bound.
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10, prefix=False)
    tok, _, _ = admit(m, body(first))
    settle(m, tok, 1500)
    assert admit(m, body(first + [ITEM(2)]))[1]["bound"] == "bytes"


def test_proxy_records_the_bound_of_each_call():
    up = Upstream(usage={**USAGE, "input_tokens": 500, "input_tokens_details": {"cached_tokens": 0}})
    m = meter.Meter(tempfile.mkdtemp(), usd_cap=10, wall_cap=600, upstream=up.url)
    port = m.start()
    first = [ITEM(0, 3000)]
    assert post(port, body(first))[0] == 200
    assert post(port, body(first + [ITEM(1)]))[0] == 200
    rec = calls(m)
    assert [r["bound"] for r in rec] == ["bytes", "prefix"] and rec[1]["prefix_items"] == 1, rec
    assert rec[1]["input_bound"] == 500 + len(json.dumps(ITEM(1))) + 64 * 2 + 2048
    assert up.seen[1]["body"]["input"] == first + [ITEM(1)]               # forwarded unchanged
    assert m.summary()["input_bounds"] == {"prefix": 1, "bytes": 1}
    m.stop()


def test_recorded_runs_replayed_through_the_meter_stay_within_the_cap_and_the_bound():
    """Every measured run of results/muse-code-1, replayed under the byte bound and the prefix
    bound: no reservation above the $10 cap, no reported input above the bound used, every recorded
    call admitted under the prefix bound; the byte bound reproduces the recorded dollar stops, and
    the prefix bound leaves the runs it stopped more of the cap."""
    runs = sorted(p.parent for p in (ROOT / "results/muse-code-1").glob("*/*-[0-9]/calls.jsonl"))
    assert len(runs) == 14, runs
    for d in runs:
        cl = [json.loads(l) for l in (d / "calls.jsonl").read_text().splitlines() if l.strip()]
        s = json.loads((d / "summary.json").read_text())
        old, new = meter_replay.replay(cl, 10.0, prefix=False), meter_replay.replay(cl, 10.0, prefix=True)
        for r in (old, new):
            assert not r["over_cap"] and r["max_reserved_usd"] <= 10 and r["input_bound_violations"] == 0, (d, r)
        assert new["refused_at"] is None and new["bounds"]["prefix"] > 0, (d, new)
        assert new["final_request"]["input_bound"] <= old["final_request"]["input_bound"]
        if s["ended_by"] == "usd":
            # the old rule stops where the run stopped (within the last calls' settlement)
            assert abs(old["final_request"]["usable_usd"] - s["meter"]["usd_list"]) < 0.1, (d, old, s["meter"]["usd_list"])
            assert new["final_request"]["usable_usd"] >= 9.4, (d, new)


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
