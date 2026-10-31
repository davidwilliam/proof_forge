"""Metering proxy for Muse Code: every model call of a run, priced and capped with agents/budget.py.

Muse Code reports token usage once, at the end of a run (`run.usage`), and that record leaves out
the calls its reminder agents make (`children_included: false`). To price a run honestly and
stop it at a dollar cap, the runner (agents/muse_code.py) points Muse Code at this proxy with
`--base-url http://127.0.0.1:<port>/v1`. The proxy forwards each request to the Meta Model API
unchanged except for one field, streams the response back, and reads the usage of every call from
its `response.completed` event.

Budget rule (the same as agents/budget.py for the A0, A1 and A2 arms):
  - `max_output_tokens` is at most 32,000 per call (Muse Code asks for 128,000), the allowance
    the A0, A1 and A2 agents get;
  - before a request is forwarded, its worst case (every byte of the request body counted as an
    uncached input token at list price, plus `max_output_tokens` of output) is reserved;
    `max_output_tokens` is lowered so that the worst case fits the dollars left; a request whose
    worst case does not fit with at least 1,024 output tokens waits while other calls are in flight
    (their settlement frees their reservations) and is refused when none is;
  - a call is settled to its reported usage when its `response.completed` event arrives; a call
    whose response ends without usage, fails or is cut off stays charged at its worst case;
  - every model id is priced at the standard-tier list price (Contributor-tier calls included),
    and the amount charged at the tier actually used is tracked separately.
When a request is refused, `stopped` is set; the runner lets the calls already in flight settle
and then ends the Muse Code process.

The proxy never logs request headers (the API key travels in `Authorization`) or message
contents. `calls.jsonl` records, per call: time, model, request size, requested and granted
output tokens, HTTP status, latency, usage, list and charged cost, and the role of the caller
(the main agent or one of Muse Code's helper agents, from the opening of its instructions).
"""
import http.client, http.server, json, pathlib, socketserver, ssl, sys, threading, time, urllib.parse

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "agents"))
from budget import Budget, BudgetExceeded, list_cost, actual_cost  # noqa: E402

UPSTREAM = "https://api.meta.ai/v1"
MIN_OUTPUT = 1024
MAX_OUTPUT = 32000   # per call, as for the A0, A1 and A2 agents (agents/repair.py Session.call)
FORWARD_HEADERS = {"authorization", "content-type", "accept", "user-agent", "openai-beta", "idempotency-key"}
HOP = {"connection", "keep-alive", "transfer-encoding", "content-length", "content-encoding", "proxy-connection"}


def responses_usage(u):
    """Responses API usage as the chat-completions shape agents/budget.py prices."""
    if not u:
        return None
    return {"prompt_tokens": u.get("input_tokens", 0),
            "prompt_tokens_details": {"cached_tokens": (u.get("input_tokens_details") or {}).get("cached_tokens", 0)},
            "completion_tokens": u.get("output_tokens", 0),
            "reasoning_tokens": (u.get("output_tokens_details") or {}).get("reasoning_tokens", 0)}


def caller_role(body):
    """The main agent or a helper agent, from the opening of the request's instructions."""
    text = body.get("instructions") or ""
    if not isinstance(text, str):
        text = json.dumps(text)
    head = text[:120].replace("\n", " ")
    if head.startswith("You are Muse Code"):
        return "main", head[:80]
    return "helper", head[:80]


class Meter:
    """Proxy state: the budget, the call log and the stop flag. Thread-safe."""

    def __init__(self, out_dir, usd_cap=None, wall_cap=None, upstream=UPSTREAM, model_override=None,
                 max_output=MAX_OUTPUT):
        self.out = pathlib.Path(out_dir)
        self.out.mkdir(parents=True, exist_ok=True)
        self.budget = Budget(usd_cap, wall_cap)
        self.upstream = urllib.parse.urlsplit(upstream.rstrip("/"))
        self.model_override = model_override
        self.max_output = max_output
        self.lock = threading.Lock()
        self.stopped = None
        self.calls = 0
        self.by_role = {}
        self.server = None

    # -- accounting ------------------------------------------------------------------------
    def admit(self, body, nbytes):
        """Reserve the worst case and return (token, granted max_output_tokens); raises
        BudgetExceeded when the request cannot fit."""
        model = body.get("model") or ""
        n_items = len(body.get("input") or []) + 1
        want = min(int(body.get("max_output_tokens") or self.max_output), self.max_output)
        while True:
            with self.lock:
                if self.stopped:
                    raise BudgetExceeded(self.stopped)
                try:
                    mt, _ = self.budget.call_limits(model, nbytes, n_items, want, 3600, min_tokens=MIN_OUTPUT)
                except BudgetExceeded as e:
                    # A call that does not fit beside the worst cases of calls still in flight waits
                    # for them to settle; the run stops only when it does not fit with none open.
                    if str(e) == "usd" and self.budget.reserved_open > 0:
                        self.budget.stop = None
                    else:
                        self.stopped = str(e)
                        raise
                else:
                    tok = self.budget.reserve(model, nbytes, n_items, mt)
                    return tok, mt
            time.sleep(0.5)

    def settle(self, tok, usage, rec):
        with self.lock:
            if usage:
                self.budget.settle(tok, usage)
            else:
                self.budget.lost(tok)
            self.calls += 1
            role = self.by_role.setdefault(rec["role"], {"calls": 0, "input": 0, "cached": 0, "output": 0,
                                                         "usd_list": 0.0, "usd_actual": 0.0})
            u = usage or tok["worst"]
            role["calls"] += 1
            role["input"] += u.get("prompt_tokens", 0)
            role["cached"] += (u.get("prompt_tokens_details") or {}).get("cached_tokens", 0)
            role["output"] += u.get("completion_tokens", 0)
            lc, ac = list_cost(tok["model"], u), actual_cost(tok["model"], u)
            role["usd_list"] += lc
            role["usd_actual"] += ac
            rec.update(usd_list=round(lc, 6), usd_actual=round(ac, 6), usage=usage, settled=bool(usage),
                       run_usd_list=round(self.budget.usd_list, 4))
            with (self.out / "calls.jsonl").open("a") as f:
                f.write(json.dumps(rec) + "\n")

    def in_flight(self):
        with self.lock:
            return self.budget.reserved_open

    def summary(self):
        with self.lock:
            s = self.budget.summary()
            s["stop"] = self.stopped or s.get("stop")
            s["calls"] = self.calls
            s["by_role"] = {k: {**v, "usd_list": round(v["usd_list"], 4), "usd_actual": round(v["usd_actual"], 4)}
                            for k, v in self.by_role.items()}
            return s

    # -- server ----------------------------------------------------------------------------
    def start(self, port=0):
        meter = self

        class Handler(ProxyHandler):
            pass
        Handler.meter = meter
        self.server = ThreadingServer(("127.0.0.1", port), Handler)
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        return self.server.server_address[1]

    def stop(self):
        if self.server:
            self.server.shutdown()
            self.server.server_close()


class ThreadingServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


class ProxyHandler(http.server.BaseHTTPRequestHandler):
    meter: Meter = None
    protocol_version = "HTTP/1.0"   # the response ends when the connection closes

    def log_message(self, *a):      # no access log: nothing about requests reaches stderr
        pass

    def _error(self, status, kind, message):
        data = json.dumps({"error": {"type": kind, "code": kind, "message": message}}).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        self._forward(None)

    def do_POST(self):
        n = int(self.headers.get("Content-Length") or 0)
        self._forward(self.rfile.read(n))

    def _forward(self, raw):
        m = self.meter
        up = m.upstream
        path = self.path
        if path.startswith("/v1"):
            path = path[3:]
        # The Muse Code catalog (`/muse-code/models`) is served at the API origin, not under /v1;
        # with a custom base URL Muse Code asks for it under the base.
        target = path if path.startswith("/muse-code/") else up.path + path
        body, tok, rec = None, None, None
        if raw is not None:
            try:
                body = json.loads(raw)
            except ValueError:
                body = None
        if isinstance(body, dict) and "model" in body:
            if m.model_override:
                body["model"] = m.model_override
            role, head = caller_role(body)
            rec = {"t": round(time.time(), 3), "path": path, "model": body.get("model"), "role": role,
                   "instructions_head": head, "bytes": len(raw), "items": len(body.get("input") or []),
                   "max_output_tokens_requested": body.get("max_output_tokens"),
                   "effort": (body.get("reasoning") or {}).get("effort")}
            try:
                tok, granted = m.admit(body, len(raw))
            except BudgetExceeded as e:
                rec.update(refused=str(e))
                with (m.out / "calls.jsonl").open("a") as f:
                    f.write(json.dumps(rec) + "\n")
                return self._error(400, "budget_exhausted",
                                   f"ProofForge run budget exhausted ({e}); no further model calls are made.")
            except KeyError:
                rec.update(refused="unpriced model")
                with (m.out / "calls.jsonl").open("a") as f:
                    f.write(json.dumps(rec) + "\n")
                return self._error(400, "unpriced_model", f"model {body.get('model')!r} has no list price")
            body["max_output_tokens"] = granted
            rec["max_output_tokens_granted"] = granted
            raw = json.dumps(body).encode()
        headers = {k: v for k, v in self.headers.items() if k.lower() in FORWARD_HEADERS or k.lower().startswith("x-")}
        headers["Accept-Encoding"] = "identity"
        if raw is not None:
            headers["Content-Length"] = str(len(raw))
        t0 = time.monotonic()
        usage, status = None, 0
        try:
            if up.scheme == "https":
                conn = http.client.HTTPSConnection(up.hostname, up.port or 443, timeout=900,
                                                   context=ssl.create_default_context())
            else:   # a local stand-in for the API (tests)
                conn = http.client.HTTPConnection(up.hostname, up.port or 80, timeout=900)
            conn.request(self.command, target, body=raw, headers=headers)
            resp = conn.getresponse()
            status = resp.status
            self.send_response(resp.status)
            for k, v in resp.getheaders():
                if k.lower() not in HOP:
                    self.send_header(k, v)
            self.end_headers()
            sse = "text/event-stream" in (resp.getheader("Content-Type") or "")
            buf = b""
            while True:
                chunk = resp.read1(65536) if sse else resp.read(65536)
                if not chunk:
                    break
                self.wfile.write(chunk)
                self.wfile.flush()
                if tok is None:
                    continue
                buf += chunk
                if sse:
                    while b"\n" in buf:
                        line, buf = buf.split(b"\n", 1)
                        if line.startswith(b"data:") and b"\"usage\"" in line:
                            try:
                                ev = json.loads(line[5:].strip())
                            except ValueError:
                                continue
                            r = ev.get("response") if isinstance(ev, dict) else None
                            if isinstance(r, dict) and r.get("usage") and ev.get("type", "").endswith((".completed", ".incomplete")):
                                usage = responses_usage(r["usage"])
            if tok is not None and not sse and buf:
                try:
                    usage = responses_usage((json.loads(buf) or {}).get("usage"))
                except ValueError:
                    pass
            conn.close()
        except Exception as e:  # upstream failure or client gone: the worst case stays charged
            if rec is not None:
                rec["error"] = f"{type(e).__name__}: {e}"[:300]
            if status == 0:
                try:
                    self._error(502, "upstream_error", "the Meta Model API could not be reached")
                except Exception:
                    pass
        finally:
            if tok is None:
                with (m.out / "requests.jsonl").open("a") as f:
                    f.write(json.dumps({"t": round(time.time(), 3), "method": self.command, "path": path,
                                        "status": status, "ms": int((time.monotonic() - t0) * 1000)}) + "\n")
            if tok is not None:
                rec.update(status=status, ms=int((time.monotonic() - t0) * 1000))
                m.settle(tok, usage, rec)
