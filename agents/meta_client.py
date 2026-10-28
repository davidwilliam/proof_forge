"""Minimal Meta Model API client (OpenAI-compatible Chat Completions), stdlib only.

Reads META_API_KEY from the environment or the repository's .env file. Every call is
logged to runs/model_calls.jsonl with model, purpose, token usage and latency; the key
and message contents are never logged.
"""
import http.client, json, os, pathlib, socket, threading, time, urllib.error, urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
BASE_URL = os.environ.get("META_API_BASE", "https://api.meta.ai/v1")
LOG = ROOT / "runs" / "model_calls.jsonl"


def api_key() -> str:
    if os.environ.get("META_API_KEY"):
        return os.environ["META_API_KEY"]
    env = ROOT / ".env"
    if env.exists():
        for line in env.read_text().splitlines():
            if line.strip().startswith("META_API_KEY="):
                return line.split("=", 1)[1].strip().strip('"').strip("'")
    raise RuntimeError("META_API_KEY not set")


class APIError(Exception):
    def __init__(self, status, body):
        super().__init__(f"HTTP {status}: {body[:500]}")
        self.status, self.body = status, body


TRANSIENT = (urllib.error.URLError, socket.timeout, TimeoutError, ConnectionError,
             http.client.RemoteDisconnected, http.client.IncompleteRead)


class DeadlineReached(APIError):
    """The request did not complete before the caller's deadline; any later response is discarded."""
    def __init__(self, detail="deadline reached"):
        super().__init__(0, detail)


def _attempt(data, limit):
    """One HTTP request in a worker thread, waited for at most `limit` seconds in total.
    Returns (status, body, error); a request still running at the limit is abandoned and
    its eventual response is never used."""
    box = {}

    def work():
        req = urllib.request.Request(
            f"{BASE_URL}/chat/completions", data=data,
            headers={"Authorization": f"Bearer {api_key()}", "Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=limit) as resp:
                box["result"] = (resp.status, json.loads(resp.read()), None)
        except urllib.error.HTTPError as e:
            box["result"] = (e.code, None, APIError(e.code, e.read().decode(errors="replace")))
        except TRANSIENT as e:
            box["result"] = (0, None, APIError(0, f"network error: {type(e).__name__}: {e}"))
        except Exception as e:  # malformed body and similar: transient for the caller
            box["result"] = (0, None, APIError(0, f"error: {type(e).__name__}: {e}"))

    t = threading.Thread(target=work, daemon=True)
    t.start()
    t.join(limit)
    if t.is_alive() or "result" not in box:
        return 0, None, DeadlineReached(f"no complete response within {limit:.1f} s")
    return box["result"]


def chat(model, messages, purpose, tools=None, max_tokens=2048, timeout=180, retries=4, deadline=None, **extra):
    """One chat completion. Each attempt has an absolute time limit: min(timeout, time to
    `deadline`), covering connection, upload and the whole response body. Transient failures
    are retried with backoff (retries=0 for callers that account for each attempt); after
    the last one they raise APIError with status 0. A response that would arrive after the
    deadline is never returned."""
    payload = {"model": model, "messages": messages, "max_tokens": max_tokens, **extra}
    if tools:
        payload["tools"] = tools
    data = json.dumps(payload).encode()
    for attempt in range(retries + 1):
        t0 = time.monotonic()
        limit = timeout if deadline is None else min(timeout, deadline - t0)
        if limit < 1:
            raise DeadlineReached()
        status, body, err = _attempt(data, limit)
        _log(model, purpose, status, int((time.monotonic() - t0) * 1000), body)
        if err is None:
            if deadline is not None and time.monotonic() > deadline:
                raise DeadlineReached("response completed after the deadline")
            return body
        if isinstance(err, DeadlineReached) or err.status not in (0,) or attempt == retries:
            raise err
        pause = min(60, 5 * 2 ** attempt)
        if deadline is not None:
            pause = min(pause, max(0.0, deadline - time.monotonic()))
        time.sleep(pause)


def _log(model, purpose, status, ms, body):
    LOG.parent.mkdir(exist_ok=True)
    rec = {"ts": time.time(), "model": model, "purpose": purpose, "status": status,
           "latency_ms": ms, "returned_model": (body or {}).get("model"),
           "usage": (body or {}).get("usage")}
    with LOG.open("a") as f:
        f.write(json.dumps(rec) + "\n")
