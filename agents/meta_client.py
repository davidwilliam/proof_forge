"""Minimal Meta Model API client (OpenAI-compatible Chat Completions), stdlib only.

Reads META_API_KEY from the environment or the repository's .env file. Every call is
logged to runs/model_calls.jsonl with model, purpose, token usage and latency; the key
and message contents are never logged.
"""
import http.client, json, os, pathlib, socket, time, urllib.error, urllib.request

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


def chat(model, messages, purpose, tools=None, max_tokens=2048, timeout=180, retries=4, deadline=None, **extra):
    """One chat completion. Network failures are retried with backoff; after the last
    retry they raise APIError with status 0, which callers treat as transient. With a
    monotonic `deadline`, no attempt or backoff extends past it."""
    payload = {"model": model, "messages": messages, "max_tokens": max_tokens, **extra}
    if tools:
        payload["tools"] = tools
    data = json.dumps(payload).encode()
    for attempt in range(retries + 1):
        req = urllib.request.Request(
            f"{BASE_URL}/chat/completions", data=data,
            headers={"Authorization": f"Bearer {api_key()}", "Content-Type": "application/json"})
        t0 = time.monotonic()
        limit = timeout if deadline is None else min(timeout, deadline - t0)
        if limit < 1:
            raise APIError(0, "deadline reached")
        try:
            with urllib.request.urlopen(req, timeout=limit) as resp:
                body = json.loads(resp.read())
            _log(model, purpose, resp.status, int((time.monotonic() - t0) * 1000), body)
            return body
        except urllib.error.HTTPError as e:
            text = e.read().decode(errors="replace")
            _log(model, purpose, e.code, int((time.monotonic() - t0) * 1000), None)
            raise APIError(e.code, text) from None
        except TRANSIENT as e:
            _log(model, purpose, 0, int((time.monotonic() - t0) * 1000), None)
            if attempt == retries:
                raise APIError(0, f"network error: {type(e).__name__}: {e}") from None
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
