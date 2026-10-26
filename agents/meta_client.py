"""Minimal Meta Model API client (OpenAI-compatible Chat Completions), stdlib only.

Reads META_API_KEY from the environment or the repository's .env file. Every call is
logged to runs/model_calls.jsonl with model, purpose, token usage and latency; the key
and message contents are never logged.
"""
import json, os, pathlib, time, urllib.error, urllib.request

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


def chat(model, messages, purpose, tools=None, max_tokens=2048, timeout=180, **extra):
    payload = {"model": model, "messages": messages, "max_tokens": max_tokens, **extra}
    if tools:
        payload["tools"] = tools
    req = urllib.request.Request(
        f"{BASE_URL}/chat/completions", data=json.dumps(payload).encode(),
        headers={"Authorization": f"Bearer {api_key()}", "Content-Type": "application/json"})
    t0 = time.monotonic()
    status, body = None, None
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            status, body = resp.status, json.loads(resp.read())
    except urllib.error.HTTPError as e:
        status, text = e.code, e.read().decode(errors="replace")
        _log(model, purpose, status, int((time.monotonic() - t0) * 1000), None)
        raise APIError(status, text) from None
    _log(model, purpose, status, int((time.monotonic() - t0) * 1000), body)
    return body


def _log(model, purpose, status, ms, body):
    LOG.parent.mkdir(exist_ok=True)
    rec = {"ts": time.time(), "model": model, "purpose": purpose, "status": status,
           "latency_ms": ms, "returned_model": (body or {}).get("model"),
           "usage": (body or {}).get("usage")}
    with LOG.open("a") as f:
        f.write(json.dumps(rec) + "\n")
