#!/usr/bin/env python3
"""Smoke-test every Meta model ID used by ProofForge: plain completion and tool calling."""
import json, sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from meta_client import chat, APIError

MODELS = ["muse-spark-1.3", "muse-spark-1.3-contributor", "muse-wonder-1.0",
          "muse-spark-1.2", "muse-spark-1.2-contributor", "muse-spark-1.1"]
TOOL = [{"type": "function", "function": {
    "name": "check_candidate", "description": "Run the Lean checker on a candidate file.",
    "parameters": {"type": "object", "properties": {"path": {"type": "string"}}, "required": ["path"]}}}]

for m in MODELS:
    row = {"model": m}
    try:
        r = chat(m, [{"role": "user", "content": "Reply with exactly: 100 = 34 + 33 + 33"}], "smoke:plain", max_tokens=64)
        row["plain"] = (r["choices"][0]["message"].get("content") or "").strip()[:60]
        row["usage"] = r.get("usage")
        r = chat(m, [{"role": "user", "content": "Check the candidate at candidate/Solution.lean using the tool."}],
                 "smoke:tools", tools=TOOL, max_tokens=256)
        calls = r["choices"][0]["message"].get("tool_calls") or []
        row["tool_call"] = [(c["function"]["name"], c["function"]["arguments"]) for c in calls]
    except APIError as e:
        row["error"] = f"HTTP {e.status}: {e.body[:200]}"
    except Exception as e:  # network or schema problems
        row["error"] = repr(e)[:200]
    print(json.dumps(row))
