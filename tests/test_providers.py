"""Provider routing: open-weight IDs go to Baseten, Glimmer IDs to the self-hosted Modal
endpoint, each with its own key; no network calls.

Run: python3 tests/test_providers.py
"""
import os, pathlib, sys
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "agents"))
import budget, meta_client  # noqa: E402

OPEN = "meta-models/muse-spark-open-1026"
GLIMMER = "glimmer/muse-glimmer-30b"


def test_open_weight_ids_use_baseten_and_its_key():
    with patch.dict(os.environ, {"META_API_KEY": "m", "BASETEN_API_KEY": "b"}):
        assert meta_client.endpoint(OPEN) == (meta_client.BASETEN_URL, "b")
        assert meta_client.endpoint("muse-spark-1.3") == (meta_client.BASE_URL, "m")


def test_missing_baseten_key_fails_before_any_request():
    env = {k: v for k, v in os.environ.items() if k != "BASETEN_API_KEY"}
    with patch.dict(os.environ, env, clear=True), patch.object(meta_client, "ROOT", pathlib.Path("/nonexistent")), \
            patch.object(meta_client.urllib.request, "urlopen") as urlopen:
        try:
            meta_client.chat(OPEN, [{"role": "user", "content": "x"}], "test")
            raise AssertionError("expected a missing-key error")
        except RuntimeError as e:
            assert "BASETEN_API_KEY" in str(e)
        assert urlopen.call_count == 0


def test_open_weight_model_has_list_prices():
    usage = {"prompt_tokens": 1_000_000, "completion_tokens": 1_000_000}
    assert budget.list_cost(OPEN, usage) == budget.actual_cost(OPEN, usage) == 1.25 + 4.25


def test_glimmer_ids_use_the_modal_endpoint_and_its_key():
    env = {"META_API_KEY": "m", "BASETEN_API_KEY": "b", "GLIMMER_API_KEY": "g",
           "GLIMMER_API_BASE": "https://example.invalid/v1/"}
    with patch.dict(os.environ, env):
        assert meta_client.provider(GLIMMER) == "glimmer"
        assert meta_client.endpoint(GLIMMER) == ("https://example.invalid/v1", "g")
        assert meta_client.endpoint(OPEN) == (meta_client.BASETEN_URL, "b")


def test_missing_glimmer_key_fails_before_any_request():
    env = {k: v for k, v in os.environ.items() if not k.startswith("GLIMMER_")}
    env["GLIMMER_API_BASE"] = "https://example.invalid/v1"
    with patch.dict(os.environ, env, clear=True), patch.object(meta_client, "ROOT", pathlib.Path("/nonexistent")), \
            patch.object(meta_client.urllib.request, "urlopen") as urlopen:
        try:
            meta_client.chat(GLIMMER, [{"role": "user", "content": "x"}], "test")
            raise AssertionError("expected a missing-key error")
        except RuntimeError as e:
            assert "GLIMMER_API_KEY" in str(e)
        assert urlopen.call_count == 0


def test_glimmer_reasoning_effort_becomes_the_template_reasoning_strength():
    assert meta_client.request_fields(GLIMMER, {"reasoning_effort": "medium"}) == \
        {"chat_template_kwargs": {"reasoning_strength": "medium"}}
    assert meta_client.request_fields(OPEN, {"reasoning_effort": "medium"}) == {"reasoning_effort": "medium"}
    assert meta_client.request_fields("muse-spark-1.3", {}) == {}


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
