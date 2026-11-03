"""The API's task listing, the counterexample option of POST /api/verify and GET /api/results.
No model calls, no Docker and no Lean: the Passport pipeline is replaced by a stub.

Run: .venv/bin/python tests/test_api_tasks.py
"""
import os, pathlib, sys, tempfile
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
DATA = pathlib.Path(tempfile.mkdtemp(prefix="pf-api-tasks-test-"))
os.environ.update(PF_DATA=str(DATA), PF_PREWARM="0")
os.environ.pop("PF_MODE", None)
sys.path[:0] = [str(ROOT), str(ROOT / "harness")]

from starlette.requests import Request  # noqa: E402
import passport, task as taskmod  # noqa: E402
from server import app as api  # noqa: E402

FLAGSHIP_TASKS = ["rw-cetus-shlw", "rw-euler-donate", "rw-hundred-vault", "rw-balancer-upscale",
                  "rc-knight-router", "rw-compound-comp"]


def request(ip="203.0.113.9"):
    return Request({"type": "http", "method": "POST", "path": "/api/verify", "client": (ip, 5000), "headers": []})


def test_tasks_lists_benchmark_and_realworld_tasks():
    listed = api.tasks()
    ids = [t["id"] for t in listed]
    assert len(ids) == len(set(ids))
    bench = [t.id for t in taskmod.all_tasks() if (t.root / "spec/locked.json").exists()]
    realworld = sorted(d.name for d in taskmod.REALWORLD.glob("*") if (d / "task.json").exists())
    assert ids == bench + realworld
    for tid in FLAGSHIP_TASKS:
        assert tid in ids, tid
    rw = api.tasks(split="realworld")
    assert [t["id"] for t in rw] == realworld
    assert all(t["split"] == "realworld" and t["requirements"] for t in rw)
    assert [t["id"] for t in api.tasks(split="test")] == [t.id for t in taskmod.all_tasks("test")]


def test_listing_never_includes_hidden_variants():
    ids = {t["id"] for t in api.tasks()}
    hidden = {d.name for d in (ROOT / "hidden").glob("*") if (d / "task.json").exists()}
    assert hidden and not (ids & hidden)
    assert api.tasks(split="hidden") == []


def test_every_listed_task_is_reachable_by_id():
    for t in api.tasks():
        assert api.public_task(t["id"]).id == t["id"]


def test_verify_passes_the_counterexample_option_to_the_pipeline():
    seen = []

    def run(f, t, cases=2000, seed=0, provenance=None, counterexample=False):
        seen.append((t.id, cases, seed, counterexample))
        return {"status": "REFUTED", "requirements": [], "solution": {"files": {}}}

    with patch.object(passport, "run", run), patch.object(api, "issue_passport", lambda p, f: p):
        src = (ROOT / "realworld/tasks/rw-cetus-shlw/attacks/pr6_mask_only.lean").read_text()
        api.verify(api.VerifyRequest(task="rw-cetus-shlw", source=src, counterexample=True), request())
        api.verify(api.VerifyRequest(task="rw-cetus-shlw", source=src), request(ip="203.0.113.10"))
    assert seen == [("rw-cetus-shlw", 1000, 0, True), ("rw-cetus-shlw", 1000, 0, False)]



def test_results_serve_the_muse_code_experiments_with_their_passports():
    r = api.results()
    assert list(r)[:6] == list(api.MUSE_CODE_EXPERIMENTS)
    f4 = r["frontier-4"]
    task = next(c for c in f4["comparisons"] if c["id"] == "frontier-4/rw-compound-comp")
    assert (task["alone"]["verified"], task["proofforge"]["verified"]) == (0, 8)
    assert len(f4["runs"]) == 20 and sum(x["status"] == "VERIFIED" for x in f4["runs"]) == 8
    assert all((ROOT / x["passport"]).exists() and len(x["passport_sha256"]) == 64 for x in f4["runs"])
    assert "e1-test-open-2" in r and "e2-all-1" in r


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
