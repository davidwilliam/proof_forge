"""POST /api/swap: the Balancer swap replay over the deployed port, the plus-one hotfix and the
verified Muse repair. No model calls. The input checks, the Passport binding and the request
handling run without Docker; with PF_TEST_SIDECAR=1 the last test also builds the three
swap-sidecars (Docker, or in the Lean image) and checks the attack batch's numbers.

Run: .venv/bin/python tests/test_swap_api.py
"""
import json, os, pathlib, re, sys, tempfile
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
DATA = pathlib.Path(tempfile.mkdtemp(prefix="pf-swap-test-"))
os.environ.update(PF_DATA=str(DATA), PF_PREWARM="0")
os.environ.pop("PF_MODE", None)
sys.path[:0] = [str(ROOT), str(ROOT / "harness")]

from fastapi import HTTPException  # noqa: E402
from starlette.requests import Request  # noqa: E402
import judge, task as taskmod  # noqa: E402
from server import app as api, controls  # noqa: E402

WETH, OSETH = "1000000000000000000", "1058132408689971699"
WITNESS = ROOT / "realworld/tasks/rw-balancer-upscale/witnesses/attack_batch.lean"


def request(ip="203.0.113.21"):
    return Request({"type": "http", "method": "POST", "path": "/api/swap", "client": (ip, 5000), "headers": []})


def raises(status, fn, *a, **kw):
    try:
        fn(*a, **kw)
    except HTTPException as e:
        assert e.status_code == status, (e.status_code, e.detail)
        return e
    raise AssertionError(f"expected HTTP {status}")


def attack_batch():
    """The four-round batch of witnesses/attack_batch.lean, part 1."""
    src = WITNESS.read_text()
    block = src[src.index("def batch"):src.index("theorem batch_runs")]
    return [{"kind": "out", "in": int(a), "out": int(b), "amount": int(c)}
            for a, b, c in re.findall(r"⟨\.givenOut, (\d), (\d), (\d+)⟩", block)]


def body(**kw):
    b = {"math": "product", "pool": {"balances": [67000, 67000], "rates": [WETH, OSETH], "fee": "100000000000000"},
         "swaps": attack_batch()}
    b.update(kw)
    return api.SwapRequest(**b)


def test_input_is_rebuilt_from_checked_whole_numbers():
    b = body()
    b.pool["extra"] = "x"
    b.swaps[0] = {**b.swaps[0], "cmd": "; rm -rf /"}
    out = api.swap_input(b)
    assert set(out) == {"math", "pool", "swaps"} and set(out["pool"]) == {"balances", "rates", "fee"}
    assert set(out["swaps"][0]) == {"kind", "in", "out", "amount"}
    assert out["pool"]["rates"] == [10 ** 18, 1058132408689971699] and out["pool"]["fee"] == 10 ** 14
    assert len(out["swaps"]) == 12 and out["swaps"][1]["amount"] == 17
    s = api.swap_input(body(math="stable", amp="200000"))
    assert s["amp"] == 200000


def test_input_limits():
    big = str(api.SWAP_MAX_AMOUNT + 1)
    bad = [
        body(math="sum"),
        body(math="stable"),                                       # no amp
        body(math="stable", amp=api.SWAP_MAX_AMP + 1),
        body(pool={"balances": [1, 2, 3], "rates": [WETH] * 3, "fee": 0}),
        body(pool={"balances": [1, 2], "rates": [WETH], "fee": 0}),
        body(pool={"balances": [big, 1], "rates": [WETH, WETH], "fee": 0}),
        body(pool={"balances": [1, 1], "rates": ["0", WETH], "fee": 0}),
        body(pool={"balances": [1, 1], "rates": [str(api.SWAP_MAX_RATE + 1), WETH], "fee": 0}),
        body(pool={"balances": [1, 1], "rates": [WETH, WETH], "fee": str(api.SWAP_MAX_FEE + 1)}),
        body(pool={"balances": [-1, 1], "rates": [WETH, WETH], "fee": 0}),
        body(pool={"balances": [1.5, 1], "rates": [WETH, WETH], "fee": 0}),
        body(pool={"balances": [True, 1], "rates": [WETH, WETH], "fee": 0}),
        body(pool={"balances": ["1e18", 1], "rates": [WETH, WETH], "fee": 0}),
        body(pool={"balances": ["１２", 1], "rates": [WETH, WETH], "fee": 0}),     # non-ASCII digits
        body(pool={"balances": ["1" * 41, 1], "rates": [WETH, WETH], "fee": 0}),
        body(swaps=[]),
        body(swaps=[{"kind": "out", "in": 0, "out": 1, "amount": 1}] * (api.SWAP_MAX_SWAPS + 1)),
        body(swaps=[{"kind": "both", "in": 0, "out": 1, "amount": 1}]),
        body(swaps=[{"kind": "out", "in": 0, "out": 0, "amount": 1}]),
        body(swaps=[{"kind": "out", "in": 0, "out": 2, "amount": 1}]),
        body(swaps=[{"kind": "out", "in": 0, "out": 1, "amount": big}]),
        body(swaps=["out 0 1 5"]),
    ]
    for b in bad:
        raises(400, api.swap_input, b)
    raises(400, api.swap, body(versions=["deployed", "deployed"]), request())
    raises(400, api.swap, body(versions=["../formal/candidate/Solution.lean"]), request())
    raises(400, api.swap, body(versions=[]), request())


def test_numbers_go_out_as_strings():
    assert api.stringify({"a": [1, None, True, {"b": 10 ** 40}], "s": "x"}) == \
        {"a": ["1", None, True, {"b": str(10 ** 40)}], "s": "x"}


def test_each_version_has_a_committed_passport_of_its_exact_source():
    want = {"deployed": "REFUTED", "plus_one": "REFUTED", "repaired": "VERIFIED"}
    for k, (src, pp) in api.SWAP_VERSIONS.items():
        sha = taskmod.sha256(ROOT / src)
        p = api.committed_passport(pp, sha)
        assert p and p["status"] == want[k], (k, p)
        assert p["passport_sha256"] == json.loads((ROOT / pp).read_text())["passport_sha256"]
        assert api.committed_passport(pp, "0" * 64) is None        # bound to the file, not the name
    assert api.committed_passport(api.SWAP_VERSIONS["repaired"][1], taskmod.sha256(ROOT / api.SWAP_VERSIONS["deployed"][0])) is None


def fake_sidecar(results, scripts):
    """in_container stand-in: records the script and writes the given result to the output file."""
    def run(project, script, timeout=900):
        scripts.append(script)
        m = re.fullmatch(r"\.lake/build/bin/swap-sidecar < (in-[A-Za-z0-9_]+)/in\.jsonl > \1/out\.jsonl", script)
        assert m, script
        (project / m.group(1) / "out.jsonl").write_text(json.dumps(results[project.name]) + "\n")
        return {"exit_code": 0, "elapsed_ms": 3, "output_tail": ""}
    return run


def fake_builds():
    root = pathlib.Path(tempfile.mkdtemp())
    out = {}
    for k, (src, _) in api.SWAP_VERSIONS.items():
        d = root / k
        (d / ".lake/build/bin").mkdir(parents=True)
        (d / ".lake/build/bin/swap-sidecar").write_text(k)
        out[str(ROOT / src)] = (d, taskmod.sha256(ROOT / src))
    return out


def test_swap_runs_every_version_with_fixed_scripts_and_counts_the_quota():
    builds = fake_builds()
    step = {"quote": 3182320, "ok": True, "balances": [3556673, 1], "value": 3556673}
    results = {k: {"steps": [step], "ok": True, "value_before": 7112707, "balances_after": [3556673, 1],
                   "value_after": 3556673} for k in api.SWAP_VERSIONS}
    scripts = []
    store = controls.Store(pathlib.Path(tempfile.mkdtemp()) / "server.db")
    with patch.object(api, "CTRL", controls.Controls(store)), \
            patch.object(api, "built_project", lambda t, src: builds[str(src)]), \
            patch.object(judge, "in_container", fake_sidecar(results, scripts)):
        r = api.swap(body(), request())
        assert [v["version"] for v in r["versions"]] == ["deployed", "plus_one", "repaired"]
        assert r["versions"][0]["result"]["value_after"] == "3556673"
        assert r["versions"][0]["result"]["steps"][0]["balances"] == ["3556673", "1"]
        assert r["versions"][2]["passport"]["passport_sha256"].startswith("48930efdd4d6")
        assert r["input"]["pool"]["rates"] == [WETH, OSETH]
        assert len(scripts) == 3 and store.used("203.0.113.21", "swap") == 1
        one = api.swap(body(versions=["repaired"]), request())
        assert [v["version"] for v in one["versions"]] == ["repaired"]


def test_swap_waits_for_prewarm_and_reports_timeouts_and_refusals():
    builds = fake_builds()
    with patch.object(api, "WARM", type("E", (), {"is_set": lambda self: False})()):
        e = raises(503, api.swap, body(), request())
        assert e.headers["Retry-After"]
    stopped = lambda project, script, timeout=900: {"exit_code": 124, "elapsed_ms": 1, "output_tail": judge.TIMEOUT_MARK}
    with patch.object(api, "built_project", lambda t, src: builds[str(src)]), \
            patch.object(judge, "in_container", stopped):
        raises(504, api.swap, body(), request(ip="203.0.113.22"))
    refused = {k: {"error": "bad input"} for k in api.SWAP_VERSIONS}
    with patch.object(api, "built_project", lambda t, src: builds[str(src)]), \
            patch.object(judge, "in_container", fake_sidecar(refused, [])):
        raises(400, api.swap, body(), request(ip="203.0.113.23"))


def test_quota_kind_exists():
    assert controls.QUOTA["swap"] > 0 and controls.JUDGE_QUOTA["swap"] >= controls.QUOTA["swap"]


def test_built_sidecars_reproduce_the_kernel_checked_attack():
    """With PF_TEST_SIDECAR=1: the three real builds on the attack batch of the witness file."""
    if os.environ.get("PF_TEST_SIDECAR") != "1":
        print("skip  test_built_sidecars_reproduce_the_kernel_checked_attack (set PF_TEST_SIDECAR=1)")
        return
    r = api.swap(body(), request(ip="203.0.113.30"))
    v = {x["version"]: x["result"] for x in r["versions"]}
    # witnesses/attack_batch.lean: value_before, value_after, balances_after (checked by `decide`)
    assert v["deployed"]["ok"] and v["deployed"]["value_before"] == "4749898000"
    assert v["deployed"]["value_after"] == "297229191" and v["deployed"]["balances_after"] == ["4193", "66993"]
    for k in ("plus_one", "repaired"):
        assert not v[k]["ok"] and v[k]["value_after"] == "4749898000"
        assert all(int(s["value"]) >= 4749898000 for s in v[k]["steps"])
    refuse = api.SwapRequest(math="product", pool={"balances": [1000000, 10], "rates": [WETH, WETH], "fee": "100000000000000"},
                             swaps=[{"kind": "out", "in": 0, "out": 1, "amount": 9}])
    v = {x["version"]: x["result"] for x in api.swap(refuse, request(ip="203.0.113.31"))["versions"]}
    assert v["repaired"]["ok"] and v["deployed"]["ok"] and not v["plus_one"]["ok"]


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
