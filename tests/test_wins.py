"""The wins ledger (eval/wins.py) on the committed data; no model calls, no Lean, no network.

Checks the computed counts against the counts the experiment READMEs and reports state, that the
three known differences between README prose and the raw data are still detected, that the build
is deterministic, and that the committed results/wins files match a fresh build.
"""
import importlib.util, json, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("wins", ROOT / "eval" / "wins.py")
wins = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wins)

L = wins.build()
BY = {c["id"]: c for c in L["comparisons"]}


def verified(cid):
    c = BY[cid]
    return c["alone"]["verified"], c["alone"]["runs"], c["proofforge"]["verified"], c["proofforge"]["runs"]


def test_muse_code_1():
    assert verified("muse-code-1/all-four") == (4, 7, 5, 7)
    assert verified("muse-code-1/rw-balancer-upscale") == (1, 3, 2, 3)
    assert verified("muse-code-1/rc-knight-router") == (2, 2, 2, 2)
    assert verified("muse-code-1/rw-cetus-shlw") == (1, 1, 1, 1)
    assert verified("muse-code-1/rw-compound-comp") == (0, 1, 0, 1)
    c = BY["muse-code-1/all-four"]
    assert (c["alone"]["list_usd_per_verified"], c["proofforge"]["list_usd_per_verified"]) == (9.5, 7.02)
    assert abs(BY["muse-code-1/rw-balancer-upscale"]["test"]["p"] - 0.5) < 1e-9


def test_hard_task_1():
    assert verified("hard-task-1/rw-vyper-sqrt") == (2, 5, 5, 5)
    assert verified("hard-task-1/rw-oz-sqrt") == (0, 5, 0, 5)
    assert verified("hard-task-1/both-tasks") == (2, 10, 5, 10)
    assert round(BY["hard-task-1/rw-vyper-sqrt"]["test"]["p"], 3) == 0.083
    assert round(BY["hard-task-1/both-tasks"]["test"]["p"], 3) == 0.175
    v = BY["hard-task-1/rw-vyper-sqrt"]
    assert (v["alone"]["list_usd_total"], v["proofforge"]["list_usd_total"]) == (45.88, 27.46)
    assert (v["alone"]["cap_stops"]["usd"], v["proofforge"]["cap_stops"]["usd"]) == (3, 0)
    assert v["test"]["preregistered"] and not v["test"]["significant_at_0_05"]


def test_e1():
    t = L["e1_arm_totals"]
    assert {a: t["e1-test-1"][a]["completed"] for a in ("A0", "A1", "A2")} == {"A0": 28, "A1": 30, "A2": 30}
    assert {a: t["e1-test-open-1"][a]["completed"] for a in ("A0", "A1")} == {"A0": 21, "A1": 24}
    assert {a: t["e1-dev-2"][a]["completed"] for a in ("A0", "A1", "A2")} == {"A0": 19, "A1": 20, "A2": 21}
    assert {a: t["e1-dev-1"][a]["completed"] for a in ("A0", "A1", "A2")} == {"A0": 20, "A1": 11, "A2": 17}
    # glimmer: the README's counts excluding the outage runs, and the 13 tasks with both arms scored
    assert (t["e1-test-glimmer-1"]["A0"]["scored"], t["e1-test-glimmer-1"]["A0"]["completed"]) == (15, 0)
    assert (t["e1-test-glimmer-1"]["A1"]["scored"], t["e1-test-glimmer-1"]["A1"]["completed"]) == (13, 3)
    assert verified("e1-test-glimmer-1/all/A1-vs-A0") == (0, 13, 3, 13)
    assert "incomplete" in BY["e1-test-glimmer-1/all/A1-vs-A0"]["flags"]
    # McNemar as the evaluator reports it
    assert BY["e1-test-1/all/A1-vs-A0"]["test"]["p"] == 0.5
    assert round(BY["e1-test-open-1/all/A1-vs-A0"]["test"]["p"], 4) == 0.5078
    assert BY["e1-test-open-1/all/A1-vs-A0"]["test"]["discordant"] == {"proofforge_only": 6, "alone_only": 3}


def test_flagships_and_library():
    for task, n in (("rw-cetus-shlw", 2), ("rw-euler-donate", 2), ("rw-hundred-vault", 2),
                    ("rw-balancer-upscale", 1), ("rc-knight-router", 1), ("rw-compound-comp", 0)):
        ids = [cid for cid in BY if cid.startswith("baseline-flagships-1+") and f"/{task}/" in cid]
        assert ids and all(BY[cid]["alone"]["verified"] == n and BY[cid]["alone"]["runs"] == 2 for cid in ids), task
    assert verified("baseline-flagships-1+knight-1/rc-knight-router/A1-vs-A0")[2:] == (0, 2)
    assert verified("baseline-flagships-1+knight-1/rc-knight-router/A2-vs-A0")[2:] == (1, 2)
    assert verified("baseline-flagships-1+compound-1/rw-compound-comp/A2-vs-A0")[2:] == (0, 2)
    assert BY["baseline-flagships-1+compound-1/rw-compound-comp/A2-vs-A0"]["proofforge"]["req_proved_per_run"] == [5, 5]
    c = BY["library-1/rw-balancer-upscale/all-measured/A2-vs-A0"]
    assert verified(c["id"]) == (2, 5, 3, 3)
    assert (c["alone"]["list_usd_total"], c["proofforge"]["list_usd_total"], c["proofforge"]["list_usd_per_verified"]) == (40.04, 9.18, 3.06)
    assert round(c["test"]["p"], 2) == 0.18


def test_catches():
    e = L["catches"][0]
    assert (e["bad_cases"], e["good_cases"]) == (247, 239)
    assert e["bad_accepted"] == {"ordinary": 233, "rebuild_and_tests": 1, "proofforge": 0}
    assert e["good_rejected"]["proofforge"] == 0


def test_wins_groups():
    g1 = {w["id"] for w in L["wins"]["1_alone_did_not_verify_proofforge_did"]}
    assert {"e1-test-1/ledgers-reversal-b1/A1-vs-A0", "e1-test-1/ledgers-reversal-b3/A1-vs-A0",
            "e1-test-1/ledgers-reversal-b1/A2-vs-A0", "e1-test-1/ledgers-reversal-b3/A2-vs-A0"} <= g1
    assert len([i for i in g1 if i.startswith("e1-test-open-1/") and "/all/" not in i]) == 6
    g2 = {w["id"]: w for w in L["wins"]["2_both_verified_proofforge_faster_or_cheaper"]}
    assert g2["hard-task-1/rw-vyper-sqrt"]["cost_factor"] == round(22.94 / 5.49, 2)
    assert "e2-all-1/catches" in {w["id"] for w in L["wins"]["3_other"]}
    # every win sentence names its comparison and carries no em or en dash
    for group in L["wins"].values():
        for w in group:
            assert w["sentence"].startswith(f"`{w['id']}`") and "—" not in w["sentence"] and "–" not in w["sentence"]
    # ties and losses are kept: the ledger is not only wins
    cnt = L["counts"]["classification"]["verification"]
    assert cnt["loss"] > 0 and cnt["tie"] > 0


def test_claims():
    known = {("results/README.md", "e1-dev-1: two runs lost to network timeouts"): (2, 3),
             ("README.md", "results/library-1 is running; no results are committed (section 'Muse alone and Muse with ProofForge')"): (0, 14)}
    differ = [c for c in L["claims"] if not c["matches"]]
    for c in differ:
        key = (c["source"], c["claim"])
        if c["source"] == "results/baseline-flagships-1/README.md":
            assert c["computed"] == "3600.0, 7200.0, 14400.0", c
        else:
            assert key in known and known[key] == (c["stated"], c["computed"]), c
    assert len(differ) == 3, differ
    assert len(L["claims"]) >= 60


def test_deterministic_and_committed():
    a = json.dumps(L, indent=1, ensure_ascii=False) + "\n"
    b = json.dumps(wins.build(), indent=1, ensure_ascii=False) + "\n"
    assert a == b
    committed = ROOT / "results/wins/ledger.json"
    if committed.exists():
        old = json.loads(committed.read_text())
        if old["optional_sources"] == L["optional_sources"]:
            assert committed.read_text() == a, "results/wins/ledger.json is stale: run python3 eval/wins.py"
            assert (ROOT / "results/wins/README.md").read_text() == wins.readme(L), "results/wins/README.md is stale"


def test_statistics():
    assert abs(wins.fisher_one_sided(5, 5, 2, 5) - 21 / 252) < 1e-12
    assert wins.mcnemar_exact(2, 0) == 0.5
    assert abs(wins.mann_whitney_less([1, 2, 3], [4, 5, 6]) - 1 / 20) < 1e-12


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
