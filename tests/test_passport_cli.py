"""Passport serialization and tampering regressions; no model or Docker calls."""
import copy, hashlib, json, pathlib, runpy, sys, tempfile, types
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "harness"))
import passport

cli = runpy.run_path(str(ROOT / "bin/proofforge"))


def test_cli_hashes_the_final_serialized_passport():
    task = passport.taskmod.load()
    j = {"accepted": True, "elapsed_ms": 0, "solution_tree_sha256": "test-source",
         "checks": {"tree": {"passed": True, "problems": []},
                    "impl_scan": {"passed": True, "problems": []}}}
    b = {"status": "PASS", "cases": 2001, "followup_cases": 0, "seed": 0, "violations": {}}
    with patch.object(passport.judge, "image_id", return_value="test-image"):
        original = passport.build(task, ROOT / "formal/evidence/muse-repair-002/Solution.lean", j, b)
    with tempfile.TemporaryDirectory() as tmp:
        dest = pathlib.Path(tmp) / "passport.json"
        args = types.SimpleNamespace(task="payout-flagship", candidate="formal/evidence/muse-repair-002/Solution.lean",
                                     cases=2000, seed=0, out=str(dest), comment=None)
        with patch.object(passport, "run", return_value=copy.deepcopy(original)):
            assert cli["cmd_check"](args) == 0
        saved = json.loads(dest.read_text())
        digest = saved.pop("passport_sha256")
        assert digest == hashlib.sha256(json.dumps(saved, sort_keys=True).encode()).hexdigest()
        assert saved["reproduce"].startswith("proofforge verify")


def test_changed_passport_is_refused_before_rechecking():
    with tempfile.TemporaryDirectory() as tmp:
        dest = pathlib.Path(tmp) / "passport.json"
        data = {"status": "VERIFIED", "scope": "original scope"}
        data["passport_sha256"] = passport.content_hash(data)
        data["scope"] = "changed scope"
        dest.write_text(json.dumps(data))
        with patch.object(passport, "run") as judge:
            assert cli["cmd_verify"](types.SimpleNamespace(passport=str(dest), candidate="unused")) == 1
            judge.assert_not_called()


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
