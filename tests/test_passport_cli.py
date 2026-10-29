"""Passport serialization and tampering regressions; no model or Docker calls."""
import contextlib, copy, hashlib, io, json, pathlib, runpy, shutil, sys, tempfile, types
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
    with patch.object(passport.judge, "image_id", return_value="test-image"), \
            patch.object(passport.judge, "image_platform", return_value="linux/amd64"):
        original = passport.build(task, ROOT / "formal/evidence/muse-repair-002/Solution.lean", j, b)
    assert original["executable"]["platform"] == "linux/amd64"
    with tempfile.TemporaryDirectory() as tmp:
        dest = pathlib.Path(tmp) / "passport.json"
        args = types.SimpleNamespace(task="payout-flagship", candidate="formal/evidence/muse-repair-002/Solution.lean",
                                     cases=2000, seed=0, out=str(dest), comment=None)
        with patch.object(passport, "run", return_value=copy.deepcopy(original)):
            assert cli["cmd_check"](args) == 0
        saved = json.loads(dest.read_text())
        digest = saved.pop("passport_sha256")
        assert digest == hashlib.sha256(json.dumps(saved, sort_keys=True).encode()).hexdigest()
        assert saved["reproduce"].startswith(f"bin/proofforge verify {dest} --candidate")


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


def built_passport(platform, exe_sha, binary_status="PASS"):
    task = passport.taskmod.load()
    j = {"accepted": True, "elapsed_ms": 0, "solution_tree_sha256": "test-source",
         "checks": {"tree": {"passed": True, "problems": []}, "impl_scan": {"passed": True, "problems": []}}}
    b = {"status": binary_status, "cases": 2001, "followup_cases": 0, "seed": 0, "violations": {}, "binary_sha256": exe_sha}
    if binary_status != "PASS":
        j["accepted"] = False
    with patch.object(passport.judge, "image_id", return_value="test-image"), \
            patch.object(passport.judge, "image_platform", return_value=platform):
        return passport.build(task, ROOT / "formal/evidence/muse-repair-002/Solution.lean", j, b)


def verify_against(issued, rechecked):
    with tempfile.TemporaryDirectory() as tmp:
        dest = pathlib.Path(tmp) / "passport.json"
        dest.write_text(json.dumps(issued))
        out = io.StringIO()
        with patch.object(passport, "run", return_value=rechecked), contextlib.redirect_stdout(out):
            code = cli["cmd_verify"](types.SimpleNamespace(passport=str(dest), candidate="unused"))
        return code, out.getvalue()


def test_executable_hash_is_compared_only_on_the_same_platform():
    issued = built_passport("linux/amd64", "a" * 64)
    code, out = verify_against(issued, built_passport("linux/arm64", "b" * 64))
    assert code == 0 and "not compared  executable" in out and "reproduced, except the executable hash" in out
    code, out = verify_against(issued, built_passport("linux/amd64", "b" * 64))
    assert code == 1 and "DIFFERENT  executable:" in out
    code, out = verify_against(issued, built_passport("linux/arm64", "b" * 64, binary_status="REFUTED"))
    assert code == 1 and "DIFFERENT  executable tests" in out


def test_passport_without_a_platform_still_compares_the_executable():
    issued = built_passport("linux/amd64", "a" * 64)
    del issued["executable"]["platform"]
    issued["passport_sha256"] = passport.content_hash(issued)
    code, out = verify_against(issued, built_passport("linux/arm64", "b" * 64))
    assert code == 1 and "does not record its build platform" in out


def test_missing_comparator_config_is_a_rejection_not_a_crash():
    with tempfile.TemporaryDirectory() as tmp:
        root = pathlib.Path(tmp) / "formal"
        shutil.copytree(ROOT / "formal", root, ignore=shutil.ignore_patterns(".lake", "__pycache__"))
        (root / "spec/comparator.json").unlink()
        task = passport.taskmod.load(str(root))
        locked = json.loads((root / "spec/locked.json").read_text())
        tree = passport.judge.tree_check(pathlib.Path(tmp) / "empty", locked, task)
        assert not tree["passed"] and "repository protected file missing: spec/comparator.json" in tree["problems"]
        assert passport.permitted_axioms(task) == []


def test_realworld_task_loads_by_id_for_verify():
    assert passport.taskmod.load("rw-gomoney-split").root == ROOT / "realworld/tasks/rw-gomoney-split"


def test_reconstructed_task_note_is_on_every_passport_and_only_there():
    plain = built_passport("linux/amd64", "a" * 64)
    assert "reconstruction" not in plain and plain["trust_assumptions"] == passport.TRUST
    note = "Reconstructed from published findings; not the original code."
    with tempfile.TemporaryDirectory() as tmp:
        root = pathlib.Path(tmp) / "formal"
        shutil.copytree(ROOT / "formal", root, ignore=shutil.ignore_patterns(".lake", "__pycache__"))
        meta = json.loads((root / "task.json").read_text())
        meta["source"] = {"reconstructed": True, "passport_note": note}
        (root / "task.json").write_text(json.dumps(meta))
        task = passport.taskmod.load(str(root))
        j = {"accepted": False, "elapsed_ms": 0, "solution_tree_sha256": "test-source",
             "checks": {"tree": {"passed": True, "problems": []}, "impl_scan": {"passed": True, "problems": []}}}
        b = {"status": "REFUTED", "cases": 2001, "followup_cases": 0, "seed": 0, "violations": {}}
        with patch.object(passport.judge, "image_id", return_value="test-image"), \
                patch.object(passport.judge, "image_platform", return_value="linux/amd64"):
            p = passport.build(task, root / "candidate/Solution.lean", j, b)
    assert p["reconstruction"] == note and p["trust_assumptions"] == passport.TRUST + [note]
    assert p["passport_sha256"] == passport.content_hash(p)
    assert note in passport.markdown(p)


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
