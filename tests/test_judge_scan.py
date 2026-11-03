"""Implementation scan regressions and the recorded form of container commands; no Docker or Lean runs.

Run: python3 tests/test_judge_scan.py
"""
import pathlib, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "harness"))
import judge, task as taskmod  # noqa: E402

GOOD = ROOT / "formal/evidence/muse-repair-002/Solution.lean"


def scan(source, task_id="payout-flagship"):
    with tempfile.TemporaryDirectory() as tmp:
        f = pathlib.Path(tmp) / "Solution.lean"
        f.write_text(source)
        return judge.impl_scan([f], taskmod.load(task_id))


def test_a_complete_candidate_declares_every_required_theorem():
    assert scan(GOOD.read_text())["passed"]


def test_a_required_theorem_kept_under_another_name_is_named_as_missing():
    # Muse's transfers-batch-b1 version 44 proved idempotency only as req_idempotency_final_tmp.
    src = GOOD.read_text().replace("theorem req_idempotency ", "theorem req_idempotency_final_tmp ", 1)
    r = scan(src)
    assert not r["passed"] and r["problems"] == ["required theorem missing: req_idempotency"]


def test_a_theorem_named_only_in_a_comment_does_not_count():
    src = GOOD.read_text().replace("theorem req_conservation ", "lemma conservation_draft ", 1)
    r = scan(src + "\n-- theorem req_conservation : Conserves step\n")
    assert "required theorem missing: req_conservation" in r["problems"]



def test_a_recorded_container_command_names_no_host_path():
    from unittest.mock import patch
    project = pathlib.Path(tempfile.mkdtemp(prefix="pf-judge-"))
    seen = []

    def fake_run(cmd, timeout=900, on_timeout=None, keep=4000):
        seen.append(cmd)
        return {"command": list(cmd), "exit_code": 0, "elapsed_ms": 1, "output_tail": ""}

    with patch.object(judge, "run", fake_run):
        for in_image in (True, False):
            with patch.object(judge, "IN_IMAGE", in_image):
                r = judge.in_container(project, "lake build")
            assert str(project) in " ".join(seen[-1])
            assert str(project) not in " ".join(r["command"]) and "<project>" in " ".join(r["command"]), r["command"]


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
