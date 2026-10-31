"""The Muse Code runner (agents/muse_code.py): the workspace of each arm, the prompts, the Muse Code
settings and the sanitizing of run records. No model calls, no Lean.

The workspace never holds reference solutions, attacks, witnesses, the README, the oracle or
results; the ProofForge arm also gets AGENTS.md, the skill and the vendored library. The two arms'
prompts differ only in the imports line and the tools line.

Run: python3 tests/test_muse_runner.py
"""
import pathlib, shutil, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse")]
import muse_code  # noqa: E402
import task as taskmod  # noqa: E402


def test_runner_workspace_and_prompts():
    t = taskmod.load("rw-cetus-shlw")
    alone = muse_code.make_workspace(t, "alone")
    pf = muse_code.make_workspace(t, "proofforge")
    for ws in (alone, pf):
        for leaked in ("reference", "attacks", "witnesses", "README.md", "oracle.py", "validation.json", "task.json"):
            assert not (ws / leaked).exists(), (ws, leaked)
        assert (ws / "candidate/Solution.lean").read_text() == t.start.read_text()
        assert t.issue in (ws / "ISSUE.md").read_text()
        assert subprocess.run(["git", "-C", str(ws), "status", "--porcelain"], capture_output=True, text=True).stdout == ""
    assert not (alone / "AGENTS.md").exists() and not (alone / ".agents").exists()
    assert not (alone / ".lake/packages/proofforge-fin").exists()
    assert (pf / "AGENTS.md").is_file() and (pf / ".agents/skills/proofforge/SKILL.md").is_file()
    assert (pf / ".lake/packages/proofforge-fin").is_dir()
    pa, pp = muse_code.prompt_for(t, "alone"), muse_code.prompt_for(t, "proofforge")
    diff = [(x, y) for x, y in zip(pa.splitlines(), pp.splitlines()) if x != y]
    assert len(pa.splitlines()) == len(pp.splitlines()) and len(diff) == 2, diff   # imports line and tools line
    assert "ProofForgeFin" not in pa and "check_candidate" not in pa
    shutil.rmtree(alone)
    shutil.rmtree(pf)


def test_runner_settings():
    t = taskmod.load("rw-cetus-shlw")
    s = muse_code.settings_for("alone", pathlib.Path("/w"), t, pathlib.Path("/o/mcp.jsonl"), pathlib.Path("/h"))
    srv = s["mcp_servers"]["proofforge"]
    assert s["schema_version"] == 1 and s["telemetry"] == {"enabled": False}
    assert srv["transport"] == "stdio" and srv["mode"] == "required" and srv["tool_timeout_sec"] == 3600
    assert srv["args"][srv["args"].index("--profile") + 1] == "lean" and "--blind" in srv["args"]
    s = muse_code.settings_for("proofforge", pathlib.Path("/w"), t, pathlib.Path("/o/mcp.jsonl"), pathlib.Path("/h"))
    srv = s["mcp_servers"]["proofforge"]
    assert srv["args"][srv["args"].index("--profile") + 1] == "proofforge"


def test_runner_sanitize():
    d = pathlib.Path(tempfile.mkdtemp())
    f = d / "events.jsonl"
    f.write_text(f'{{"cwd": "/var/folders/x/T/pf-muse-alone-1", "repo": "{ROOT}/bin"}}\n')
    muse_code.sanitize(f, [("/var/folders/x/T/pf-muse-alone-1", "<workspace>"), (str(ROOT), "<proofforge>")])
    assert f.read_text() == '{"cwd": "<workspace>", "repo": "<proofforge>/bin"}\n'


class FakeServer:
    def __init__(self, build, status):
        self.build, self.status = build, status

    def lean(self, script, timeout=None):
        return self.build

    def theorem_status(self, task):
        return self.status


def test_no_verdict_is_not_a_rejection():
    """A Docker failure, a time limit or a judge run without a verdict yields no message, never
    "the judge rejected it" (the runner then retries once and stops with judge_unavailable)."""
    from unittest.mock import patch
    t = taskmod.load("rw-cetus-shlw")
    ws = muse_code.make_workspace(t, "alone")
    ok_build = {"exit_code": 0, "output_tail": "Build completed successfully"}
    proved = {th: "PROVED" for th in t.theorems}
    docker_down = {"exit_code": 125, "output_tail": "docker: Cannot connect to the Docker daemon at unix:///x"}
    assert muse_code.ordinary_feedback(FakeServer(docker_down, proved), t, ws) == (False, None)
    timed_out = {"exit_code": 124, "output_tail": muse_code.judge.TIMEOUT_MARK}
    assert muse_code.ordinary_feedback(FakeServer(timed_out, proved), t, ws) == (False, None)
    missing = {th: "MISSING" for th in t.theorems}
    assert muse_code.ordinary_feedback(FakeServer(ok_build, missing), t, ws) == (False, None)
    no_verdict = {"accepted": False, "checks": {"tree": {"problems": []}, "impl_scan": {"problems": []},
                                                "comparator": {"exit_code": 1, "output_tail": "context canceled"}}}
    with patch.object(muse_code.judge, "judge", return_value=no_verdict):
        assert muse_code.ordinary_feedback(FakeServer(ok_build, proved), t, ws) == (False, None)
    rejected = {"accepted": False, "checks": {"tree": {"problems": []}, "impl_scan": {"problems": []},
                                              "comparator": {"exit_code": 1, "output_tail": "error: theorem statement differs"}}}
    with patch.object(muse_code.judge, "judge", return_value=rejected):
        ok, msg = muse_code.ordinary_feedback(FakeServer(ok_build, proved), t, ws)
        assert not ok and "judge rejected it" in msg and "statement differs" in msg
    some_sorry = dict(proved, **{t.theorems[0]: "SORRY"})
    ok, msg = muse_code.ordinary_feedback(FakeServer(ok_build, some_sorry), t, ws)
    assert not ok and "not proved yet" in msg
    shutil.rmtree(ws)


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
