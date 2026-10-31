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
    assert srv["transport"] == "stdio" and srv["mode"] == "required"
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


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
