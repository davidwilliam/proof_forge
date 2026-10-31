"""The ProofForge MCP server (integrations/muse/proofforge_mcp.py). No model calls.

Without Lean: the JSON-RPC protocol over stdio, the two tool profiles, task listing and the
locked requirements, blind mode, path containment, output scrubbing, library search.

SLOW (skipped with --quick, and without Docker and the pinned image): `lean_build`, `try_snippet`
and `check_candidate` on queues-ring-b1, whose start candidate is REFUTED and whose reference
solution is VERIFIED with a Passport that `verify_passport` reproduces.

Run: python3 tests/test_muse_mcp.py [--quick]
"""
import json, pathlib, shutil, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "integrations" / "muse"), str(ROOT / "agents"), str(ROOT / "harness")]
import proofforge_mcp as pm  # noqa: E402
import task as taskmod  # noqa: E402

TASK = "queues-ring-b1"


def workspace(task=TASK):
    t = taskmod.load(task)
    ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-mcp-test-"))
    for rel in taskmod.PROJECT_FILES:
        src = t.root / rel
        (shutil.copytree if src.is_dir() else shutil.copy)(src, ws / rel)
    (ws / "candidate").mkdir()
    shutil.copy(t.start, ws / "candidate/Solution.lean")
    (ws / ".proofforge").mkdir()
    (ws / ".proofforge/task.json").write_text(json.dumps({"task": task}))
    return ws


def rpc(lines, *args):
    """Run the server as Muse Code does (a subprocess on stdio) and return its responses."""
    p = subprocess.run([sys.executable, str(ROOT / "integrations/muse/proofforge_mcp.py"), *args],
                       input="".join(json.dumps(m) + "\n" for m in lines), capture_output=True, text=True, timeout=600)
    return [json.loads(l) for l in p.stdout.splitlines() if l.strip()]


INIT = {"jsonrpc": "2.0", "id": 1, "method": "initialize",
        "params": {"protocolVersion": "2025-06-18", "capabilities": {}, "clientInfo": {"name": "test", "version": "0"}}}


def test_protocol_over_stdio():
    ws = workspace()
    out = rpc([INIT, {"jsonrpc": "2.0", "method": "notifications/initialized"},
               {"jsonrpc": "2.0", "id": 2, "method": "tools/list"},
               {"jsonrpc": "2.0", "id": 3, "method": "ping"},
               {"jsonrpc": "2.0", "id": 4, "method": "no/such"},
               {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {"name": "list_tasks", "arguments": {"split": "realworld"}}},
               {"jsonrpc": "2.0", "id": 6, "method": "tools/call", "params": {"name": "no_such_tool", "arguments": {}}}],
              "--workspace", str(ws))
    by = {r["id"]: r for r in out}
    assert len(out) == 6, out   # the notification gets no response
    assert by[1]["result"]["protocolVersion"] == "2025-06-18" and by[1]["result"]["serverInfo"]["name"] == "proofforge"
    names = [t["name"] for t in by[2]["result"]["tools"]]
    assert names == ["lean_build", "list_tasks", "show_task", "try_snippet", "check_candidate", "verify_passport",
                     "search_library"], names
    assert all(t["inputSchema"]["type"] == "object" for t in by[2]["result"]["tools"])
    assert by[3]["result"] == {}
    assert by[4]["error"]["code"] == -32601
    text = by[5]["result"]["content"][0]["text"]
    assert "rw-balancer-upscale" in text and "rc-knight-router" in text and by[5]["result"]["isError"] is False
    assert by[6]["result"]["isError"] is True


def test_unknown_protocol_version_gets_the_latest():
    ws = workspace()
    init = {**INIT, "params": {**INIT["params"], "protocolVersion": "1999-01-01"}}
    out = rpc([init], "--workspace", str(ws))
    assert out[0]["result"]["protocolVersion"] == pm.PROTOCOL_VERSIONS[0]


def test_lean_profile_has_only_lean_build():
    s = pm.Server(workspace(), TASK, profile="lean")
    assert [t["name"] for t in s.tools()] == ["lean_build"]
    try:
        s.call("check_candidate", {})
        raise AssertionError("check_candidate available in the lean profile")
    except ValueError:
        pass


def test_show_task_lists_locked_requirements():
    s = pm.Server(workspace(), profile="proofforge")      # task from .proofforge/task.json
    doc = json.loads(s.show_task().split("\n\n=== README.md ===")[0])
    t = taskmod.load(TASK)
    assert [r["id"] for r in doc["requirements"]] == [rid for rid, _ in t.requirements]
    challenge = (t.root / t.spec_dir / "Challenge.lean").read_text()
    for r in doc["requirements"]:
        assert r["statement"] and r["statement"] in challenge, r
    assert doc["issue_report"] == t.issue


def test_blind_mode_omits_the_readme():
    s = pm.Server(workspace("rw-cetus-shlw"), "rw-cetus-shlw", profile="proofforge")
    assert "=== README.md ===" in s.show_task()
    s = pm.Server(workspace("rw-cetus-shlw"), "rw-cetus-shlw", profile="proofforge", blind=True)
    text = s.show_task()
    assert "=== README.md ===" not in text and "SolutionA" not in text


def test_hidden_tasks_and_paths_are_refused():
    s = pm.Server(workspace(), TASK)
    for bad in ("../x", "/etc/passwd"):
        try:
            s.path(bad)
            raise AssertionError(f"{bad} accepted")
        except ValueError:
            pass
    try:
        s.task("../../realworld/tasks/rw-balancer-upscale")
        raise AssertionError("path as task id accepted")
    except ValueError:
        pass
    assert all("hidden" not in t.split for t in pm.all_tasks())


def test_tool_output_is_scrubbed_of_machine_paths():
    text = pm.scrub(f"File {pm.ROOT}/harness/judge.py and {pathlib.Path.home()}/x")
    assert str(pm.ROOT) not in text and str(pathlib.Path.home()) not in text


def test_search_library():
    import fin_lib
    try:
        fin_lib.Index.load()
    except Exception as e:  # the library is built in the pinned image on first use
        print(f"skip  test_search_library: {e}")
        return
    s = pm.Server(workspace(), TASK)
    text = s.search_library("round up division ceilDiv", limit=5)
    assert "ceilDiv" in text and "(import ProofForgeFin" in text


# --------------------------------------------------------------------------------------------- Lean

def lean_available():
    r = subprocess.run(["docker", "image", "inspect", "proofforge-lean:4.35.0"], capture_output=True)
    return r.returncode == 0


def test_lean_tools():
    ws = workspace()
    s = pm.Server(ws, profile="proofforge")
    out = s.lean_build()
    assert out.startswith("$ lake build Solution") and "exit code 0" in out, out[-2000:]
    bad = s.try_snippet("theorem pf_snippet_test : 1 + 1 = 3 := by decide")
    assert bad.startswith("snippet:") or "snippet:" in bad, bad
    good = s.try_snippet("theorem pf_snippet_test : 1 + 1 = 2 := by decide")
    assert good.startswith("snippet compiles"), good
    assert (ws / "candidate/Solution.lean").read_text() == taskmod.load(TASK).start.read_text()
    (ws / "Probe.lean").write_text("import Solution\n#print axioms RingBuffer.req_valid_succeeds\n")
    out = s.lean_build("Probe.lean")
    assert "sorryAx" in out, out


def test_check_candidate_and_verify():
    t = taskmod.load(TASK)
    ws = workspace()
    s = pm.Server(ws, profile="proofforge")
    start = json.loads(s.check_candidate(cases=300))
    assert start["status"] in ("REFUTED", "UNRESOLVED") and start["passport_sha256"], start
    assert (ws / start["passport"]).is_file()
    if start["status"] == "REFUTED":
        assert any(r.get("witness") for r in start["requirements"])
    shutil.copy(sorted((t.root / "reference").glob("*.lean"))[0], ws / "candidate/Solution.lean")
    ref = json.loads(s.check_candidate())
    assert ref["status"] == "VERIFIED" and all(r["status"] == "VERIFIED" for r in ref["requirements"]), ref
    out = s.verify_passport(ref["passport"], ref["checked_file"])
    assert out.startswith("exit code 0") and "reproduced" in out, out


if __name__ == "__main__":
    quick = "--quick" in sys.argv
    for name, fn in list(globals().items()):
        if not name.startswith("test_"):
            continue
        if name in ("test_lean_tools", "test_check_candidate_and_verify") and (quick or not lean_available()):
            print(f"skip  {name}")
            continue
        fn()
        print(f"ok  {name}")
