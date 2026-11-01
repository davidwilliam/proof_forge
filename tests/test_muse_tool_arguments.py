"""Arguments a ProofForge MCP tool does not take (integrations/muse/proofforge_mcp.py). No model
calls, no Lean: a scripted Lean answers `lean_build`.

lean_build failed outright on an argument it does not take: `max_output_tokens` in hard-task-1
(rw-oz-sqrt proofforge-full-1, rw-vyper-sqrt proofforge-full-2) and `candidate` in muse-code-1
(rc-knight-router proofforge-2). In every profile such an argument is now ignored:
the tool runs with the arguments it takes and its result ends with a note naming the ignored
ones; a call that omits an argument the tool needs is still an error.

Run: python3 tests/test_muse_tool_arguments.py
"""
import pathlib, shutil, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "integrations" / "muse"), str(ROOT / "agents"), str(ROOT / "harness")]
import proofforge_mcp as pm  # noqa: E402
import task as taskmod  # noqa: E402

TASK = taskmod.load("rw-oz-sqrt")
OUTPUT = "Build completed successfully (10 jobs)."


class Scripted(pm.Server):
    """The MCP server with a Lean that always compiles in place of the container."""
    def __init__(self, ws, profile):
        super().__init__(ws, TASK.id, profile)
        self.scripts = []

    def lean(self, script, timeout=None):
        self.scripts.append(script)
        return {"exit_code": 0, "output_tail": OUTPUT, "elapsed_ms": 1000}

    def theorem_status(self, t):
        return {th: "SORRY" for th in t.theorems}


def workspace():
    ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-args-ws-"))
    (ws / "candidate").mkdir()
    shutil.copy(TASK.start, ws / "candidate/Solution.lean")
    (ws / "Probe.lean").write_text("import Solution\n")
    return ws


def respond(server, name, args):
    """One tools/call through the JSON-RPC handler, as Muse Code sends it: (text, isError)."""
    r = server.handle({"jsonrpc": "2.0", "id": 7, "method": "tools/call", "params": {"name": name, "arguments": args}})
    res = r["result"]
    return res["content"][0]["text"], res["isError"]


def test_lean_build_ignores_an_argument_it_does_not_take_in_every_profile():
    ws = workspace()
    try:
        for profile in pm.PROFILES:
            s = Scripted(ws, profile)
            plain, err = respond(s, "lean_build", {})
            assert not err and plain.startswith("$ lake build Solution\nexit code 0"), plain
            text, err = respond(s, "lean_build", {"max_output_tokens": "3000"})
            assert not err, text
            assert text == plain + "\n(ignored argument that lean_build does not take: max_output_tokens)", (profile, text)
            text, err = respond(s, "lean_build", {"candidate": "candidate/Solution.lean", "max_output_tokens": 4000})
            assert not err and text.startswith("$ lake build Solution\nexit code 0"), text
            assert text.endswith("(ignored arguments that lean_build does not take: candidate, max_output_tokens)"), text
            # an argument the tool takes is still used, next to one it ignores
            text, err = respond(s, "lean_build", {"file": "Probe.lean", "verbose": True})
            assert not err and text.startswith("$ lake env lean Probe.lean"), text
            assert text.endswith("(ignored argument that lean_build does not take: verbose)"), text
            assert all("lake" in x for x in s.scripts)
    finally:
        shutil.rmtree(ws)


def test_other_tools_ignore_unknown_arguments_and_still_need_their_own():
    ws = workspace()
    try:
        s = Scripted(ws, "full")
        text, err = respond(s, "show_task", {"format": "json"})
        assert not err and text.startswith("{") and f'"id": "{TASK.id}"' in text, text
        assert text.endswith("(ignored argument that show_task does not take: format)"), text
        text, err = respond(s, "try_snippet", {"timeout": 30})           # `code` is missing
        assert err and "code" in text and "ignored" not in text, text
        text, err = respond(s, "no_such_tool", {"x": 1})
        assert err and text == "error: unknown tool 'no_such_tool'", text
        # arguments with the value null are dropped as before, without a note
        text, err = respond(s, "lean_build", {"file": None})
        assert not err and "ignored" not in text, text
    finally:
        shutil.rmtree(ws)


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
