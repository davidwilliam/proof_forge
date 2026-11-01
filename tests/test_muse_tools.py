"""The `full` profile of the ProofForge MCP server (integrations/muse/proofforge_mcp.py and
integrations/muse/session_tools.py) and the runner's resume, tool counts and ledger
(agents/muse_code.py). No model calls: every tool call is scripted JSON-RPC, as Muse Code sends it.

Without Lean: the tool lists of the three profiles (the `lean` and `proofforge` profiles are those
of results/muse-code-1), statement forms for refute_statement, argument errors, search_library
with a goal named by a declaration, the runner's settings and prompts for proofforge-full and for
resumed runs, the tool counts of a run summary, the ledger of a Muse Code run built from its MCP
calls, and the refusal of --resume-from for another spec before any work.

With Lean (the pinned image; at most two containers: the persistent Lean server and one more,
with PF_CONTAINER_SLOTS=1), on rate-limiters-bucket-b1 (a small task):
  * over stdio, one server: goal_at at a `sorry` and at a line; check_snippet_fast with an error
    and a `sorry` (the state at it) and a clean snippet; try_tactics closing an easy goal (the proof
    text, nothing banked) and leaving a hard one open; refute_statement with a false statement (a
    kernel-checked counterexample), a true one, and a theorem of the candidate by name;
    search_library with a goal; prior_attempts carrying the declarations Lean re-checks, dropping
    a broken one and its dependent, refusing a ledger for another spec, with the failure notes;
    lean_build recording the compiled candidate. The candidate file and the workspace's git status
    are unchanged and no Lean container of the server is left;
  * the idle shutdown stops the persistent server and the next call starts it again;
  * the runner's resume base is the prior final file that compiles with the most theorems proved.

Run: python3 tests/test_muse_tools.py [--quick] [name ...]   (--quick skips the Lean runs)
"""
import json, os, pathlib, shutil, subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "integrations" / "muse"), str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "tests")]
import proofforge_mcp as pm, session_tools as st, muse_code, ledger, judge, fin_lib  # noqa: E402
import task as taskmod  # noqa: E402
import test_topdown as td  # noqa: E402
import test_feedback as fb  # noqa: E402

BUCKET = td.BUCKET
GOALS = """theorem gt_step (n m : Nat) (h : n < m) : n + 1 ≤ m := by
  have h2 : n + 1 ≤ m := by
    sorry
  exact h2

theorem easy_succ_le (n m : Nat) (h : n < m) : n + 1 ≤ m := by
  sorry

theorem hard_capacity (s : State) (r : Request) :
    (step s r).2.tokens ≤ (step s r).2.capacity := by
  sorry"""

BASIC = ["lean_build", "list_tasks", "show_task", "try_snippet", "check_candidate", "verify_passport", "search_library"]
FULL = BASIC + ["goal_at", "check_snippet_fast", "try_tactics", "refute_statement"]


def start_file(extra=GOALS):
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-muse-tools-start-"))
    (d / "Solution.lean").write_text(td.FIXED_BUCKET.replace("end TokenBucket", extra.strip() + "\n\nend TokenBucket"))
    return d / "Solution.lean"


def workspace(start=None, arm="proofforge-full"):
    return muse_code.make_workspace(BUCKET, arm, start or start_file())


INIT = {"jsonrpc": "2.0", "id": 0, "method": "initialize",
        "params": {"protocolVersion": "2025-06-18", "capabilities": {}, "clientInfo": {"name": "test", "version": "0"}}}


def call(i, tool, **args):
    return {"jsonrpc": "2.0", "id": i, "method": "tools/call", "params": {"name": tool, "arguments": args}}


def rpc(msgs, *args, timeout=1800):
    """The server as Muse Code runs it (a subprocess on stdio): {id: response}, and its pid."""
    p = subprocess.Popen([sys.executable, str(ROOT / "integrations/muse/proofforge_mcp.py"), *args],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    out, err = p.communicate("".join(json.dumps(m) + "\n" for m in [INIT] + msgs), timeout=timeout)
    res = {}
    for line in out.splitlines():
        if line.strip():
            r = json.loads(line)
            res[r["id"]] = r
    return res, p.pid, err


def text(res, i):
    r = res[i]["result"]
    return r["content"][0]["text"], r["isError"]


def tool_names(*args):
    res, _, _ = rpc([{"jsonrpc": "2.0", "id": 1, "method": "tools/list"}], *args)
    return {t["name"]: t for t in res[1]["result"]["tools"]}


# Without Lean

def test_profiles_and_tool_lists():
    ws = workspace()
    try:
        assert list(tool_names("--workspace", str(ws), "--profile", "lean")) == ["lean_build"]
        basic = tool_names("--workspace", str(ws), "--profile", "proofforge")
        assert list(basic) == BASIC, list(basic)
        assert set(basic["search_library"]["inputSchema"]["properties"]) == {"query", "limit"}   # as in muse-code-1
        full = tool_names("--workspace", str(ws), "--profile", "full")
        assert list(full) == FULL, list(full)
        assert "goal" in full["search_library"]["inputSchema"]["properties"]
        assert all(t["inputSchema"]["type"] == "object" for t in full.values())
        resumed = tool_names("--workspace", str(ws), "--profile", "full", "--resume-from", "/x/run-1")
        assert list(resumed) == FULL + ["prior_attempts"], list(resumed)
        # prior_attempts needs the full profile and a resumed run
        assert "prior_attempts" not in tool_names("--workspace", str(ws), "--profile", "proofforge",
                                                  "--resume-from", "/x/run-1")
    finally:
        shutil.rmtree(ws, ignore_errors=True)


def test_statement_forms():
    n = st.PROBE_NAME
    assert st.statement_decl("theorem foo (n m : Nat) : n - m + m = n") == f"theorem {n} (n m : Nat) : n - m + m = n := by\n  sorry"
    assert st.statement_decl("lemma foo {a : Nat} (h : 0 < a) : a ≠ 0 := by omega") == \
        f"theorem {n} {{a : Nat}} (h : 0 < a) : a ≠ 0 := by\n  sorry"
    assert st.statement_decl("(x : Nat) : x + 0 = x") == f"theorem {n} (x : Nat) : x + 0 = x := by\n  sorry"
    assert st.statement_decl(": ∀ x : Nat, x + 0 = x") == f"theorem {n} : ∀ x : Nat, x + 0 = x := by\n  sorry"
    assert st.statement_decl("∀ x : Nat, x ≤ x * x") == f"theorem {n} : ∀ x : Nat, x ≤ x * x := by\n  sorry"
    try:
        st.statement_decl("  ")
        raise AssertionError("an empty statement was accepted")
    except ValueError:
        pass


def test_argument_errors_need_no_lean():
    ws = workspace()
    s = pm.Server(ws, BUCKET.id, profile="full")
    try:
        for args in ({}, {"statement": ": True", "name": "gt_step"}):
            try:
                s.call("refute_statement", args)
                raise AssertionError(f"refute_statement accepted {args}")
            except ValueError:
                pass
        out = s.call("try_tactics", {"name": "req_valid_succeeds_nonexistent"})
        assert out.startswith("error: no declaration"), out
        out = s.call("try_tactics", {"name": "step"})            # a definition, not an open theorem
        assert out.startswith("error: `step` is not a theorem") and "sorry" in out, out
        out = s.call("goal_at", {"name": "no_such_decl"})
        assert out.startswith("error: no declaration"), out
        out = s.call("refute_statement", {"name": "no_such_theorem"})
        assert out.startswith("error: no theorem"), out
        # Nothing reached Lean: no persistent server was started.
        assert s._session.__dict__.get("lean_server") is None
        assert (ws / "candidate/Solution.lean").read_text() == start_file().read_text()
        try:
            s.call("prior_attempts", {})                      # not offered without --resume-from
            raise AssertionError("prior_attempts offered without a resumed run")
        except ValueError:
            pass
    finally:
        s.cleanup()
        shutil.rmtree(ws, ignore_errors=True)


def test_search_library_with_a_goal_named_by_a_declaration():
    try:
        index = fin_lib.Index.load()
    except Exception as e:  # the library is built in the pinned image on first use
        print(f"   skip: {e}")
        return
    ws = workspace()
    s = pm.Server(ws, BUCKET.id, profile="full")
    try:
        stmt = "theorem easy_succ_le (n m : Nat) (h : n < m) : n + 1 ≤ m"
        by_name = s.call("search_library", {"query": "successor bound", "goal": "easy_succ_le", "limit": 5})
        by_text = s.call("search_library", {"query": "successor bound", "goal": stmt, "limit": 5})
        assert by_name == by_text == fin_lib.render(index.search("successor bound", limit=5, goal=stmt))
        plain = s.call("search_library", {"query": "successor bound", "limit": 5})
        assert plain == fin_lib.render(index.search("successor bound", limit=5))
    finally:
        s.cleanup()
        shutil.rmtree(ws, ignore_errors=True)


def test_runner_settings_and_prompts_for_the_full_arm_and_resumed_runs():
    t = taskmod.load("rw-cetus-shlw")
    s = muse_code.settings_for("proofforge-full", pathlib.Path("/w"), t, pathlib.Path("/o/mcp.jsonl"), pathlib.Path("/h"),
                               pathlib.Path("/rec"), ["/r/a", "/r/b"])
    args = s["mcp_servers"]["proofforge"]["args"]
    assert args[args.index("--profile") + 1] == "full" and "--blind" in args
    assert args[args.index("--record-dir") + 1] == "/rec" and args[args.index("--resume-from") + 1] == "/r/a,/r/b"
    for arm in ("alone", "proofforge"):    # only the full toolset reads prior ledgers
        args = muse_code.settings_for(arm, pathlib.Path("/w"), t, pathlib.Path("/o/m"), pathlib.Path("/h"),
                                      pathlib.Path("/rec"), ["/r/a"])["mcp_servers"]["proofforge"]["args"]
        assert "--resume-from" not in args and args[args.index("--profile") + 1] == muse_code.PROFILE[arm]
    pp, pf = muse_code.prompt_for(t, "proofforge"), muse_code.prompt_for(t, "proofforge-full")
    diff = [(x, y) for x, y in zip(pp.splitlines(), pf.splitlines()) if x != y]
    assert len(pp.splitlines()) == len(pf.splitlines()) and len(diff) == 1 and "try_tactics" in diff[0][1], diff
    assert "prior_attempts" not in pf and "prior_attempts" in muse_code.prompt_for(t, "proofforge-full", resumed=True)
    for arm in muse_code.ARMS:
        plain, resumed = muse_code.prompt_for(t, arm), muse_code.prompt_for(t, arm, resumed=True)
        extra = [l for l in resumed.splitlines() if l not in plain.splitlines()]
        want = [muse_code.RESUMED_LINE, ""] if arm != "proofforge-full" else None
        assert muse_code.RESUMED_LINE in extra, (arm, extra)
        if want:
            assert len(resumed.splitlines()) == len(plain.splitlines()) + 2, arm
    ws = muse_code.make_workspace(t, "proofforge-full")
    try:
        assert (ws / "AGENTS.md").is_file() and (ws / ".agents/skills/proofforge/SKILL.md").is_file()
        assert (ws / fin_lib.VENDOR).is_dir()
    finally:
        shutil.rmtree(ws, ignore_errors=True)


def test_tool_counts_of_a_run():
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-muse-counts-"))
    try:
        ev = lambda kind: {"payload_type": "task.lifecycle.proposed", "payload": {"event": {"task_kind": kind}}}
        lines = [ev("tool.mcp__proofforge__try_tactics"), ev("tool.read_file"), ev("tool.mcp__proofforge__try_tactics"),
                 ev("model.meta.response"), ev("reminder.agent.goal-reminder"), {"payload_type": "tool.result"}]
        (out / "events.jsonl").write_text("\n".join(json.dumps(x) for x in lines) + "\nnot json\n")
        recs = [{"tool": "try_tactics", "seconds": 1.5, "error": False}, {"tool": "try_tactics", "seconds": 2.0, "error": True},
                {"tool": "goal_at", "seconds": 0.25, "error": False}]
        (out / "mcp-calls.jsonl").write_text("\n".join(json.dumps(x) for x in recs) + "\n")
        c = muse_code.tool_counts(out)
        assert c["muse_code"] == {"mcp__proofforge__try_tactics": 2, "read_file": 1}, c
        assert c["proofforge"] == {"try_tactics": {"calls": 2, "errors": 1, "seconds": 3.5},
                                   "goal_at": {"calls": 1, "errors": 0, "seconds": 0.2}}, c
        assert list(c["proofforge"]) == ["try_tactics", "goal_at"]
    finally:
        shutil.rmtree(out, ignore_errors=True)


def test_ledger_of_a_muse_code_run():
    """ledger.json from the compiled versions and the MCP calls: proved declarations, and failure
    notes per goal from the snippets that state it, the tactics tried and statements refuted."""
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-muse-ledger-"))
    try:
        recs = [
            {"tool": "try_snippet", "args": {"code": "theorem req_capacity : CapacityBound step := by\n  simp [step]  -- MARK1"},
             "result": "snippet:2:2: error: unsolved goals\n⊢ (step s r).2.tokens ≤ (step s r).2.capacity"},
            {"tool": "check_snippet_fast", "args": {"code": "theorem req_capacity : CapacityBound step := by\n  omega"},
             "result": "snippet:2:2: error: omega could not prove the goal"},
            {"tool": "try_tactics", "args": {"name": "req_capacity"}, "result": "no tactic closes it",
             "portfolio": {"goal": "req_capacity", "tried": ["grind", "omega"], "closed_by": None}},
            {"tool": "refute_statement", "args": {"name": "td0_bad"}, "result": "FALSE",
             "refute": {"name": "td0_bad", "status": "false"}},
            {"tool": "lean_build", "args": {}, "result": "exit code 0"},
        ]
        (out / "mcp-calls.jsonl").write_text("\n".join(json.dumps(r) for r in recs) + "\n")
        events = muse_code.ledger_events(out / "mcp-calls.jsonl", ["candidate/Solution.lean compiles. These ...", None])
        status = {t: ("SORRY" if t == "req_capacity" else "PROVED") for t in BUCKET.theorems}
        summary = {"model": "m", "meter": {"usd_list": 1.25}, "elapsed_s": 10.0}
        final = fb.CLEAN.replace("theorem req_capacity : CapacityBound step := sorry",
                                 "theorem td0_bad (n : Nat) : n = 0 := by\n  sorry\n\ntheorem req_capacity : CapacityBound step := sorry")
        led = muse_code.write_ledger(BUCKET, out, "proofforge-full", summary, [fb.CLEAN], events, final, status)
        assert json.loads((out / "ledger.json").read_text()) == led
        assert led["kind"] == ledger.KIND and led["task"] == BUCKET.id and led["spec_sha256"] == ledger.spec_sha256(BUCKET)
        assert {"td0_step_of_adm", "req_valid_succeeds"} <= {r["name"] for r in led["proved"]}
        goals = {g["name"]: g for g in led["open_goals"]}
        cap = goals["req_capacity"]
        assert "MARK1" in cap["tried"][0]["code"] and "unsolved goals" in cap["tried"][0]["lean"], cap["tried"]
        assert cap["tried"][1]["code"].endswith("omega") and "omega could not prove" in cap["tried"][1]["lean"]
        assert cap["portfolio"] == ["grind", "omega"] and goals["td0_bad"]["refuted"] is True
        assert led["budget"]["usd_list"] == 1.25 and led["loop"] == "muse-code"
        # The ledger loads back for this task and spec, and its notes reach the summary text.
        used, record = ledger.load_many([str(out)], BUCKET)
        assert len(used) == 1 and record[0]["used"]
        assert "MARK1" in ledger.summary_text(used)
        # A better compiling version than the final file becomes the best candidate.
        led = muse_code.write_ledger(BUCKET, out, "proofforge-full", summary, [], [], "broken", {},
                                     {"proved_required": ["req_effects"], "text": fb.CLEAN})
        assert led["best_candidate"]["version"] == "last compiling" and led["best_candidate"]["text"] == fb.CLEAN
    finally:
        shutil.rmtree(out, ignore_errors=True)


def test_resume_from_another_spec_stops_before_any_work():
    d_bad, _ = fb.prior_ledger(spec="0" * 64, name="badspec")
    from unittest.mock import patch
    try:
        with patch.object(sys, "argv", ["muse_code.py", "--task", BUCKET.id, "--arm", "proofforge-full",
                                        "--resume-from", str(d_bad)]), \
                patch.object(muse_code, "make_workspace", side_effect=AssertionError("workspace made")):
            try:
                muse_code.main()
                raise AssertionError("a run started from a ledger for another spec")
            except SystemExit as e:
                assert e.code == 2
    finally:
        shutil.rmtree(d_bad, ignore_errors=True)


def test_resume_paths_reach_the_server_absolute():
    """The MCP server runs in the workspace, so the runner hands it resolved run directories."""
    d_good, _ = fb.prior_ledger()
    from unittest.mock import patch
    seen = {}

    class Stop(Exception):
        pass

    def settings(*args):
        seen["resume"] = args[-1]
        raise Stop()
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-muse-resume-paths-"))
    try:
        rel = os.path.relpath(d_good)
        with patch.object(sys, "argv", ["muse_code.py", "--task", BUCKET.id, "--arm", "proofforge-full",
                                        "--resume-from", rel, "--out", str(out)]), \
                patch.object(muse_code, "make_workspace", return_value=out), \
                patch.object(muse_code, "settings_for", side_effect=settings):
            try:
                muse_code.main()
            except Stop:
                pass
        assert seen["resume"] == [str(d_good.resolve())], seen
        assert pm.Server(out, BUCKET.id, "full", resume_from=[rel]).resume_from == [str(d_good.resolve())]
    finally:
        shutil.rmtree(d_good, ignore_errors=True)
        shutil.rmtree(out, ignore_errors=True)


# With Lean

def lsp_containers(pid):
    if judge.IN_IMAGE:
        return []
    r = subprocess.run(["docker", "ps", "-q", "--filter", f"name=^pf-lsp-{pid}-"], capture_output=True, text=True)
    return r.stdout.split()


def test_full_tools_over_stdio():
    start = start_file()
    ws = workspace(start)
    d_prior, _ = fb.prior_ledger()
    d_bad, _ = fb.prior_ledger(spec="f" * 64, name="badspec")
    rec = pathlib.Path(tempfile.mkdtemp(prefix="pf-muse-tools-rec-"))
    log = rec / "mcp.jsonl"
    msgs = [
        call(1, "goal_at", name="gt_step"),
        call(2, "goal_at", name="gt_step", line=3),
        call(3, "check_snippet_fast", code="theorem gt_aux (a b : Nat) (h : a < b) : a + 2 ≤ b + 1 := by\n"
                                           "  have : a + 1 ≤ b := by sorry\n  exact Nat.le_refl _"),
        call(4, "check_snippet_fast", code="theorem gt_aux2 (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega"),
        call(5, "try_tactics", name="easy_succ_le"),
        call(6, "try_tactics", name="hard_capacity"),
        call(7, "refute_statement", statement="theorem sub_add (n m : Nat) : n - m + m = n"),
        call(8, "refute_statement", statement="(n m : Nat) : n + m - m = n"),
        call(9, "refute_statement", name="hard_capacity"),
        call(10, "search_library", query="sum over a list after one update", goal="hard_capacity", limit=3),
        call(11, "prior_attempts"),
        call(12, "lean_build"),
        call(13, "goal_at", name="req_valid_succeeds"),
    ]
    t0 = time.monotonic()
    res, pid, err = rpc(msgs, "--workspace", str(ws), "--profile", "full", "--log", str(log), "--record-dir", str(rec),
                        "--resume-from", f"{d_bad},{d_prior}")
    took = time.monotonic() - t0
    try:
        assert set(res) == set(range(14)), (sorted(res), err[-3000:])
        out, e = text(res, 1)
        assert not e and "h : n < m" in out and "⊢ n + 1 ≤ m" in out and "line 3" in out, out
        out, _ = text(res, 2)
        assert "before this line" in out and "after this line" in out and "no goals" in out, out
        out, _ = text(res, 3)
        assert "snippet:3" in out and "error" in out and "Proof state at each `sorry`" in out and "⊢ a + 1 ≤ b" in out, out
        out, _ = text(res, 4)
        assert out.startswith("clean:"), out
        out, _ = text(res, 5)
        assert "CLOSED by `grind`" in out and "theorem easy_succ_le (n m : Nat) (h : n < m) : n + 1 ≤ m := by\n  grind" in out, out
        out, _ = text(res, 6)
        assert "no tactic closes it" in out and "grind:" in out and "exact?:" in out, out
        out, _ = text(res, 7)
        assert out.startswith("FALSE") and "n := " in out and "kernel accepted the refutation" in out, out
        out, _ = text(res, 8)
        assert out.startswith("no counterexample"), out
        out, _ = text(res, 9)
        assert out.startswith("FALSE") and "tokens :=" in out, out             # the capacity bound fails for an over-full level
        out, e = text(res, 10)
        assert not e and out.startswith("[") and "(import ProofForgeFin" in out, out
        out, _ = text(res, 11)
        assert "refused (spec hash" in out and "used;" in out, out
        assert "`td0_step_of_adm`" in out and "`req_valid_succeeds`" in out and "Solution-with-carried.lean" in out, out
        assert "`td0_broken` (Lean error" in out and "`td0_uses_broken` (depends on a dropped declaration)" in out, out
        assert fb.MARK in out and "Still open in the current file: " in out and "`req_capacity`" in out, out
        carried = (ws / st.PRIOR_DIR / "Solution-with-carried.lean").read_text()
        assert "td0_step_of_adm" in carried and "td0_broken" not in carried and "gt_step" in carried
        out, _ = text(res, 12)
        assert "exit code 0" in out, out
        out, _ = text(res, 13)                                  # a term-mode `:= sorry` (the locked form)
        assert "not inside a tactic proof" in out and "`:= by sorry`" in out, out
        # Nothing changed the agent's file or its tracked workspace; the compiled version was recorded.
        assert (ws / "candidate/Solution.lean").read_text() == start.read_text()
        assert subprocess.run(["git", "-C", str(ws), "status", "--porcelain"], capture_output=True, text=True).stdout == ""
        assert [p.read_text() for p in rec.glob("compiled-*.lean")] == [start.read_text()]
        logged = [json.loads(l) for l in log.read_text().splitlines()]
        assert [r["tool"] for r in logged] == [m["params"]["name"] for m in msgs]
        by = {r["tool"] + str(i): r for i, r in enumerate(logged)}
        assert by["try_tactics4"]["portfolio"]["closed_by"] == "grind" and by["try_tactics5"]["portfolio"]["closed_by"] is None
        assert by["refute_statement6"]["refute"]["status"] == "false" and by["refute_statement8"]["refute"] == \
            {"name": "hard_capacity", "status": "false"}
        assert lsp_containers(pid) == [], "the persistent Lean server outlived the MCP server"
        print(f"   {len(msgs)} tool calls in {took:.0f} s")
    finally:
        for d in (ws, d_prior, d_bad, rec, start.parent):
            shutil.rmtree(d, ignore_errors=True)


def test_idle_shutdown_of_the_persistent_server():
    ws = workspace()
    s = pm.Server(ws, BUCKET.id, profile="full")
    try:
        s.session()
        s._idle.idle = 1.0
        assert "⊢ n + 1 ≤ m" in s.call("goal_at", {"name": "gt_step"})
        srv = s._session.lean_server
        assert srv.alive()
        end = time.monotonic() + 30
        while srv.alive() and time.monotonic() < end:
            time.sleep(0.5)
        assert not srv.alive(), "an idle persistent Lean server was not stopped"
        assert "⊢ n + 1 ≤ m" in s.call("goal_at", {"name": "gt_step"})   # started again on the next call
        assert srv.stats["starts"] == 2, srv.stats
    finally:
        s.cleanup()
        shutil.rmtree(ws, ignore_errors=True)


def test_resume_base_is_the_best_compiling_prior_final_file():
    broken = fb.CLEAN.replace("theorem td0_step_of_not", "theorem td0_step_of_not : Nat := \"x\"\n\ntheorem td0_unused")
    d_broken, _ = fb.prior_ledger(src=broken, name="broken")
    d_start, _ = fb.prior_ledger(src=td.FIXED_BUCKET, status={t: "SORRY" for t in BUCKET.theorems}, name="start")
    d_good, _ = fb.prior_ledger(src=fb.CLEAN, name="good")
    ws = muse_code.make_workspace(BUCKET, "alone")
    try:
        priors, _ = ledger.load_many([str(d_broken), str(d_start), str(d_good)], BUCKET)
        server = pm.Server(ws, BUCKET.id, "lean")
        base = muse_code.resume_base(server, BUCKET, ws, priors)
        assert base["run_dir"] == str(d_good.resolve()) and base["compiles"] and base["proved"] == len(BUCKET.theorems) - 1, base
        assert [c["compiles"] for c in base["candidates"]] == [False, True, True], base["candidates"]
        assert (ws / "candidate/Solution.lean").read_text() == fb.CLEAN
        assert subprocess.run(["git", "-C", str(ws), "status", "--porcelain"], capture_output=True, text=True).stdout == ""
        # A start equal to the file already in the workspace is committed as well (an empty commit).
        again = muse_code.resume_base(server, BUCKET, ws, priors)
        assert again["run_dir"] == base["run_dir"] and (ws / "candidate/Solution.lean").read_text() == fb.CLEAN
        # When none compiles, the first prior final file is the start, as it is.
        priors, _ = ledger.load_many([str(d_broken)], BUCKET)
        base = muse_code.resume_base(server, BUCKET, ws, priors)
        assert not base["compiles"] and (ws / "candidate/Solution.lean").read_text() == broken
    finally:
        for d in (ws, d_broken, d_start, d_good):
            shutil.rmtree(d, ignore_errors=True)


LEAN_TESTS = {"test_full_tools_over_stdio", "test_idle_shutdown_of_the_persistent_server",
              "test_resume_base_is_the_best_compiling_prior_final_file"}

if __name__ == "__main__":
    quick = "--quick" in sys.argv
    only = [a for a in sys.argv[1:] if not a.startswith("--")]
    for name, fn in list(globals().items()):
        if not name.startswith("test_") or (only and name not in only):
            continue
        if name in LEAN_TESTS and (quick or not td.have_lean()):
            print(f"skip  {name}")
            continue
        t0 = time.monotonic()
        fn()
        print(f"ok  {name} ({time.monotonic() - t0:.1f} s)", flush=True)
