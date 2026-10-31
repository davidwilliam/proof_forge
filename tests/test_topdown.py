"""Top-down loop of agents/repair.py (`--loop topdown`) with a scripted model; no model API calls.

The model client is replaced by a script that picks each reply by the call's purpose (structure
phase, helper dialog, phase 0), and the HTTP layer is replaced by a function that fails the test,
so nothing reaches a model API and no key is read.

Without Lean: snippet import hoisting and refusal, `open` lines in snippets, the skeleton install
rules, the dependency analysis, the tool lists of the other loops and the CLI default.
With Lean (the pinned image through the judge's container slots, one run at a time):
  * the dependency probe tells a required theorem that uses `sorry` directly from one that uses
    it only through helpers;
  * rate-limiters-bucket-b1, arm A2: phase 0 fixes the definition, the planner's first skeleton
    is rejected by the dependency check, the second is accepted with one false helper, the fill
    phase proves the shared helpers first, refutes the false one with a Lean-checked proof of its
    negation, a revised skeleton replaces it, and the judge accepts in the session;
  * rw-compound-comp, arm A1 with the library: the prover submits a skeleton that derives the
    three sequence bounds from the five per-call requirements through one reduction helper; the
    helpers are filled with pieces of tests/fixtures/library/compound_lib.lean (the reduction
    snippet imports ProofForgeFin.DeFi and opens library namespaces) and the judge accepts in the
    session.

Run: python3 tests/test_topdown.py [--quick] [name ...]   (--quick skips the Lean runs)
"""
import json, os, pathlib, re, shutil, subprocess, sys, tempfile, types
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness")]
import budget, fin_lib, judge, meta_client, repair, task as taskmod  # noqa: E402

SPARK, WONDER = "muse-spark-1.3-contributor", "muse-wonder-1.0"
BUCKET = taskmod.load("rate-limiters-bucket-b1")
COMPOUND = taskmod.load("rw-compound-comp")
FIXTURE = ROOT / "tests/fixtures/library/compound_lib.lean"
USAGE = {"prompt_tokens": 3000, "completion_tokens": 400}


def no_http(*_a, **_k):
    raise AssertionError("a model API request was attempted")


class Script:
    """Scripted model. `handlers` is a list of (purpose regex, function(purpose, messages) ->
    message dict); the first match answers. Every call is recorded."""

    def __init__(self, handlers):
        self.handlers, self.calls = handlers, []

    def __call__(self, model, messages, purpose, tools=None, **_kw):
        self.calls.append((model, purpose, [t["function"]["name"] for t in tools or []]))
        for pat, fn in self.handlers:
            if re.search(pat, purpose):
                return {"choices": [{"message": fn(purpose, messages)}], "usage": dict(USAGE), "model": model}
        raise AssertionError(f"unscripted model call: {purpose}")


def tool_call(tool, **args):
    return {"id": f"c-{tool}-{abs(hash(json.dumps(args, sort_keys=True))) % 10**8}", "type": "function",
            "function": {"name": tool, "arguments": json.dumps(args)}}


def say(text="", *calls):
    return {"content": text, **({"tool_calls": list(calls)} if calls else {})}


def turns(replies):
    """A handler that answers turn k of a dialog with replies[k] (plain text after the end)."""
    def fn(purpose, _messages):
        k = int(re.search(r":turn(\d+)$", purpose).group(1))
        return replies[k] if k < len(replies) else say("No further steps.")
    return fn


def helper_dialogs(table):
    """A handler for the obligation dialogs (`repair:<task>:d<k>:<name>:turn<n>`): table maps a
    helper name to its list of replies."""
    def fn(purpose, messages):
        m = re.search(r":d\d+:([^:]+):turn(\d+)$", purpose)
        name, k = m.group(1), int(m.group(2))
        assert name in table, f"no scripted dialog for {name}"
        replies = table[name]
        return replies[k] if k < len(replies) else say("No further steps.")
    return fn


def planner_replies(table):
    """A handler for the planner's skeleton calls (`skeleton:<task>:<round>:<try>`)."""
    def fn(purpose, _messages):
        rnd, k = map(int, re.search(r"skeleton:[^:]+:(\d+):(\d+)$", purpose).groups())
        return say(table[rnd][k])
    return fn


def lean_block(prose, code):
    return f"{prose}\n\n```lean\n{code.strip()}\n```\n"


def session(task, start=None, library=False, cap=None):
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-topdown-"))
    return repair.Session(task, SPARK, start or task.start, out, budget.Budget(cap, None), library=library)


def close(s):
    shutil.rmtree(s.ws, ignore_errors=True)
    shutil.rmtree(s.out, ignore_errors=True)


def have_lean():
    if judge.IN_IMAGE:
        return True
    return subprocess.run(["docker", "image", "inspect", judge.IMAGE], capture_output=True).returncode == 0


def events(out):
    return [json.loads(l) for l in (pathlib.Path(out) / "events.jsonl").read_text().splitlines()]


# Without Lean

def test_snippet_imports_are_hoisted_or_refused():
    s = session(BUCKET)
    try:
        src = s._source()
        s.library = True
        code, hoist, refusal = s._snippet_imports("import ProofForgeFin.Rounding\ntheorem a : True := trivial", src)
        assert refusal is None and hoist == ["ProofForgeFin.Rounding"], (hoist, refusal)
        assert code.split("\n")[0] == "" and code.count("\n") == 1   # line numbers kept
        code, hoist, refusal = s._snippet_imports("import TokenBucket.Spec\ntheorem a : True := trivial", src)
        assert refusal is None and hoist == []                         # already imported: dropped
        _, hoist, refusal = s._snippet_imports("import Std.Data.HashMap\ntheorem a : True := trivial", src)
        assert refusal and "`import Std.Data.HashMap` refused" in refusal and "only ProofForgeFin modules" in refusal
        _, _, refusal = s._snippet_imports("import ProofForgeFin.NoSuchModule", src)
        assert refusal and "NoSuchModule" in refusal
        s.library = False
        _, _, refusal = s._snippet_imports("import ProofForgeFin.Rounding", src)
        assert refusal and "library is not available" in refusal
        assert s.try_snippet("import Lean\ntheorem a : True := trivial").startswith("error: not compiled")
        assert any(e["kind"] == "snippet_import" and e["refused"] for e in s.events)
    finally:
        close(s)


def test_snippet_open_lines_scope_the_later_declarations():
    s = session(BUCKET)
    try:
        code = ("theorem first : True := trivial\n"
                "open ProofForgeFin ProofForgeFin.Seq\n"
                "/-- doc\n  more -/\n"
                "@[simp]\n"
                "theorem a : True := trivial\n"
                "open Nat in theorem b : True := trivial\n"
                "def c : Nat := 1")
        out = s._snippet_opens(code).split("\n")
        assert len(out) == len(code.split("\n"))
        assert out[0] == "theorem first : True := trivial" and out[1] == ""
        assert out[2] == "/- doc" and out[4] == ""
        assert out[5] == "open ProofForgeFin ProofForgeFin.Seq in @[simp] theorem a : True := trivial"
        assert out[6] == "open Nat in theorem b : True := trivial"
        assert out[7] == "open ProofForgeFin ProofForgeFin.Seq in def c : Nat := 1"
        # The declaration tools see through the prefix.
        assert [n for n, _ in s._chunks("\n".join(out))] == ["first", "a", "b", "c"]
        src = s._source().replace(f"end {BUCKET.ns}", "open Foo in theorem helper_x : True := by sorry\n\nend " + BUCKET.ns)
        assert repair.decl_text(s, "helper_x", src).startswith("open Foo in theorem helper_x")
        new, action = s._replace_in(src, "helper_x", "theorem helper_x : True := trivial")
        assert action == "replaced" and "open Foo in" not in new and "theorem helper_x : True := trivial" in new
    finally:
        close(s)


SKELETON_BUCKET = """
theorem td0_step_of_adm {s : State} {r : Request} (h : Admissible s r) :
    step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by sorry

theorem td0_step_of_not {s : State} {r : Request} (h : ¬ Admissible s r) :
    step s r = (.rejected, s) := by sorry

theorem td0_adm_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : Admissible s r := by sorry

theorem td0_capacity_step (s : State) (r : Request) :
    (step s r).2.tokens ≤ (step s r).2.capacity := by sorry

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [td0_step_of_adm h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact td0_step_of_not h

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r ht hc
  constructor
  · intro h; exact (td0_adm_of_ok h).2.2
  · intro h; rw [td0_step_of_adm ⟨ht, hc, h⟩]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases hv : Admissible s r
  · rw [td0_step_of_adm hv]; exact ⟨hv.1, fun _ => rfl⟩
  · rw [td0_step_of_not hv]; exact ⟨Nat.le_refl _, fun h => by cases h⟩

theorem req_remaining : Remaining step := by
  intro s r h
  have hv := td0_adm_of_ok h
  rw [td0_step_of_adm hv]
  show refilled s r.time - r.cost + r.cost = refilled s r.time
  have := hv.2.2
  omega

theorem req_effects : Effects step := by
  intro s r h
  have hv := td0_adm_of_ok h
  rw [td0_step_of_adm hv]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem req_capacity : CapacityBound step := by
  intro s r _
  exact td0_capacity_step s r
"""

FIXED_BUCKET = """import TokenBucket.Spec

namespace TokenBucket

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance

def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_valid_succeeds       : ValidSucceeds step := sorry
theorem req_invalid_noop         : InvalidNoop step := sorry
theorem req_allow_iff_sufficient : AllowIffSufficient step := sorry
theorem req_time_monotone        : TimeMonotone step := sorry
theorem req_remaining            : Remaining step := sorry
theorem req_effects              : Effects step := sorry
theorem req_capacity             : CapacityBound step := sorry

end TokenBucket
"""


def fixed_start():
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-topdown-start-"))
    (d / "Solution.lean").write_text(FIXED_BUCKET)
    return d / "Solution.lean"


def test_install_skeleton_rules():
    s = session(BUCKET, start=fixed_start())
    try:
        status = {t: "SORRY" for t in BUCKET.theorems}
        src, info, problems = repair.install_skeleton(s, f"namespace TokenBucket\n{SKELETON_BUCKET}\nend TokenBucket", status)
        assert problems == [], problems
        assert info["derived"] == BUCKET.theorems and info["helpers"] == [
            "td0_step_of_adm", "td0_step_of_not", "td0_adm_of_ok", "td0_capacity_step"], info
        # The locked statement header is kept, the skeleton's proof is installed.
        decl = repair.decl_text(s, "req_invalid_noop", src)
        assert decl.startswith("theorem req_invalid_noop         : InvalidNoop step := by") and "td0_step_of_not h" in decl
        # A proved required theorem keeps its proof.
        status2 = dict(status, req_invalid_noop="PROVED")
        _, info2, _ = repair.install_skeleton(s, SKELETON_BUCKET, status2)
        assert "req_invalid_noop" not in info2["derived"] and any("already proved" in n for n in info2["notes"])
        # Scoping commands, open definitions, changed required definitions and missing derivations.
        bad = ("section S\nvariable (n : Nat)\ndef d0 : Nat := sorry\n"
               "def step : Impl := fun s _ => (.ok, s)\ntheorem td0_x : True := by sorry\n"
               "theorem req_valid_succeeds : ValidSucceeds step := by sorry\nend S")
        _, _, problems = repair.install_skeleton(s, bad, status)
        text = "\n".join(problems)
        assert "`section S` is not supported" in text and "`variable (n : Nat)` is not supported" in text, text
        assert "`d0` is a def with `sorry`" in text and "`step` is a required definition" in text, text
        assert "`req_invalid_noop` is not derived" in text and "`req_valid_succeeds` is not derived" not in text, text
        # Imports in a skeleton follow the snippet rule.
        s.library = True
        src3, info3, problems3 = repair.install_skeleton(s, "import ProofForgeFin.Rounding\n" + SKELETON_BUCKET, status)
        assert not problems3 and info3["hoisted"] == ["ProofForgeFin.Rounding"]
        assert src3.split("\n")[:2] == ["import TokenBucket.Spec", "import ProofForgeFin.Rounding"]
    finally:
        close(s)


def test_dependency_analysis():
    s = types.SimpleNamespace(ns="N", theorems=["r1", "r2", "r3"])
    g = {"N.r1": {"kind": "theorem", "sorry": False, "deps": {"N.h1", "N.d"}},
         "N.r2": {"kind": "theorem", "sorry": False, "deps": {"N.h1", "N.h2", "N.r1"}},
         "N.r3": {"kind": "theorem", "sorry": True, "deps": set()},
         "N.h1": {"kind": "theorem", "sorry": False, "deps": {"N.h3"}},
         "N.h2": {"kind": "theorem", "sorry": True, "deps": set()},
         "N.h3": {"kind": "theorem", "sorry": True, "deps": set()},
         "N.d": {"kind": "def", "sorry": False, "deps": set()}}
    an = repair.analyze(s, g)
    assert an["direct"] == ["r3"] and an["missing"] == [] and an["proved"] == []
    assert an["open"] == {"N.h3": ["r1", "r2"], "N.h2": ["r2"]}, an["open"]
    # An open helper that only another open helper's (sorry) proof was meant to use is unreached.
    g["N.h4"] = {"kind": "theorem", "sorry": True, "deps": set()}
    assert repair.unreached_open(g, ["N.r1", "N.r2", "N.r3"], ["h1", "h2", "h3", "h4", "d"]) == ["h4"]
    assert repair.unreached_open(g, ["N.h1"], ["h2", "h3"]) == ["h2"]
    del g["N.h4"]
    g["N.h3"]["sorry"] = False
    an = repair.analyze(s, g)
    assert an["proved"] == ["r1"] and an["open"] == {"N.h2": ["r2"]}
    names = {"N.foo", "N.foo.proof_1", "N.foo.match_2", "N.bar._unfold", "N.bar", "N.S.mk"}
    assert repair.aux_owner("N.foo.proof_1", names) == "N.foo"
    assert repair.aux_owner("N.foo.match_2", names) == "N.foo"
    assert repair.aux_owner("N.bar._unfold", names) == "N.bar"
    assert repair.aux_owner("N.S.mk", names) == "N.S.mk"
    assert repair.short_name("_private.Solution.0.N.adm_of_ok") == "adm_of_ok"


def test_other_loops_are_unchanged():
    ap = repair.parser()
    a = ap.parse_args([])
    assert a.loop == "orchestrated"
    assert ap.parse_args(["--loop", "topdown"]).loop == "topdown"
    for lib in (False, True):
        names = [t["function"]["name"] for t in repair.tools_for(BUCKET, lib)]
        assert "submit_skeleton" not in names and "refute_helper" not in names
        assert {"submit_skeleton", "refute_helper"} <= {t["function"]["name"] for t in repair.tools_for(BUCKET, lib, True)}
    s = session(BUCKET)
    try:
        assert s.refuted == {} and s.extra_tools == set()
    finally:
        close(s)


def test_library_prompt_mentions_reduction_theorems():
    on = types.SimpleNamespace(task=BUCKET, mode="repair", library=True, lib_index=fin_lib.Index.load())
    text = repair.system_prompt(on)
    assert "Reduction theorems:" in text and "per-step or per-call hypotheses" in text
    assert "Reduction theorems:" in repair.library_brief(on.lib_index, tools=False)
    general = repair.REDUCTION_NOTE + repair.TOPDOWN_GUIDANCE + repair.REDUCTION_QUERY + repair.SKELETON_SYSTEM
    for task_word in ("compound", "comp ", "comptroller", "bucket", "payout", "rw-", "knight", "balancer"):
        assert task_word not in general.lower(), task_word


def test_compact_view_and_reading_one_declaration():
    s = session(BUCKET, start=fixed_start())
    try:
        proved = ("theorem td0_long (n : Nat) : n + 0 = n := by\n  have h : n + 0 = n := by\n    simp\n"
                  "  exact h\n")
        src = s._source().replace("end TokenBucket", proved + "\ntheorem td0_short (n : Nat) : n = n := rfl\n\n"
                                  "theorem td0_open (n : Nat) : 0 + n = n := by\n  sorry\n\nend TokenBucket")
        s._save(src, "fixture")
        src = s._source()
        view = repair.compact_view(s)
        assert "theorem td0_long (n : Nat) : n + 0 = n := by\n  ...  -- proved (4 lines)" in view, view
        assert "simp" not in view and "td0_short (n : Nat) : n = n := rfl" in view
        assert "theorem td0_open (n : Nat) : 0 + n = n := by\n  sorry" in view
        assert "read_file with `name`" in view and view.index("read_file with") > view.index("namespace TokenBucket")
        assert "simp" in repair.compact_view(s, keep={"td0_long"})
        assert s._source() == src                                  # the view never changes the file
        # read_file: the full file outside the top-down loop; the view and one declaration in it.
        assert s.read_file("candidate/Solution.lean") == src
        s.topdown = True
        assert s.read_file("candidate/Solution.lean") == view
        assert s.read_file("candidate/Solution.lean", name="td0_long").startswith("theorem td0_long") and \
            "simp" in s.read_file("", name="TokenBucket.td0_long")
        assert s.read_file("", name="nope").startswith("error: no declaration `nope`")
        tools = {t["function"]["name"]: t["function"] for t in repair.tools_for(BUCKET, True, True, compact=True)}
        assert "name" in tools["read_file"]["parameters"]["properties"]
        assert tools["search_library"]["parameters"]["properties"]["limit"]["maximum"] == repair.SEARCH_MAX_TOPDOWN
        plain = {t["function"]["name"]: t["function"] for t in repair.tools_for(BUCKET, True, True)}
        assert "name" not in plain["read_file"]["parameters"]["properties"]
        s.library, s.lib_index = True, fin_lib.Index.load()
        hits = s.search_library("rounding down a sum of parts", limit=25)
        assert hits.count("\n[") + 1 <= repair.SEARCH_MAX_TOPDOWN, hits
    finally:
        close(s)


# With Lean

def test_dependency_probe_separates_direct_and_helper_sorry():
    s = session(BUCKET, start=fixed_start())
    try:
        src, _, problems = repair.install_skeleton(s, SKELETON_BUCKET.replace(
            "intro s r h; exact td0_step_of_not h", "intro s r h; sorry"), {t: "SORRY" for t in BUCKET.theorems})
        assert not problems, problems
        s._save(src, "fixture")
        graph, err = s.dep_graph()
        assert graph is not None, err
        an = repair.analyze(s, graph)
        assert an["direct"] == ["req_invalid_noop"], an["direct"]
        opens = {repair.short_name(n): u for n, u in an["open"].items()}
        assert opens["td0_step_of_adm"] == ["req_valid_succeeds", "req_allow_iff_sufficient", "req_time_monotone",
                                            "req_remaining", "req_effects"], opens
        assert opens["td0_capacity_step"] == ["req_capacity"]
        assert graph["TokenBucket.step"]["kind"] == "def" and not graph["TokenBucket.step"]["sorry"]
    finally:
        close(s)


def test_linter_warnings_do_not_block_a_snippet_in_topdown():
    s = session(BUCKET)
    try:
        lint = "theorem lint_a (n : Nat) (h : n = n) : n + 0 = n := by simp"
        clean, msgs, _ = s._scratch(lint)
        assert not clean and "not explicitly referenced" in "\n".join(msgs)   # other loops: unchanged
        s.topdown = True
        assert s._scratch(lint)[0]
        assert not s._scratch("theorem lint_b (n : Nat) : n + 0 = n := by sorry")[0]
        assert not s._scratch("theorem lint_c (n : Nat) (h : n = n) : n + 1 = n := by simp")[0]
        out = s.try_snippet(lint)
        assert out.startswith("snippet compiles with no errors (linter warnings only)") and "lint_a" in out, out
    finally:
        close(s)


REFUTATION = """by
  intro h
  have := h ⟨1, 0, 5, 0⟩ ⟨0, 0⟩
  revert this
  decide"""

HELPER_PROOFS_BUCKET = {
    "td0_step_of_adm": [
        say("Try with an extra import first.", tool_call("try_snippet", code=(
            "import Std.Data.HashMap\n"
            "theorem td0_step_of_adm {s : State} {r : Request} (h : Admissible s r) :\n"
            "    step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by\n"
            "  simp [step, h]"))),
        say("Without the import.", tool_call("try_snippet", code=(
            "theorem td0_step_of_adm {s : State} {r : Request} (h : Admissible s r) :\n"
            "    step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by\n"
            "  simp [step, h]")))],
    "td0_adm_of_ok": [say("", tool_call("try_snippet", code=(
        "theorem td0_adm_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : Admissible s r := by\n"
        "  by_cases hv : Admissible s r\n"
        "  · exact hv\n"
        "  · rw [td0_step_of_not hv] at h; cases h")))],
    "td0_step_of_not": [say("", tool_call("try_snippet", code=(
        "theorem td0_step_of_not {s : State} {r : Request} (h : ¬ Admissible s r) :\n"
        "    step s r = (.rejected, s) := by\n"
        "  simp [step, h]")))],
    "td0_capacity_step": [say("A rejected request keeps an over-full level, so this is false.",
                              tool_call("refute_helper", name="td0_capacity_step", proof=REFUTATION))],
    "td1_capacity_step": [say("", tool_call("try_snippet", code=(
        "theorem td1_capacity_step (s : State) (r : Request) (hs : s.tokens ≤ s.capacity) :\n"
        "    (step s r).2.tokens ≤ (step s r).2.capacity := by\n"
        "  by_cases hv : Admissible s r\n"
        "  · rw [td0_step_of_adm hv]\n"
        "    show refilled s r.time - r.cost ≤ s.capacity\n"
        "    have : refilled s r.time ≤ s.capacity := Nat.min_le_left _ _\n"
        "    omega\n"
        "  · rw [td0_step_of_not hv]; exact hs")))],
}

SKELETON_BUCKET_1 = """
theorem td1_capacity_step (s : State) (r : Request) (hs : s.tokens ≤ s.capacity) :
    (step s r).2.tokens ≤ (step s r).2.capacity := by sorry

theorem req_capacity : CapacityBound step := by
  intro s r hs
  exact td1_capacity_step s r hs
"""


def run_main(argv, script, extra_patches=()):
    with patch.object(repair, "chat", script), patch.object(meta_client, "_attempt", no_http), \
            patch.object(repair.Session, "pause", lambda self, seconds: None):
        for p in extra_patches:
            p.start()
        try:
            with patch.object(sys, "argv", ["repair.py"] + argv):
                repair.main()
        finally:
            for p in extra_patches:
                p.stop()


def test_bucket_a2_skeleton_refutation_and_restructure_reach_verified():
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-topdown-bucket-"))
    # The first skeleton has a direct sorry and an open helper that no proof uses.
    bad = SKELETON_BUCKET.replace("intro s r h; exact td0_step_of_not h", "intro s r h; sorry") + (
        "\ntheorem td0_unused_step (s : State) (r : Request) : (step s r).2.capacity = s.capacity := by sorry\n")
    script = Script([
        (r":implement:turn\d+$", turns([say("Fix the cap and the cost bound.",
                                            tool_call("write_solution", content=FIXED_BUCKET), tool_call("run_tests"))])),
        (r"^skeleton:", planner_replies({
            0: [lean_block("Three facts about one step carry every requirement.", bad),
                lean_block("Move the remaining step of the invalid case into td0_step_of_not.", SKELETON_BUCKET)],
            1: [lean_block("The capacity bound needs the hypothesis that the level starts within capacity.",
                           SKELETON_BUCKET_1)]})),
        (r":d\d+:[^:]+:turn\d+$", helper_dialogs(HELPER_PROOFS_BUCKET)),
    ])
    run_main(["--task", BUCKET.id, "--loop", "topdown", "--model", SPARK, "--planner", WONDER,
              "--budget-usd", "5", "--out", str(out)], script)
    summary = json.loads((out / "summary.json").read_text())
    ev = events(out)
    kinds = [e["kind"] for e in ev]
    assert summary["accepted_in_session"] is True, summary
    assert set(summary["final_status"].values()) == {"PROVED"}, summary["final_status"]
    assert summary["mode"] == "topdown" and summary["budget"]["stop"] is None
    sk = [e for e in ev if e["kind"] == "skeleton"]
    assert [(e["round"], e["accepted"]) for e in sk] == [(0, False), (0, True), (1, True)], sk
    assert "req_invalid_noop` uses `sorry` in its own proof" in sk[0]["problems"]
    assert "`td0_unused_step` is left open (`sorry`) but no required theorem uses it" in sk[0]["problems"]
    assert sk[1]["helpers"]["td0_step_of_adm"] == ["req_valid_succeeds", "req_allow_iff_sufficient",
                                                   "req_time_monotone", "req_remaining", "req_effects"]
    order = [h["name"] for h in next(e for e in ev if e["kind"] == "fill_order")["order"]]
    assert order == ["td0_step_of_adm", "td0_adm_of_ok", "td0_step_of_not", "td0_capacity_step"], order
    assert any(e["kind"] == "refute" and e["ok"] and e["name"] == "td0_capacity_step" for e in ev)
    rs = next(e for e in ev if e["kind"] == "restructure")
    assert rs["refuted"] == ["td0_capacity_step"]
    assert any(e["kind"] == "snippet_import" and e.get("refused") for e in ev)
    assert any(e["kind"] == "judge" and e["accepted"] for e in ev)
    assert "pass1" not in {e.get("label", "").split(":")[0] for e in ev if e["kind"] == "turn"}
    assert kinds.index("restructure") < max(i for i, k in enumerate(kinds) if k == "skeleton")
    final = (out / "final.lean").read_text()
    assert "td0_capacity_step" not in final and "td1_capacity_step" in final and "sorry" not in final
    by_model = summary["budget"]["by_model"]
    assert by_model[WONDER]["calls"] == 3 and by_model[SPARK]["calls"] >= 6, by_model
    assert not any(p.startswith("plan:") for _, p, _ in script.calls)
    print(f"   bucket: {len(script.calls)} scripted calls, {summary['versions']} versions, "
          f"{summary['budget']['elapsed_s']} s")
    shutil.rmtree(out, ignore_errors=True)


# rw-compound-comp from pieces of the library fixture

def fixture_parts():
    """The fixture split at its section markers: the per-call part before the transcription of the
    deployed code, the transcription (the implementation), the per-call part after it, and the
    library section (`namespace Lib`)."""
    text = FIXTURE.read_text()
    body = text.split("namespace CompRewards\n", 1)[1]
    impl_at = body.index("/-! ## The shipped fix")
    after_impl = body.index("/-! ### The transcription computes")
    lib_at = body.index("namespace Lib\n")
    lib_end = body.index("end Lib\n")
    return {"percall_a": body[:impl_at], "impl": body[impl_at:after_impl],
            "percall_b": body[after_impl:lib_at], "lib": body[lib_at + len("namespace Lib\n"):lib_end]}


# Declarations of the library section whose names the per-call part also declares.
RENAMED = ["distS", "distB", "supplyNext", "borrowNext", "speedsNext", "claim_eq", "speeds_eq"]


def flatten_lib(lib):
    """The fixture's library section as top-level declarations, the way a model would write them
    in a snippet: no nested namespace, every section variable an explicit binder of each
    declaration in the section, names shared with the per-call part prefixed with `L_`."""
    lib = lib.replace("CompRewards.Lib.", "")
    for n in RENAMED:
        lib = re.sub(rf"(?<![\w.']){re.escape(n)}(?![\w'])", f"L_{n}", lib)
    out, binders, var = [], None, None
    for line in lib.split("\n"):
        if line.startswith("section "):
            binders = ""
            continue
        if line.startswith("end ") and binders is not None:
            binders = None
            continue
        if line.startswith("variable "):
            var = line[len("variable "):].strip()
            continue
        if var is not None:
            if line.startswith("  ") and not line.startswith("include"):
                var += " " + line.strip()
                continue
            binders, var = var, None
        if line.startswith("include "):
            continue
        if binders:
            m = re.match(rf"^({repair.DECL_PREFIX}{repair.DECL_KINDS}\s+[^\s:({{\[]+)(.*)$", line)
            if m:
                line = f"{m.group(1)} {binders}{m.group(2)}"
        out.append(line)
    return "\n".join(out)


def compound_start():
    parts = fixture_parts()
    reqs = re.findall(r"^theorem\s+(\S+)\s*:\s*([^\n]+?)\s*:=\s*sorry", (COMPOUND.root / COMPOUND.spec_dir / "Challenge.lean").read_text(), re.M)
    text = ("import CompRewards.Spec\n\nnamespace CompRewards\n\n" + parts["impl"].rstrip() + "\n\n"
            + "\n".join(f"theorem {n} : {t} := sorry" for n, t in reqs) + "\n\nend CompRewards\n")
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-topdown-start-"))
    (d / "Solution.lean").write_text(text)
    return d / "Solution.lean"


PER_CALL = [("td0_calls_succeed", "CallsSucceed", "spec_calls_succeed"),
            ("td0_supply_hook", "SupplyHookEffects", "spec_supply_hook"),
            ("td0_borrow_hook", "BorrowHookEffects", "spec_borrow_hook"),
            ("td0_claim", "ClaimEffects", "spec_claim"),
            ("td0_set_speeds", "SetSpeedsEffects", "spec_set_speeds")]
CALL_HYPS = ("{impl : Impl} (hOK : CallsSucceed impl) (hS : SupplyHookEffects impl) (hB : BorrowHookEffects impl) "
             "(hC : ClaimEffects impl) (hP : SetSpeedsEffects impl)")
ARGS = "req_calls_succeed req_supply_hook req_borrow_hook req_claim req_set_speeds"


def compound_skeleton(direct_sorry=False):
    helpers = "\n\n".join(f"theorem {n} : {p} comptroller := by sorry" for n, p, _ in PER_CALL)
    derive = "\n".join(f"theorem {r} : {p} comptroller := {n}"
                       for (n, p, _), r in zip(PER_CALL, COMPOUND.theorems[:5]))
    bound = "sorry" if direct_sorry else f"(td0_bounds_of_calls {ARGS}).1"
    return f"""
{helpers}

theorem td0_bounds_of_calls {CALL_HYPS} :
    RewardsBounded impl ∧ AccountBounded impl ∧ NoBackdatedRewards impl := by sorry

{derive}
theorem req_rewards_bounded : RewardsBounded comptroller := {bound}
theorem req_account_bounded : AccountBounded comptroller := (td0_bounds_of_calls {ARGS}).2.1
theorem req_no_backdated : NoBackdatedRewards comptroller := (td0_bounds_of_calls {ARGS}).2.2
"""


def compound_helper_dialogs():
    parts = fixture_parts()
    state = {"percall": False}
    lib_snippet = ("import ProofForgeFin.DeFi\n" + flatten_lib(parts["lib"]) + "\n\n"
                   f"theorem td0_bounds_of_calls {CALL_HYPS} :\n"
                   "    RewardsBounded impl ∧ AccountBounded impl ∧ NoBackdatedRewards impl :=\n"
                   "  ⟨rewards_bounded hOK hS hB hC hP, account_bounded hOK hS hB hC hP, no_backdated hOK hS hB hC hP⟩\n")

    def fn(purpose, _messages):
        m = re.search(r":d\d+:([^:]+):turn(\d+)$", purpose)
        name, k = m.group(1), int(m.group(2))
        if k > 0:
            return say("No further steps.")
        if name == "td0_bounds_of_calls":
            return say("The library's potential argument gives the three bounds from the per-call facts.",
                       tool_call("search_library", query="bound for every sequence of operations via a potential"),
                       tool_call("try_snippet", code=lib_snippet))
        spec = {n: (p, sp) for n, p, sp in PER_CALL}[name]
        thm = f"theorem {name} : {spec[0]} comptroller := by rw [comptroller_eq]; exact {spec[1]}\n"
        if not state["percall"]:
            state["percall"] = True
            return say("The transcription computes the specification-shaped implementation.",
                       tool_call("try_snippet", code=parts["percall_a"] + parts["percall_b"] + "\n" + thm))
        return say("", tool_call("try_snippet", code=thm))
    return fn


def test_compound_a1_library_reduction_reaches_verified():
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-topdown-compound-"))
    start = compound_start()
    script = Script([
        (r":structure0:turn\d+$", turns([
            say("A first skeleton.", tool_call("search_library", query="every sequence of operations per-step reduction"),
                tool_call("submit_skeleton", code=compound_skeleton(direct_sorry=True))),
            say("The bounds go through one reduction helper.", tool_call("submit_skeleton", code=compound_skeleton()))])),
        (r":d\d+:[^:]+:turn\d+$", compound_helper_dialogs()),
    ])
    passing = '{"status": "PASS", "violations": {}, "examples": []}'
    run_main(["--task", COMPOUND.id, "--loop", "topdown", "--model", SPARK, "--planner", "none",
              "--budget-usd", "5", "--start", str(start), "--out", str(out)], script,
             # Phase 0's binary check is covered by the bucket test; the start already implements the fix.
             [patch.object(repair.Session, "run_tests", lambda self: passing)])
    summary = json.loads((out / "summary.json").read_text())
    ev = events(out)
    assert summary["accepted_in_session"] is True, summary
    assert set(summary["final_status"].values()) == {"PROVED"}, summary["final_status"]
    sk = [e for e in ev if e["kind"] == "skeleton"]
    assert [(e["source"], e["accepted"]) for e in sk] == [("prover", False), ("prover", True)], sk
    assert "`req_rewards_bounded` uses `sorry` in its own proof" in sk[0]["problems"]
    users = sk[1]["helpers"]
    assert users["td0_bounds_of_calls"] == ["req_rewards_bounded", "req_account_bounded", "req_no_backdated"]
    assert all(len(users[n]) == 4 for n, _, _ in PER_CALL), users
    order = [h["name"] for h in next(e for e in ev if e["kind"] == "fill_order")["order"]]
    assert order[-1] == "td0_bounds_of_calls" and set(order[:5]) == {n for n, _, _ in PER_CALL}, order
    assert any(e["kind"] == "snippet_import" and e.get("added") and e["module"] == "ProofForgeFin.DeFi" for e in ev)
    assert any(e["kind"] == "judge" and e["accepted"] for e in ev)
    final = (out / "final.lean").read_text()
    assert "import ProofForgeFin.DeFi" in final and "open ProofForgeFin ProofForgeFin.DeFi.Rewards in" in final
    assert summary["budget"]["by_model"][SPARK]["calls"] >= 8 and WONDER not in summary["budget"]["by_model"]
    print(f"   compound: {len(script.calls)} scripted calls, {summary['versions']} versions, "
          f"{summary['budget']['elapsed_s']} s")
    shutil.rmtree(out, ignore_errors=True)


LEAN = {"test_dependency_probe_separates_direct_and_helper_sorry",
        "test_linter_warnings_do_not_block_a_snippet_in_topdown",
        "test_bucket_a2_skeleton_refutation_and_restructure_reach_verified",
        "test_compound_a1_library_reduction_reaches_verified"}

def limit_lean_threads(threads):
    """Every Lean run of the tests uses at most `threads` threads (the machine is shared)."""
    orig = judge.in_container

    def run(project, script, timeout=900):
        return orig(project, f"export LEAN_NUM_THREADS={threads}; {script}", timeout=timeout)
    judge.in_container = run


if __name__ == "__main__":
    limit_lean_threads(int(os.environ.get("LEAN_NUM_THREADS", "4")))
    quick = "--quick" in sys.argv
    only = [x for x in sys.argv[1:] if not x.startswith("--")]
    lean = have_lean()
    for name, fn in list(globals().items()):
        if not name.startswith("test_") or (only and name not in only):
            continue
        if name in LEAN and (quick or not lean):
            print(f"skip {name}")
            continue
        fn()
        print(f"ok  {name}")
