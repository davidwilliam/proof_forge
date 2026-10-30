"""Harness phase 2 and selection: the joint proof architecture, the compact prompt view,
notes kept across dialogs, unused-helper removal and best-version selection.

The pure tests need no model and no Lean. The tests marked with `lean` compile in the
pinned image and are skipped without Docker. Model calls are replaced by fixed replies.
Run: python3 tests/test_harness_architecture.py
"""
import argparse, pathlib, shutil, subprocess, sys, tempfile
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "agents")]
import judge, repair, task as taskmod  # noqa: E402

TASK = taskmod.load()   # the payout flagship
EVIDENCE = ROOT / "formal/evidence/muse-repair-002/Solution.lean"


def have_lean():
    if judge.IN_IMAGE:
        return True
    r = subprocess.run(["docker", "image", "inspect", judge.IMAGE], capture_output=True)
    return r.returncode == 0


def session(start=None):
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-arch-"))
    return repair.Session(TASK, "none", start or TASK.start, out)


def close(s):
    shutil.rmtree(s.ws, ignore_errors=True)
    shutil.rmtree(s.out, ignore_errors=True)


def args(**kw):
    base = dict(model="muse-spark-1.3-contributor", planner="none", architect="auto", planner_effort="high",
                effort="medium", max_depth=2, obligation_turns=12, pass1_turns=8, rounds=3)
    base.update(kw)
    return argparse.Namespace(**base)


def reply(text):
    return {"choices": [{"message": {"content": text}}]}, {}


SKELETON = """Plan: one helper carries the statement.

```lean
/-- the shared fact -/
theorem arch0_core : Conserves step := by sorry

theorem req_conservation : Conserves step := by
  exact arch0_core

end Payout
```"""


def test_split_decls_drops_comments_and_namespace_lines():
    s = session()
    try:
        code = ("namespace Payout\n/-- doc -/\n@[simp]\ntheorem a : True := trivial\n\n-- note\ndef b : Nat := 1\n"
                "/- block\ncomment -/\ntheorem c : b = 1 := rfl\nend Payout\n")
        got = repair.split_decls(s, code)
        assert [n for n, _ in got] == ["a", "b", "c"], got
        assert got[0][1].startswith("@[simp]\ntheorem a"), got[0]
        assert all("end Payout" not in t and "doc" not in t and "block" not in t for _, t in got), got
    finally:
        close(s)


def test_install_keeps_the_locked_statement_and_appends_helpers():
    s = session()
    try:
        code = ("theorem arch0_core : Conserves step := by sorry\n\n"
                "theorem req_conservation : ∀ x, x = x := by\n  exact arch0_core\n")
        status = {t: "SORRY" for t in TASK.theorems}
        src, helpers, derived = repair.install_architecture(s, code, status)
        assert helpers == ["arch0_core"] and derived == ["req_conservation"], (helpers, derived)
        decl = repair.decl_text(s, "req_conservation", src)
        assert decl.startswith("theorem req_conservation   : Conserves step := by"), decl
        assert "exact arch0_core" in decl
        assert src.index("arch0_core") < src.index("end Payout")
    finally:
        close(s)


def test_install_keeps_proved_declarations():
    s = session()
    try:
        s._save(s._source().replace("end Payout", "theorem h1 : 1 = 1 := rfl\n\ntheorem h2 : 2 = 2 := by sorry\n\nend Payout"), "fixture")
        status = {t: "SORRY" for t in TASK.theorems}
        status["req_conservation"] = "PROVED"
        code = ("theorem h1 : 1 = 1 := by sorry\n\ntheorem h2 : 2 = 2 := rfl\n\n"
                "theorem req_conservation : Conserves step := by\n  exact h1\n")
        src, helpers, derived = repair.install_architecture(s, code, status)
        assert repair.decl_text(s, "h1", src).strip() == "theorem h1 : 1 = 1 := rfl", src
        assert "sorry" not in repair.decl_text(s, "h2", src)
        assert derived == [] and "exact h1" not in src
    finally:
        close(s)


def test_outline_hides_only_proofs_of_proved_theorems():
    s = session()
    try:
        s._save(s._source().replace("end Payout",
                                    "theorem h1 : 1 = 1 := by\n  rfl\n\ntheorem h2 : 2 = 2 := by\n  sorry\n\nend Payout"), "fixture")
        view = repair.outline(s)
        assert "theorem h1 : 1 = 1 := by\n  -- proved; proof omitted here" in view and "  rfl" not in view, view
        assert "theorem h2 : 2 = 2 := by\n  sorry" in view
        assert "def step" in view and "fun s r" in view
        assert "  rfl" in repair.outline(s, {"h1"})
    finally:
        close(s)


def test_notes_keep_the_end_of_a_failed_dialog():
    s = session()
    try:
        msgs = [{"role": "assistant", "content": "trying induction on the list"},
                {"role": "tool", "content": "snippet:3:2: error: unsolved goals"},
                {"role": "assistant", "content": ""}]
        repair.remember(s, "h", msgs)
        repair.remember(s, "h", msgs)
        repair.remember(s, "h", [{"role": "assistant", "content": "third"}])
        assert len(s.notes["h"]) == 2 and s.notes["h"][-1] == "third"
        assert "unsolved goals" in s.notes["h"][0] and "induction" in s.notes["h"][0]
        assert repair.notes_text(s, "h").startswith("- trying induction")
    finally:
        close(s)


def test_resolve_attempts_a_shared_helper_once_per_round():
    s = session()
    calls = []
    try:
        s._save(s._source().replace("end Payout", "theorem shared : 1 = 1 := by sorry\n\nend Payout"), "fixture")
        for t in ("req_effects", "req_conservation"):
            s._save(repair.Session._replace_in(s, s._source(), t, f"theorem {t} : True := by\n  exact (shared ▸ trivial)")[0], "fixture")
        with patch.object(repair, "prove_target", lambda s_, a_, sy, sp, t, b, lab, pt="": calls.append(t) or False), \
                patch.object(repair.Session, "check_status", lambda self, names=None: {n: "SORRY" for n in (names or TASK.theorems)}):
            s.tried = set()
            repair.resolve(s, args(), "", "", "req_effects", 0)
            repair.resolve(s, args(), "", "", "req_conservation", 0)
        assert calls == ["shared"], calls
    finally:
        close(s)


def test_architect_reverts_code_that_does_not_compile_and_keeps_a_fix():
    if not have_lean():
        print("skip (no Lean image)")
        return
    s = session()
    replies = [reply("```lean\ntheorem arch0_core : Conserves step ∧ (1 : Nat) = true := by sorry\n```"), reply(SKELETON)]
    try:
        with patch.object(repair.Session, "call", lambda self, *x, **k: replies.pop(0)):
            helpers, derived = repair.architect(s, args(), repair.spec_text(s), ["req_conservation"], 0)
        assert helpers == ["arch0_core"] and derived == ["req_conservation"], (helpers, derived)
        assert "arch0_core" in s.targets
        whys = [e["why"] for e in s.events if e["kind"] == "write"]
        assert "revert architect 0" in whys, whys
        st = s.check_status()
        assert st["req_conservation"] == "SORRY" and "ERROR" not in st.values(), st
        assert repair.own_sorry_free(s, "req_conservation") and repair.pending_deps(s, "req_conservation") == ["arch0_core"]
        assert (s.out / "arch_0.md").exists()
    finally:
        close(s)


def test_planner_failure_ends_the_plan_without_more_retries():
    s = session()
    seen = []
    def fail(self, model, messages, purpose, **k):
        seen.append(k)
        raise repair.APIError(503, "overloaded")
    try:
        with patch.object(repair.Session, "call", fail):
            assert repair.plan(s, args(planner="muse-wonder-1.0"), "", "req_conservation", 0) == ([], "")
        assert len(seen) == 1 and seen[0]["max_tokens"] == repair.PLANNER_MAX_TOKENS
        assert seen[0]["attempts"] == repair.PLANNER_ATTEMPTS
    finally:
        close(s)


def test_architect_falls_back_to_the_prover_when_the_planner_fails():
    if not have_lean():
        print("skip (no Lean image)")
        return
    s = session()
    models = []
    def call(self, model, messages, purpose, **k):
        models.append((model, k.get("max_tokens")))
        if model == "muse-wonder-1.0":
            raise repair.APIError(503, "overloaded")
        return reply(SKELETON)
    try:
        with patch.object(repair.Session, "call", call):
            helpers, derived = repair.architect(s, args(planner="muse-wonder-1.0"), "", ["req_conservation"], 0)
        assert models == [("muse-wonder-1.0", repair.PLANNER_MAX_TOKENS), ("muse-spark-1.3-contributor", None)], models
        assert derived == ["req_conservation"]
        assert any(e["kind"] == "architect_fallback" for e in s.events)
    finally:
        close(s)


def test_finish_selects_the_best_compiling_version():
    if not have_lean():
        print("skip (no Lean image)")
        return
    s = session(EVIDENCE)
    try:
        assert set(s.check_status().values()) == {"PROVED"}
        s._save(TASK.start.read_text(), "worse rewrite")
        assert set(s.check_status().values()) == {"SORRY"}
        summary = repair.finish(s, s.out, "A1", {}, select="best")
        assert set(summary["final_status"].values()) == {"PROVED"}, summary["final_status"]
        assert summary["final_snapshot"]["selected"].startswith("restore best version")
        s2 = session(EVIDENCE)
        s2.check_status()
        s2._save(TASK.start.read_text(), "worse rewrite")
        summary2 = repair.finish(s2, s2.out, "A0", {})
        assert set(summary2["final_status"].values()) == {"SORRY"}   # the baseline keeps the newest
        close(s2)
    finally:
        shutil.rmtree(s.out, ignore_errors=True)


def test_compact_removes_unused_helpers_and_keeps_attributed_ones():
    if not have_lean():
        print("skip (no Lean image)")
        return
    s = session(EVIDENCE)
    try:
        extra = ("theorem zz_unused : (1 : Nat) + 1 = 2 := by decide\n\n"
                 "@[simp] theorem zz_simp : (2 : Nat) + 0 = 2 := by decide\n\n"
                 "theorem zz_open : (3 : Nat) = 3 := by sorry\n\nend Payout")
        s._save(s._source().replace("end Payout", extra), "fixture")
        s.check_status()
        repair.compact(s)
        src = s._source()
        assert "zz_unused" not in src and "zz_open" not in src and "zz_simp" in src, src[-600:]
        assert set(s.check_status().values()) == {"PROVED"}
    finally:
        close(s)


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
