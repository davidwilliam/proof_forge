"""Rendered hint diffs in Lean's output (integrations/muse/proofforge_mcp.py, agents/muse_code.py).
No model calls, no Lean.

Lean renders the fix of a deprecated name as a diff, one combining strikethrough or underline mark
per character (`i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲`). clean_lean drops the warning's header and `Hint:`
lines, so these lines trailed the message before them: in the ten proofforge-full runs of
hard-task-1, 82 of 218 lean_build results carried them, and with the current compact_build 8,892
characters of them were still left in 60 results, after errors. In the full profile, lean_build
and the continuation's first errors now leave them out; the lean and proofforge profiles return
Lean's output as before.

Run: python3 tests/test_muse_hint_diffs.py
"""
import gzip, json, pathlib, shutil, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse"), str(ROOT / "tests")]
import muse_code  # noqa: E402
import proofforge_mcp as pm  # noqa: E402
import test_muse_keep_best as kb  # noqa: E402

DIFF = "  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲"
OUTPUT = f"""error: candidate/Solution.lean:20:4: unsolved goals
a : Nat
⊢ a ≤ a + 1

{DIFF}

{DIFF}

warning: candidate/Solution.lean:30:8: declaration uses `sorry`
error: build failed"""


def test_compact_build_and_first_errors_drop_hint_diffs():
    out = pm.compact_build(OUTPUT, "")
    assert pm.HINT_DIFF.search(out) is None, out
    assert out == ("error: candidate/Solution.lean:20:4: unsolved goals\na : Nat\n⊢ a ≤ a + 1\n\nerror: build failed\n"
                   "warning: 1 declaration uses `sorry`: line 30"), out
    first = muse_code.first_errors(OUTPUT)
    assert pm.HINT_DIFF.search(first) is None and first == "error: candidate/Solution.lean:20:4: unsolved goals\n" \
        "a : Nat\n⊢ a ≤ a + 1\n", repr(first)
    assert pm.drop_hint_diffs("a\n\n\n\nb") == "a\n\nb" and pm.drop_hint_diffs("") == ""


def test_only_the_full_profile_drops_them():
    ws, out = kb.dirs()
    try:
        (ws / "candidate/Solution.lean").write_text(kb.candidate())
        full = kb.Scripted(ws, "full", OUTPUT).lean_build()
        assert DIFF not in full and "unsolved goals" in full, full
        for profile in ("lean", "proofforge"):
            r = kb.Scripted(ws, profile, OUTPUT).lean_build()
            assert r.count(DIFF) == 2, r
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_hard_task_1_build_outputs_lose_only_the_diffs():
    """The lean_build results of the proofforge-full runs of hard-task-1 (made before compact_build):
    compact_build leaves no hint diff and keeps every error line."""
    n = diffs = 0
    for run in sorted((ROOT / "results/hard-task-1/runs").glob("*/proofforge-full-*")):
        kinds, per = {}, {}
        for line in gzip.open(run / "events.jsonl.gz", "rt"):
            e = json.loads(line)
            ev = (e.get("payload") or {}).get("event") or {}
            if e.get("payload_type") == "task.lifecycle.proposed":
                kinds[ev.get("task_id")] = ev.get("task_kind")
            elif e.get("payload_type") == "task.lifecycle.output":
                per[ev.get("task_id")] = per.get(ev.get("task_id"), "") + (ev.get("chunk") or "")
        for tid, text in per.items():
            if kinds.get(tid) != "tool.mcp__proofforge__lean_build":
                continue
            body = text.split("\n", 2)[2] if text.startswith("$ ") else text
            out = pm.compact_build(body, "")
            n += 1
            diffs += bool(pm.HINT_DIFF.search(body))
            assert pm.HINT_DIFF.search(out) is None
            errors = [l for l in body.splitlines() if l.startswith("error:")]
            assert [l for l in out.splitlines() if l.startswith("error:")] == errors, run
    assert n == 218 and diffs == 82, (n, diffs)


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
