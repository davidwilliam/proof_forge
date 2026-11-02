"""Lean's output in the `full` profile of integrations/muse/proofforge_mcp.py. No model calls, no
Lean: a scripted Lean stands in for the container.

In the ten proofforge-full runs of results/frontier-3 (rw-compound-comp), lean_build returned the
last 4,000 characters of Lean's output, the part the judge's run record keeps (judge.run): 95
of the 144 failed builds began inside a message, so the position of the first error was not
shown, and in the eight runs that did not verify that was 90 of 138. Three of those runs (longest
streaks of 10, 10 and 21 failed builds in a row) spent 69 to 82 percent of their budget in streaks
of three or more failed builds; the runs that verified never had more than two in a row.

  * the full profile reads Lean's output whole (LEAN_KEEP characters) and cuts a long output from
    the end (clip_lean): the first errors stay whole and every later message is named by its
    first line; the `lean` and `proofforge` profiles, the tools of the other arms, are unchanged;
  * try_snippet and the `lean_errors` of check_candidate are cut the same way in the full profile;
  * from the third failed build in a row the result names the declarations with errors and how to
    work on them outside the file; a build that compiles resets the count;
  * the recorded results of results/frontier-3 show the cut this replaces.

Run: python3 tests/test_muse_build_output.py
"""
import gzip, json, pathlib, re, shutil, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse"), str(ROOT / "tests")]
import judge  # noqa: E402
import proofforge_mcp as pm  # noqa: E402
import test_muse_keep_best as kb  # noqa: E402

TH = kb.TASK.theorems


def long_output(n_errors=6, body=2500):
    """A failed build: `n_errors` errors with long goals, each in a different declaration."""
    text = kb.candidate()
    lines = [i for i, l in enumerate(text.splitlines(), 1) if l.startswith("theorem ")]
    out = []
    for k in range(n_errors):
        out.append(f"error: candidate/Solution.lean:{lines[k]}:4: unsolved goals {k}")
        out += [f"h{k}_{j} : " + "x" * 60 for j in range(body // 64)]
        out.append(f"⊢ goal {k}")
    out.append("error: build failed")
    return "\n".join(out)


def test_clip_keeps_the_first_errors_whole_and_names_the_others():
    text = long_output()
    assert len(text) > 12000
    r = pm.clip_lean(text, 6000)
    assert r.startswith("error: candidate/Solution.lean:"), r[:200]
    assert "⊢ goal 0" in r and "⊢ goal 1" in r, r
    assert "more messages, first lines only:" in r, r
    for k in range(3, 6):
        assert f"unsolved goals {k}" in r, k
    assert len(r) < 6000 + 2000
    old = pm.tail(text, 6000)
    assert "unsolved goals 0" not in old and not old.split("\n", 1)[1].startswith("error:"), old[:200]
    assert pm.clip_lean("short", 6000) == "short"
    snippet = "\n".join(f"snippet:{k}:2: error: unsolved goals\n" + "y" * 3000 for k in range(5))
    r = pm.clip_lean(snippet, 7000)
    assert r.startswith("snippet:0:2: error") and "snippet:4:2: error: unsolved goals" in r, r


def test_full_profile_reads_the_whole_output_and_other_profiles_are_unchanged():
    calls = []

    def fake(project, script, timeout=900, keep=4000):
        calls.append((script, keep))
        return {"exit_code": 0, "output_tail": "Build completed successfully", "elapsed_ms": 1}
    real = judge.in_container
    judge.in_container = fake
    ws, out = kb.dirs()
    try:
        (ws / "candidate/Solution.lean").write_text(kb.candidate())
        for profile in ("lean", "proofforge"):
            calls.clear()
            pm.Server(ws, kb.TASK.id, profile).lean_build()
            assert calls == [("set -o pipefail; lake build Solution 2>&1 | tail -c 60000", 4000)], calls
        calls.clear()
        s = pm.Server(ws, kb.TASK.id, "full")
        s.theorem_status = lambda t: {x: "SORRY" for x in t.theorems}
        s.lean_build()
        assert calls and all(k == pm.LEAN_KEEP for _, k in calls), calls
        assert f"tail -c {pm.LEAN_KEEP}" in calls[0][0], calls
    finally:
        judge.in_container = real
        shutil.rmtree(ws)
        shutil.rmtree(out)


class Failing(kb.Scripted):
    """The full-profile server with a scripted build that fails while the candidate is BROKEN."""
    def __init__(self, ws, output):
        super().__init__(ws, "full", "")
        self.fail_output = output

    def lean(self, script, timeout=None):
        r = super().lean(script, timeout)
        if r["exit_code"]:
            r["output_tail"] = self.fail_output
        return r


def test_long_build_output_starts_at_the_first_error_and_streaks_are_named():
    ws, out = kb.dirs()
    try:
        cand = ws / "candidate/Solution.lean"
        cand.write_text(kb.candidate(broken=True))
        s = Failing(ws, long_output())
        r1 = s.lean_build()
        body = r1.split("\n", 2)[2]
        assert body.startswith("error: candidate/Solution.lean:"), body[:200]
        assert "unsolved goals 0" in body and "first lines only" in body, body[-800:]
        assert "in a row" not in r1
        s.lean_build()
        r3 = s.lean_build()
        assert "This is failed build 3 in a row." in r3, r3[-600:]
        assert f"`{TH[0]}` (line" in r3 and f"`{TH[1]}` (line" in r3 and "check_snippet_fast" in r3, r3[-600:]
        cand.write_text(kb.candidate())
        assert "in a row" not in s.lean_build()
        cand.write_text(kb.candidate(broken=True))
        assert "in a row" not in s.lean_build()
        for profile in ("lean", "proofforge"):
            o = kb.Scripted(ws, profile, long_output()).lean_build()
            assert "[... earlier output omitted ...]" in o and "in a row" not in o, o[:300]
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_error_declarations_are_read_from_lake_and_lean_positions():
    src = "namespace N\n\ntheorem a : True := by\n  trivial\n\nprivate theorem b : True := by\n  exact x\n"
    out = ("error: candidate/Solution.lean:4:2: unsolved goals\n"
           "candidate/Solution.lean:7:8: error: unknown identifier 'x'\n"
           "warning: candidate/Solution.lean:3:8: declaration uses `sorry`")
    assert pm.error_decls(out, src) == [("a", 4), ("b", 7)]
    assert pm.decl_of_line(src.splitlines(), 1) is None


def test_frontier_3_build_results_began_inside_a_message():
    """The lean_build results the proofforge-full runs of results/frontier-3 received: most failed
    builds began inside a Lean message (the judge's last 4,000 characters)."""
    base = ROOT / "results/frontier-3/runs/rw-compound-comp"
    failed = mid = 0
    per = {}
    for run in sorted(base.glob("proofforge-full-*")):
        f = m = 0
        for line in gzip.open(run / "events.jsonl.gz", "rt"):
            e = json.loads(line)
            if e.get("payload_type") != "tool.result":
                continue
            t = (e.get("payload") or {}).get("text") or ""
            if not t.startswith("$ lake build Solution") or not re.search(r"exit code [1-9]", t[:80]):
                continue
            f += 1
            m += not re.match(r"\$ lake build Solution\nexit code \d+ \(\d+ ms\)\n(error|warning|\[\.\.\.)", t)
        per[run.name] = (f, m)
        failed, mid = failed + f, mid + m
    assert (failed, mid) == (144, 95), (failed, mid, per)
    unverified = [k for k in per if k not in ("proofforge-full-5", "proofforge-full-9")]
    assert sum(per[k][0] for k in unverified) == 138 and sum(per[k][1] for k in unverified) == 90, per


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            print("ok ", name)
