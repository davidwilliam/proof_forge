"""Versions of the candidate that no ProofForge tool compiled (agents/muse_code.py). No model calls;
a scripted Lean stands in for the container (test_muse_keep_best.ScriptedLean).

The best compiling version of a proofforge-full run was chosen among the versions Lean compiled in
lean_build (without `file`), check_candidate or the runner's checks between sessions. A version
written to disk and checked another way (check_snippet_fast, try_snippet, lean_build with `file`)
or not at all was not considered. Now:

  * the runner keeps every version it sees on disk (Session.seen, every 2 s) and version_pool
    merges them with the compiled ones, oldest first, with the set of compiled ones;
  * candidates takes the best compiled versions by their text, as before, and the best versions
    seen on disk only that prove more by their text than any compiled one, never the file on disk;
  * the final choice and the continuation between sessions compile those too: a version seen on
    disk only that compiles and proves more is chosen (summary.json says it was not compiled in
    the run), one that does not compile is passed over.

With Lean (the pinned image, one container at a time; skipped with --quick): the final choice on
rate-limiters-bucket-b1 takes a version seen on disk only.

Run: python3 tests/test_muse_seen_versions.py [--quick]
"""
import json, os, pathlib, shutil, sys, tempfile, time, types

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse"), str(ROOT / "tests")]
import muse_code  # noqa: E402
import proofforge_mcp as pm  # noqa: E402
import test_muse_keep_best as kb  # noqa: E402

TASK = kb.TASK
TH = TASK.theorems


def test_version_pool_merges_compiled_and_seen_versions():
    rec = pathlib.Path(tempfile.mkdtemp(prefix="pf-seen-rec-"))
    try:
        a, b, c, d = (kb.candidate(TH[:k]) for k in (1, 2, 3, 4))
        (rec / "compiled-001-x.lean").write_text(b)
        os.utime(rec / "compiled-001-x.lean", (200, 200))
        seen = [(100, a), (150, b), (300, c), (400, b)]
        texts, compiled = muse_code.version_pool(rec, [(350, d)], seen)
        assert texts == [a, b, c, d], [muse_code.text_proved(TASK, x) for x in texts]
        assert compiled == {b, d}
        assert muse_code.version_pool(None, (), seen) == ([a, b, c], set())
    finally:
        shutil.rmtree(rec)


def test_candidates_add_better_versions_seen_on_disk_only():
    v = [kb.candidate(TH[:1]), kb.candidate(TH[:2]), kb.candidate(TH[:4]), kb.candidate(TH[:3]),
         kb.candidate(TH[:5], broken=True), kb.candidate(TH[:2], extra="-- seen")]
    compiled = {v[0], v[1]}
    # without the set every version counts as compiled, as before
    assert muse_code.candidates(TASK, v, current="", limit=3) == muse_code.rank_versions(TASK, v)[:3]
    # the compiled ones by their text, then the ones seen only that prove more than 2 by their text
    assert muse_code.candidates(TASK, v, current="", limit=3, compiled=compiled) == [1, 0, 4, 2, 3]
    assert muse_code.candidates(TASK, v, current=v[4], limit=2, compiled=compiled) == [1, 0, 2, 3]
    assert muse_code.candidates(TASK, v, current="", limit=1, compiled=set()) == [4]


def choose(ws, out, versions, disk, compiled):
    (ws / "candidate/Solution.lean").write_text(disk)
    lean = kb.ScriptedLean(ws)
    ok, status = muse_code.compiles(lean)
    return muse_code.choose_final(lean, TASK, ws, out, versions, disk, ok, status, compiled), lean


def test_final_choice_takes_a_better_version_seen_on_disk_only():
    ws, out = kb.dirs()
    try:
        built, seen_good, seen_broken = kb.candidate(TH[:1]), kb.candidate(TH[:3]), kb.candidate(TH[:5], broken=True)
        disk = kb.candidate(TH[:2], broken=True)
        (text, ok, status, rec), lean = choose(ws, out, [built, seen_good, seen_broken, disk], disk, {built})
        assert text == seen_good and ok and rec["proved"] == sorted(TH[:3]) and rec["compiled_in_run"] is False, rec
        assert (out / "final-on-disk.lean").read_text() == disk and (ws / "candidate/Solution.lean").read_text() == seen_good
        assert lean.builds == 1 + 3, lean.builds              # the file on disk, then three versions
        # a compiled version that proves as much as anything seen wins, and is marked as compiled
        (text, _, _, rec), lean = choose(ws, out, [seen_broken, built, kb.candidate(TH[:1], extra="-- seen")], disk, {built})
        assert text == built and rec["compiled_in_run"] is True and lean.builds == 1 + 2, (rec, lean.builds)
        # without the set of compiled versions the record is as before
        (_, _, _, rec), _ = choose(ws, out, [built], disk, None)
        assert "compiled_in_run" not in rec, rec
        json.dumps(rec)
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_continuation_restores_a_version_seen_on_disk_only():
    ws, out = kb.dirs()
    try:
        built, seen_good = kb.candidate(TH[:1]), kb.candidate(TH[:2])
        broken = kb.candidate(TH[:3], broken=True)
        (ws / "candidate/Solution.lean").write_text(broken)
        lean = kb.ScriptedLean(ws)
        record = {}
        ok, feedback = muse_code.ordinary_feedback(lean, TASK, ws, record)
        assert not ok and "lean" in record
        msg = muse_code.progress_prompt(lean, TASK, ws, 4, feedback, record, built, [built, seen_good, broken],
                                        compiled={built})
        assert "unfinished-04.lean" in msg and f"it proves 2 of {len(TH)} required theorems" in msg, msg
        assert (ws / "candidate/Solution.lean").read_text() == seen_good
        assert json.loads((ws / pm.BEST_RECORD).read_text())["proved"] == list(TH[:2])
        # a compiling file hears of a version seen on disk only that proves more
        (ws / pm.BEST).unlink()
        current = kb.candidate(TH[:1], extra="-- current")
        (ws / "candidate/Solution.lean").write_text(current)
        record = {}
        _, feedback = muse_code.ordinary_feedback(lean, TASK, ws, record)
        msg = muse_code.progress_prompt(lean, TASK, ws, 5, feedback, record, "x", [built, seen_good, current],
                                        compiled={built, current})
        assert f"An earlier compiling version of this run, saved as {pm.BEST}, proves more; it proves 2" in msg, msg
        assert (ws / "candidate/Solution.lean").read_text() == current and (ws / pm.BEST).read_text() == seen_good
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_session_keeps_every_version_it_sees():
    ws, out = kb.dirs()
    try:
        a = types.SimpleNamespace()
        s = muse_code.Session(a, TASK, ws, out, None, 0, {}, "sid")
        for text in ("one", "one", "two", "one"):
            (ws / "candidate/Solution.lean").write_text(text)
            s.snapshot()
        assert [x for _, x in s.seen] == ["one", "two", "one"] and s.snaps == 3
        assert all(abs(t - time.time()) < 60 for t, _ in s.seen)
        assert (out / "candidate_v002.lean").read_text() == "two"
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


# With Lean (the pinned image, one container at a time)

def test_final_choice_with_a_version_seen_on_disk_only_with_lean():
    import test_topdown as td, test_feedback as fb
    bucket = td.BUCKET
    broken = fb.CLEAN.replace("theorem td0_step_of_not", "theorem td0_step_of_not : Nat := \"x\"\n\ntheorem td0_unused")
    ws = muse_code.make_workspace(bucket, "proofforge-full", None)
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-seen-out-"))
    try:
        server = pm.Server(ws, bucket.id, "lean")
        (ws / "candidate/Solution.lean").write_text(broken)
        ok, status = muse_code.compiles(server)
        assert not ok
        versions = [td.FIXED_BUCKET, fb.CLEAN, broken]
        text, ok, status, rec = muse_code.choose_final(server, bucket, ws, out, versions, broken, ok, status,
                                                       {td.FIXED_BUCKET})
        assert text == fb.CLEAN and ok and rec["compiled_in_run"] is False, rec
        assert len(rec["proved"]) == len(bucket.theorems) - 1
    finally:
        shutil.rmtree(ws, ignore_errors=True)
        shutil.rmtree(out, ignore_errors=True)


LEAN_TESTS = {"test_final_choice_with_a_version_seen_on_disk_only_with_lean"}

if __name__ == "__main__":
    quick = "--quick" in sys.argv
    for name, fn in list(globals().items()):
        if not name.startswith("test_"):
            continue
        if name in LEAN_TESTS and (quick or not __import__("test_topdown").have_lean()):
            print(f"skip  {name}")
            continue
        fn()
        print(f"ok  {name}")
