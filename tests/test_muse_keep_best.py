"""What a proofforge-full run keeps of its progress (agents/muse_code.py and the `full` profile of
integrations/muse/proofforge_mcp.py). No model calls, no Lean: a scripted Lean stands in for the
container (a candidate with the marker `BROKEN` does not compile; a required theorem is proved when
neither it nor a candidate declaration it uses has `sorry` or `admit`).

  * the final candidate of a proofforge-full run is the compiling version with the most required
    theorems proved by Lean, the latest on a tie, when the file on disk does not compile or proves
    fewer; the file on disk otherwise, and when Lean gives no verdict; the other arms keep the file
    on disk;
  * `lean_build` of the candidate in the `full` profile names the required theorems the build
    proves, keeps the best compiling version as .proofforge/best.lean (across server restarts, and
    not when the file was changed by hand), says how to restore it after a failed build, and gives
    the `sorry` warnings as one line and other warnings on their first line; the `lean` and
    `proofforge` profiles return Lean's output as before;
  * the continuation message of a proofforge-full run gives Lean's first errors (with their
    position, which the end of a long output leaves out), the required theorems the file proves,
    a session that did not change the file, and an earlier compiling version that proves more; a
    file that does not compile is saved under .proofforge/ and the best compiling version takes its
    place (and becomes the server's best.lean); the other arms get the message they always got;
  * the skill and AGENTS.md of the ProofForge workspace ask for the short requirements first and
    for a file that keeps compiling, with .proofforge/best.lean as the way back; the alone
    workspace has neither.

With Lean (the pinned image, one container at a time; skipped with --quick): the final choice and
the restore at the end of a session on rate-limiters-bucket-b1, with the runner's own Lean checks.

Run: python3 tests/test_muse_keep_best.py [--quick]
"""
import json, pathlib, re, shutil, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse"), str(ROOT / "tests")]
import muse_code, ledger  # noqa: E402
import proofforge_mcp as pm  # noqa: E402
import task as taskmod  # noqa: E402

TASK = taskmod.load("rw-oz-sqrt")


def candidate(proved=(), broken=False, admit=(), extra=""):
    """A candidate of rw-oz-sqrt with the given required theorems proved (a proof without `sorry`),
    the `admit` ones proved in their text only, the others `sorry`, and an error when `broken`."""
    lines = ["import OzSqrt.Spec", "import OzSqrt.Lemmas", "namespace OzSqrt", "",
             "def sqrt : SqrtFn := newtonSqrt 7", ""]
    for th in TASK.theorems:
        body = "by\n  exact proof_of_it" if th in proved else "by\n  admit" if th in admit else "sorry"
        lines.append(f"theorem {th} : P_{th} sqrt := {body}")
    lines += ["", extra, "BROKEN" if broken else "", f"end {TASK.ns}", ""]
    return "\n".join(lines)


class ScriptedLean:
    """The two Lean runs muse_code.compiles makes, answered from the workspace candidate."""
    def __init__(self, ws, verdict=True, error="error: candidate/Solution.lean:20:0: unexpected identifier"):
        self.ws, self.verdict, self.error, self.builds = ws, verdict, error, 0

    def text(self):
        return (self.ws / "candidate/Solution.lean").read_text()

    def lean(self, script, timeout=None):
        self.builds += 1
        if not self.verdict:
            return {"exit_code": 125, "output_tail": "docker: Cannot connect to the Docker daemon"}
        if "BROKEN" in self.text():
            return {"exit_code": 1, "output_tail": self.error}
        return {"exit_code": 0, "output_tail": "Build completed successfully"}

    def task(self):
        return TASK

    def theorem_status(self, task):
        text = self.text()
        done = ledger.proved_in(text, task.ns)
        out = {}
        for th in task.theorems:
            decl = re.search(rf"^theorem {th} .*$(?:\n  .*)*", text, re.M)
            out[th] = "MISSING" if not decl else "PROVED" if th in done and "admit" not in decl.group(0) else "SORRY"
        return out


def dirs():
    ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-keep-ws-"))
    (ws / "candidate").mkdir()
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-keep-out-"))
    return ws, out


def choose(ws, out, versions, disk, verdict=True):
    (ws / "candidate/Solution.lean").write_text(disk)
    lean = ScriptedLean(ws, verdict)
    if verdict:
        ok, status = muse_code.compiles(lean)
    else:
        ok, status = False, {}
    return muse_code.choose_final(lean, TASK, ws, out, versions, disk, ok, status), lean


def test_only_the_full_arm_keeps_the_best_version():
    assert muse_code.KEEP_BEST == ("proofforge-full",)
    assert set(muse_code.ARMS) - set(muse_code.KEEP_BEST) == {"alone", "proofforge"}


def test_rank_by_text_then_latest():
    th = TASK.theorems
    v = [candidate(th[:1]), candidate(th[:2]), candidate(th[:1], extra="-- later"), candidate(th[:2], extra="-- last")]
    assert muse_code.rank_versions(TASK, v) == [3, 1, 2, 0]


def test_broken_file_on_disk_is_replaced_by_the_best_compiling_version():
    th = TASK.theorems
    ws, out = dirs()
    try:
        v1, v2, v3 = candidate(th[:1]), candidate(th[:3]), candidate(th[:2])
        disk = candidate(th[:3], broken=True)
        (text, ok, status, rec), _ = choose(ws, out, [v1, v2, v3], disk)
        assert text == v2 and ok and sum(x == "PROVED" for x in status.values()) == 3
        assert rec["from"] == "best compiling version" and rec["proved"] == sorted(th[:3])
        assert rec["on_disk"] == {"compiles": False, "proved": 0}
        assert (ws / "candidate/Solution.lean").read_text() == v2
        assert (out / "final-on-disk.lean").read_text() == disk
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_compiling_file_on_disk_is_kept_unless_an_earlier_version_proves_more():
    th = TASK.theorems
    ws, out = dirs()
    try:
        older = candidate(th[:2])
        disk = candidate(th[:2], extra="-- newer, as good")
        (text, ok, _, rec), _ = choose(ws, out, [older, disk], disk)
        assert text == disk and ok and rec["from"] == "file on disk" and rec["on_disk"]["proved"] == 2
        assert not (out / "final-on-disk.lean").exists()
        worse = candidate(th[:1])
        (text, ok, _, rec), _ = choose(ws, out, [older, worse], worse)
        assert text == older and rec["from"] == "best compiling version" and rec["on_disk"] == {"compiles": True, "proved": 1}
        assert (out / "final-on-disk.lean").read_text() == worse
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_lean_decides_between_versions_whose_text_disagrees():
    """`admit` reads as proved in the text; Lean's status (sorryAx) ranks it below."""
    th = TASK.theorems
    ws, out = dirs()
    try:
        honest, admitted = candidate(th[:1]), candidate(admit=th[:4], extra="-- later")
        disk = candidate(broken=True)
        (text, _, status, rec), lean = choose(ws, out, [honest, admitted], disk)
        assert text == honest and rec["proved"] == [th[0]], rec
        assert lean.builds <= 2 * (1 + muse_code.BEST_CANDIDATES)
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_no_verdict_or_no_compiling_version_keeps_the_file_on_disk():
    th = TASK.theorems
    ws, out = dirs()
    try:
        disk = candidate(th[:1], broken=True)
        (text, ok, _, rec), _ = choose(ws, out, [candidate(th[:2])], disk, verdict=False)
        assert text == disk and not ok and rec["from"] == "file on disk" and "no verdict" in rec["error"]
        assert (ws / "candidate/Solution.lean").read_text() == disk
        (text, ok, _, rec), _ = choose(ws, out, [], disk)
        assert text == disk and not ok and rec == {"from": "file on disk", "on_disk": {"compiles": False, "proved": 0}}
        assert not (out / "final-on-disk.lean").exists()
        json.dumps(rec)
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


# lean_build in the full profile

WARNINGS = """warning: candidate/Solution.lean:{a}:25: Variable name `hn` is not explicitly referenced.

  [apply] _hn

warning: candidate/Solution.lean:{b}:8: declaration uses `sorry`
warning: candidate/Solution.lean:{c}:8: declaration uses `sorry`
Build completed successfully (10 jobs)."""

ERROR = """error: candidate/Solution.lean:{a}:4: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  l ≥ 0
where
 a := ↑X / 2
warning: candidate/Solution.lean:{b}:8: declaration uses `sorry`
Some required targets logged failures:
- Solution
error: build failed"""


class Scripted(pm.Server):
    """The MCP server with the scripted Lean in place of the container."""
    def __init__(self, ws, profile, output=""):
        super().__init__(ws, TASK.id, profile)
        self.scripted, self.output = ScriptedLean(ws), output

    def lean(self, script, timeout=None):
        r = dict(self.scripted.lean(script))
        r["output_tail"] = self.output + "\n" + r["output_tail"]
        r["elapsed_ms"] = 1000
        return r

    def theorem_status(self, t):
        return self.scripted.theorem_status(t)


def line_of(text, name):
    return next(i for i, l in enumerate(text.splitlines(), 1) if re.match(rf"theorem {name} ", l))


def test_full_build_names_what_it_proves_and_keeps_the_best_version():
    th, n = TASK.theorems, len(TASK.theorems)
    ws, out = dirs()
    try:
        cand = ws / "candidate/Solution.lean"
        best = ws / pm.BEST
        s = Scripted(ws, "full")
        v1 = candidate(th[:2])
        cand.write_text(v1)
        r = s.lean_build()
        assert f"Required theorems proved in this build: 2 of {n}: {th[0]}, {th[1]}." in r, r
        assert f"Not proved yet: {th[2]} (sorry)" in r and f"Kept as {pm.BEST}" in r, r
        assert best.read_text() == v1 and json.loads((ws / pm.BEST_RECORD).read_text())["proved"] == list(th[:2])
        cand.write_text(candidate(th[:1]))                    # fewer: the best stays
        r = s.lean_build()
        assert f"proved in this build: 1 of {n}" in r and f"The best compiling version so far, {pm.BEST}, proves 2 of {n}" in r, r
        assert best.read_text() == v1
        cand.write_text(candidate(th[:3], broken=True))       # a failed build names the way back
        r = s.lean_build()
        assert "exit code 1" in r and f"`cp {pm.BEST} candidate/Solution.lean` restores it" in r, r
        assert "proves 2 of" in r and best.read_text() == v1
        v2 = candidate(th[1:3])                               # as many, later: kept
        cand.write_text(v2)
        s2 = Scripted(ws, "full")                             # a new session's server reads the record
        r = s2.lean_build()
        assert f"Kept as {pm.BEST}" in r and best.read_text() == v2, r
        best.write_text("edited by hand")                     # a record that no longer matches is not trusted
        cand.write_text(candidate(th[:1], broken=True))
        assert "restores it" not in s2.lean_build()
        cand.write_text(candidate())
        r = s2.lean_build()
        assert f"0 of {n}." in r and f"Kept as {pm.BEST}" in r and best.read_text() == candidate()
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_full_build_output_is_compact_and_other_profiles_are_unchanged():
    th = TASK.theorems
    ws, out = dirs()
    try:
        text = candidate(th[:6])
        (ws / "candidate/Solution.lean").write_text(text)
        a, b, c = 5, line_of(text, th[6]), line_of(text, th[7])
        lean_out = WARNINGS.format(a=a, b=b, c=c)
        r = Scripted(ws, "full", lean_out).lean_build()
        assert "warning: candidate/Solution.lean:5:25: Variable name `hn` is not explicitly referenced." in r, r
        assert "[apply] _hn" not in r and "declaration uses `sorry`\n" not in r, r
        assert f"warning: 2 declarations use `sorry`: {th[6]} (line {b}), {th[7]} (line {c})" in r, r
        assert "Build completed successfully (10 jobs)." in r and "Required theorems proved in this build: 6" in r, r
        for profile in ("lean", "proofforge"):
            r = Scripted(ws, profile, lean_out).lean_build()
            assert r == "$ lake build Solution\nexit code 0 (1000 ms)\n" + pm.clean_lean(lean_out + "\nBuild completed successfully"), r
        assert not (ws / pm.BEST).exists() or json.loads((ws / pm.BEST_RECORD).read_text())["proved"] == list(th[:6])
        bad = candidate(th[:6], broken=True)
        (ws / "candidate/Solution.lean").write_text(bad)
        r = Scripted(ws, "full", ERROR.format(a=a, b=b)).lean_build()
        assert "omega could not prove the goal:\na possible counterexample" in r and " a := ↑X / 2" in r, r
        assert f"warning: 1 declaration uses `sorry`: {th[6]} (line {b})" in r and "error: build failed" in r, r
        assert "- Solution" in r and "restores it" in r, r
        full = {t["name"]: t for t in Scripted(ws, "full").tools()}
        assert pm.BEST in full["lean_build"]["description"]
        for profile in ("lean", "proofforge"):
            assert pm.BEST not in {t["name"]: t for t in Scripted(ws, profile).tools()}["lean_build"]["description"]
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_full_build_without_an_axiom_verdict_says_nothing_of_progress():
    ws, out = dirs()
    try:
        (ws / "candidate/Solution.lean").write_text(candidate())
        s = Scripted(ws, "full")
        s.theorem_status = lambda t: {x: "MISSING" for x in t.theorems}
        r = s.lean_build()
        assert "exit code 0" in r and "Required theorems" not in r and not (ws / pm.BEST).exists(), r
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


# Continuation messages

GOAL_DUMP = "error: candidate/Solution.lean:{a}:6: omega could not prove the goal:\n" + "\n".join(
    f" v{i} := ↑(ProofForgeFin.Sqrt.newton a (2 ^ k) - a.sqrt) * {i}" for i in range(400)) + "\nerror: build failed"


def continue_after(ws, text, versions, start_text=None, error=None, n=2):
    """Session part n ends with `text` on disk: (message, ordinary_feedback's message)."""
    (ws / "candidate/Solution.lean").write_text(text)
    lean = ScriptedLean(ws, error=error or ScriptedLean(ws).error)
    record = {}
    ok, feedback = muse_code.ordinary_feedback(lean, TASK, ws, record)
    assert not ok and feedback
    msg = muse_code.progress_prompt(lean, TASK, ws, n, feedback, record,
                                    text if start_text is None else start_text, versions)
    return msg, feedback


def test_other_arms_continue_with_the_message_they_always_got():
    old = ("Your session ended, but the task is not finished. " + "FEEDBACK" +
           "\nContinue from the current candidate/Solution.lean until the file compiles and every required theorem is proved.")
    assert muse_code.CONTINUE + "FEEDBACK" + muse_code.CONTINUE_END == old


def test_a_broken_file_at_the_end_of_a_session_gives_way_to_the_best_compiling_version():
    th, n = TASK.theorems, len(TASK.theorems)
    ws, out = dirs()
    try:
        v1, v2 = candidate(th[:2]), candidate(th[:1], extra="-- later")
        broken = candidate(th[:3], broken=True)
        a = broken.splitlines().index("BROKEN") + 1
        msg, feedback = continue_after(ws, broken, [v1, v2], start_text=v2, error=GOAL_DUMP.format(a=a), n=3)
        assert "omega could not prove the goal" not in feedback[-6000:]     # the end of the output lost the error
        assert f"error: candidate/Solution.lean:{a}:6: omega could not prove the goal:" in msg, msg
        assert "  [...]" in msg and len(msg) < 6000, len(msg)
        assert "That file is saved as .proofforge/unfinished-03.lean" in msg and "made no change" not in msg, msg
        assert f"it proves 2 of {n} required theorems: {th[0]}, {th[1]}; not proved yet: {th[2]} (sorry)" in msg, msg
        assert msg.startswith(muse_code.CONTINUE) and msg.endswith(muse_code.CONTINUE_END)
        assert (ws / "candidate/Solution.lean").read_text() == v1
        assert (ws / ".proofforge/unfinished-03.lean").read_text() == broken
        s = pm.Server(ws, TASK.id, "full")                               # the server takes it as its best version
        assert s.best_record()["proved"] == list(th[:2]) and (ws / pm.BEST).read_text() == v1
        # Nothing compiled yet: the file stays, with Lean's first errors.
        ws2, out2 = dirs()
        try:
            msg, _ = continue_after(ws2, broken, [])
            assert "does not compile. Lean's first errors:\nerror: candidate/Solution.lean:20:0" in msg, msg
            assert (ws2 / "candidate/Solution.lean").read_text() == broken and not (ws2 / ".proofforge").exists()
        finally:
            shutil.rmtree(ws2)
            shutil.rmtree(out2)
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_a_compiling_file_hears_what_it_proves_and_of_a_better_earlier_version():
    th, n = TASK.theorems, len(TASK.theorems)
    ws, out = dirs()
    try:
        current = candidate(th[:1])
        msg, _ = continue_after(ws, current, [candidate(th[:3]), current])
        assert "The session made no change to candidate/Solution.lean." in msg, msg
        assert f"candidate/Solution.lean compiles; it proves 1 of {n} required theorems: {th[0]}; not proved yet: " in msg, msg
        assert f"An earlier compiling version of this run, saved as {pm.BEST}, proves more; it proves 3 of {n}" in msg, msg
        assert (ws / "candidate/Solution.lean").read_text() == current               # a compiling file is never replaced
        assert (ws / pm.BEST).read_text() == candidate(th[:3])
        (ws / pm.BEST).unlink()
        msg, _ = continue_after(ws, current, [candidate(th[:1], extra="-- older"), current], start_text="changed")
        assert "made no change" not in msg and "earlier compiling version" not in msg and not (ws / pm.BEST).exists(), msg
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_a_judge_rejection_is_passed_on_as_is():
    from unittest.mock import patch
    ws, out = dirs()
    try:
        rejected = {"accepted": False, "checks": {"tree": {"problems": []}, "impl_scan": {"problems": []},
                                                  "comparator": {"exit_code": 1, "output_tail": "error: theorem statement differs"}}}
        with patch.object(muse_code.judge, "judge", return_value=rejected), \
                patch.object(muse_code.judge, "impl_scan", return_value={"problems": []}):
            msg, feedback = continue_after(ws, candidate(TASK.theorems), [])
        assert "judge rejected it" in feedback and msg == muse_code.CONTINUE + \
            "The session made no change to candidate/Solution.lean. " + feedback + muse_code.CONTINUE_END, msg
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


# Guidance

def test_workspace_guidance_banks_short_requirements_and_keeps_the_file_compiling():
    alone = muse_code.make_workspace(TASK, "alone")
    full = muse_code.make_workspace(TASK, "proofforge-full")
    try:
        skill = (full / ".agents/skills/proofforge/SKILL.md").read_text()
        agents = (full / "AGENTS.md").read_text()
        steps = re.findall(r"^(\d+)\. \*\*([^*]+)\*\*", skill, re.M)
        assert [int(n) for n, _ in steps] == list(range(1, len(steps) + 1)), steps
        names = [s for _, s in steps]
        assert names.index("Bank the short requirements first.") < names.index("Prove, cheapest first.")
        assert names.index("Keep the file compiling.") < names.index("Check and iterate.")
        assert "`cp .proofforge/best.lean candidate/Solution.lean`" in skill and pm.BEST in agents
        assert "Keep the file compiling" in agents and "follow directly from the definitions" in agents
        assert not (alone / ".agents").exists() and not (alone / "AGENTS.md").exists()
    finally:
        shutil.rmtree(alone)
        shutil.rmtree(full)


# With Lean (the pinned image, one container at a time)

def test_final_choice_and_restore_with_lean():
    """On rate-limiters-bucket-b1: a run whose file on disk does not compile ends on its compiling
    version with the most required theorems proved, and a session ending on that file is continued
    from it."""
    import test_topdown as td, test_feedback as fb
    bucket = td.BUCKET
    broken = fb.CLEAN.replace("theorem td0_step_of_not", "theorem td0_step_of_not : Nat := \"x\"\n\ntheorem td0_unused")
    ws = muse_code.make_workspace(bucket, "proofforge-full", None)
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-keep-out-"))
    try:
        server = pm.Server(ws, bucket.id, "lean")
        (ws / "candidate/Solution.lean").write_text(broken)
        ok, status = muse_code.compiles(server)
        assert not ok
        versions = [td.FIXED_BUCKET, fb.CLEAN, td.FIXED_BUCKET + "\n"]
        text, ok, status, rec = muse_code.choose_final(server, bucket, ws, out, versions, broken, ok, status)
        assert text == fb.CLEAN and ok and rec["from"] == "best compiling version", rec
        assert len(rec["proved"]) == len(bucket.theorems) - 1 and (out / "final-on-disk.lean").read_text() == broken
        (ws / "candidate/Solution.lean").write_text(broken)
        record = {}
        ok, feedback = muse_code.ordinary_feedback(server, bucket, ws, record)
        assert not ok and "lean" in record
        msg = muse_code.progress_prompt(server, bucket, ws, 2, feedback, record, td.FIXED_BUCKET, versions)
        assert "error: " in msg and "unfinished-02.lean" in msg and (ws / "candidate/Solution.lean").read_text() == fb.CLEAN, msg
        assert muse_code.compiles(server)[0]
    finally:
        shutil.rmtree(ws, ignore_errors=True)
        shutil.rmtree(out, ignore_errors=True)


LEAN_TESTS = {"test_final_choice_and_restore_with_lean"}

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
