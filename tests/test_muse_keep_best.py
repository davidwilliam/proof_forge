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
    `proofforge` profiles return Lean's output as before.

Run: python3 tests/test_muse_keep_best.py
"""
import json, pathlib, re, shutil, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse")]
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
    def __init__(self, ws, verdict=True):
        self.ws, self.verdict, self.builds = ws, verdict, 0

    def text(self):
        return (self.ws / "candidate/Solution.lean").read_text()

    def lean(self, script, timeout=None):
        self.builds += 1
        if not self.verdict:
            return {"exit_code": 125, "output_tail": "docker: Cannot connect to the Docker daemon"}
        if "BROKEN" in self.text():
            return {"exit_code": 1, "output_tail": "error: candidate/Solution.lean:20:0: unexpected identifier"}
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


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
