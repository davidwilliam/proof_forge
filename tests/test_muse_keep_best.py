"""What a proofforge-full run keeps of its progress (agents/muse_code.py). No model calls, no Lean:
a scripted Lean stands in for the container (a candidate with the marker `BROKEN` does not compile;
a required theorem is proved when neither it nor a candidate declaration it uses has `sorry` or
`admit`).

  * the final candidate of a proofforge-full run is the compiling version with the most required
    theorems proved by Lean, the latest on a tie, when the file on disk does not compile or proves
    fewer; the file on disk otherwise, and when Lean gives no verdict; the other arms keep the file
    on disk.

Run: python3 tests/test_muse_keep_best.py
"""
import json, pathlib, re, shutil, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse")]
import muse_code, ledger  # noqa: E402
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


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
