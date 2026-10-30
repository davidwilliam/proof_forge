"""ProofForgeFin (lib/): sources free of proof escape hatches, the library and its demonstrations
build in the pinned Lean image, and the axiom audit reports only propext, Classical.choice and
Quot.sound. A probe copy of the library with a `sorry`, a `native_decide` and a `bv_decide` checks
that the audit reports each of them.

The build and audit tests need Docker and the pinned Lean image; they are skipped without them.
They share the judge's container slots and run one container at a time.
Run: python3 tests/test_fin_lib.py
"""
import pathlib, re, shutil, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness")]
import judge  # noqa: E402

LIB = ROOT / "lib"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [r"(?<![\w.])sorry(?!\w)", r"(?<![\w.])admit(?!\w)", r"native_decide", r"bv_decide",
             r"decide\s*\+kernel", r"implemented_by", r"@\[\s*extern", r"(?<![\w.])unsafe(?!\w)",
             r"skipKernelTC", r"(?m)^\s*(?:private\s+|protected\s+)?axiom\s"]
SCRIPT = ("mkdir -p .lake; lake build > .lake/fin-build.log 2>&1; echo build=$?; "
          "lake env lean Audit.lean > .lake/fin-audit.log 2>&1; echo audit=$?")
AUDIT_LINE = re.compile(r"audit: (\d+) constants, (\d+) theorems, (\d+) violations")


def sources():
    return sorted(LIB.glob("ProofForgeFin*/**/*.lean")) + sorted(LIB.glob("*.lean"))


def strip_comments(text):
    """Lean source without block comments, doc comments and line comments."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def docker_ready():
    try:
        r = subprocess.run(["docker", "image", "inspect", judge.IMAGE], capture_output=True, timeout=30)
        return r.returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def skip_without_docker():
    if docker_ready():
        return False
    try:
        import pytest
        pytest.skip("Docker or the pinned Lean image is not available")
    except ImportError:
        print("skip: Docker or the pinned Lean image is not available")
    return True


def build_and_audit(project):
    r = judge.in_container(project, SCRIPT, timeout=1800)
    build = (project / ".lake/fin-build.log").read_text(errors="replace")
    audit = (project / ".lake/fin-audit.log").read_text(errors="replace")
    return r, build, audit


def test_sources_have_no_escape_hatches():
    files = sources()
    assert len(files) >= 10
    for f in files:
        code = strip_comments(f.read_text())
        for pattern in FORBIDDEN:
            assert not re.search(pattern, code), (f.name, pattern)


def test_library_builds_and_audit_is_clean():
    if skip_without_docker():
        return
    r, build, audit = build_and_audit(LIB)
    assert "build=0" in r["output_tail"], build[-3000:]
    assert "audit=0" in r["output_tail"], audit[-3000:]
    assert "error" not in build.lower(), build[-3000:]
    assert "sorry" not in build, build[-3000:]
    assert "warning" not in build, build[-3000:]
    m = AUDIT_LINE.search(audit)
    assert m, audit[-3000:]
    constants, theorems, violations = map(int, m.groups())
    assert violations == 0 and "violation:" not in audit, audit
    assert constants >= 1000 and theorems >= 250, m.group(0)
    used = re.search(r"axioms used: \[([^\]]*)\]", audit)
    assert used and {a.strip() for a in used.group(1).split(",") if a.strip()} <= ALLOWED, audit
    printed = re.findall(r"'([\w.]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", audit)
    assert len(printed) >= 30, audit
    for name, axs in printed:
        assert {a.strip() for a in axs.split(",") if a.strip()} <= ALLOWED, (name, axs)


def test_audit_reports_sorry_native_decide_and_bv_decide():
    if skip_without_docker():
        return
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-fin-probe-"))
    try:
        probe = d / "lib"
        shutil.copytree(LIB, probe, ignore=shutil.ignore_patterns("fin-*.log"))
        (probe / "ProofForgeFinDemo/Probe.lean").write_text(
            "import Std.Tactic.BVDecide\n\n"
            "theorem probe_sorry : 1 = 2 := sorry\n\n"
            "theorem probe_native : 2 + 2 = 4 := by native_decide\n\n"
            "theorem probe_bv (x y : BitVec 8) : x * y = y * x := by bv_decide\n")
        root = probe / "ProofForgeFinDemo.lean"
        root.write_text("import ProofForgeFinDemo.Probe\n" + root.read_text())
        r, build, audit = build_and_audit(probe)
        assert "build=0" in r["output_tail"], build[-3000:]
        m = AUDIT_LINE.search(audit)
        assert m and int(m.group(3)) > 0, audit[-3000:]
        flagged = set(re.findall(r"violation: (probe_\w+)", audit))
        assert flagged == {"probe_sorry", "probe_native", "probe_bv"}, [l for l in audit.splitlines() if "probe" in l]
        assert "violation: probe_sorry depends on [sorryAx]" in audit, audit[-3000:]
    finally:
        shutil.rmtree(d, ignore_errors=True)


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
