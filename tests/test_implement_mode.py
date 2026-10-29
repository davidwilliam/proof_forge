"""Implement mode: the starting candidate is generated from the locked challenge and spec only.

The compile check needs Docker and the pinned Lean image; it is skipped without them.
Run: python3 tests/test_implement_mode.py
"""
import pathlib, re, shutil, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "agents")]
import judge, repair, task as taskmod  # noqa: E402


def tasks():
    return [t for t in taskmod.all_tasks() if (t.root / "spec/locked.json").exists()]


def challenge_of(t):
    return (t.root / t.spec_dir / "Challenge.lean").read_text()


def added_lines(t, stub):
    """Lines of the stub that do not occur in the locked challenge."""
    have = {l.strip() for l in challenge_of(t).splitlines()}
    return [l.strip() for l in stub.splitlines() if l.strip() and l.strip() not in have]


def test_stub_keeps_every_signature_and_statement():
    for t in tasks():
        stub = repair.stub_candidate(t)
        ch = challenge_of(t)
        for line in ch.splitlines():
            if re.match(r"^theorem\s+\S+\s*:", line):
                assert line in stub.splitlines(), (t.id, line)
        for d in t.definitions:
            want = re.search(rf"^def\s+{re.escape(d)}\s*:\s*([^\n]+?)\s*:=\s*sorry", ch, re.M).group(1)
            got = re.search(rf"^def\s+{re.escape(d)}\s*:\s*(.+?)\s*:=\s*(.+)$", stub, re.M)
            assert got and got.group(1) == want, (t.id, d)
            assert "sorry" not in got.group(2), (t.id, d)
        assert stub.count("theorem ") == len(t.theorems) and stub.count("sorry") == len(t.theorems), t.id
        assert f"namespace {t.ns}" in stub and f"end {t.ns}" in stub, t.id


def test_stub_uses_only_allowed_imports_and_no_forbidden_constructs():
    for t in tasks():
        stub = repair.stub_candidate(t)
        allowed = judge.allowed_imports(t)
        imports = re.findall(r"^import\s+(\S+)", stub, re.M)
        assert imports and all(allowed.match(i) for i in imports), (t.id, imports)
        if (t.root / t.spec_dir / "Lemmas.lean").exists():
            assert f"{t.lib}.Lemmas" in imports, t.id
        with tempfile.TemporaryDirectory() as tmp:
            f = pathlib.Path(tmp) / "Solution.lean"
            f.write_text(stub)
            assert judge.impl_scan([f], t)["passed"], t.id


def test_stub_body_is_a_neutral_placeholder():
    for t in tasks():
        lines = added_lines(t, repair.stub_candidate(t))
        defs = [l for l in lines if l.startswith("def ")]
        assert len(defs) == len(t.definitions), (t.id, lines)
        for l in defs:
            assert l.endswith("fun s _ => (Outcome.rejected, s)"), (t.id, l)


def test_stub_contains_no_reference_or_buggy_text():
    for t in tasks():
        stub = repair.stub_candidate(t)
        hidden = [p for d in ("reference", "attacks") for p in (t.root / d).glob("*.lean")] + [t.start]
        texts = {p: {l.strip() for l in p.read_text().splitlines()} for p in hidden}
        for line in added_lines(t, stub):
            if line.startswith(("import ", "--")):
                continue
            for p, have in texts.items():
                assert line not in have, (t.id, p.name, line)
        assert t.issue not in stub, t.id


def test_stub_is_generated_without_candidate_reference_or_attacks():
    for t in tasks()[:12]:
        with tempfile.TemporaryDirectory() as tmp:
            copy = pathlib.Path(tmp) / t.root.name
            shutil.copytree(t.root, copy, ignore=shutil.ignore_patterns(
                "candidate", "reference", "attacks", "oracle.py", ".lake"))
            assert repair.stub_candidate(taskmod.Task(copy)) == repair.stub_candidate(t), t.id


def test_implement_brief_has_no_issue_report_and_repair_brief_is_unchanged():
    for t in tasks():
        b = repair.task_brief(t, "implement")
        assert t.issue not in b and "Issue report" not in b, t.id
        assert f"{t.spec_dir}/Spec.lean is the source of truth" in b, t.id
        assert repair.task_brief(t) == repair.task_brief(t, "repair") and t.issue in repair.task_brief(t), t.id


def test_implement_workspace_holds_only_the_stub():
    t = taskmod.load("ledgers-log-b1")
    out = pathlib.Path(tempfile.mkdtemp())
    start = out / "start.lean"
    start.write_text(repair.stub_candidate(t))
    s = repair.Session(t, "none", start, out, mode="implement")
    try:
        assert s._source() == start.read_text()
        assert s._source() != t.start.read_text()
        assert not any("reference" in p.parts or "attacks" in p.parts for p in s.ws.rglob("*"))
    finally:
        shutil.rmtree(s.ws, ignore_errors=True)
        shutil.rmtree(out, ignore_errors=True)


def docker_ready():
    try:
        r = subprocess.run(["docker", "image", "inspect", judge.IMAGE], capture_output=True, timeout=30)
        return r.returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def test_stub_compiles_with_every_theorem_sorry():
    """One task per distinct test specification (variants of a base share the spec)."""
    if not docker_ready():
        try:
            import pytest
            pytest.skip("Docker or the pinned Lean image is not available")
        except ImportError:
            print("skip: Docker or the pinned Lean image is not available")
            return
    seen, picks = set(), []
    for t in taskmod.all_tasks("test"):
        if t.locked()["manifest_sha256"] not in seen:
            seen.add(t.locked()["manifest_sha256"])
            picks.append(t)
    for t in picks:
        out = pathlib.Path(tempfile.mkdtemp())
        start = out / "start.lean"
        start.write_text(repair.stub_candidate(t))
        s = repair.Session(t, "none", start, out, mode="implement")
        try:
            r = s.compile(4000)
            assert "error:" not in r["output_tail"], (t.id, r["output_tail"][-2000:])
            assert set(s.theorem_status().values()) == {"SORRY"}, t.id
        finally:
            shutil.rmtree(s.ws, ignore_errors=True)
            shutil.rmtree(out, ignore_errors=True)


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
