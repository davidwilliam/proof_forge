"""Isolation checks: what agents can see.

Run: python3 tests/test_isolation.py
"""
import pathlib, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "agents")]
import repair, task as taskmod  # noqa: E402


def test_workspace_excludes_hidden_material():
    for t in taskmod.all_tasks():
        if not (t.root / "spec/locked.json").exists():
            continue
        s = repair.Session(t, "none", t.start, pathlib.Path(tempfile.mkdtemp()))
        names = {p.relative_to(s.ws).parts[0] for p in s.ws.rglob("*")}
        assert names <= {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "spec", "app", "candidate"}, (t.id, names)
        for p in s.ws.rglob("*"):
            assert "reference" not in p.parts and "attacks" not in p.parts and p.name != "oracle.py", (t.id, p)
        assert sorted(p.name for p in (s.ws / "candidate").iterdir()) == ["Solution.lean"], t.id


def test_readable_files_are_spec_and_candidate_only():
    for t in taskmod.all_tasks():
        for r in t.readable:
            assert r.startswith("spec/") or r == "candidate/Solution.lean", (t.id, r)


def test_hidden_variants_not_listed():
    ids = {t.id for t in taskmod.all_tasks()}
    assert not any(i.endswith(("-h1", "-h2", "-h3")) for i in ids), ids


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
