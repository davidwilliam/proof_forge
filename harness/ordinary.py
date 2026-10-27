"""Ordinary checking, the E2 baseline: what a repository without protected enforcement does.

The candidate's own project is built (candidate-supplied files, including spec files,
override the task's, as in an unprotected repository), every required theorem name must
exist, and `#print axioms` must show no sorry and only permitted axioms. Statements are not
compared with a locked challenge and the binary is not tested.
"""
import pathlib, re, shutil, sys, tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import judge, task as taskmod  # noqa: E402

PERMITTED = {"propext", "Quot.sound", "Classical.choice"}


def check(t, path):
    """Ordinary checking: build the candidate's own project and audit axioms by name."""
    ws = judge.load_workspace(str(path))
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-ordinary-"))
    for rel in taskmod.PROJECT_FILES:
        src = t.root / rel
        (shutil.copytree if src.is_dir() else shutil.copy)(src, d / rel)
    for f in ws.rglob("*"):
        if f.is_file() and ".lake" not in f.parts:
            dst = d / f.relative_to(ws)
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(f, dst)
    probe = "import Solution\n" + "\n".join(f"#print axioms {t.ns}.{x}" for x in t.theorems) + "\n"
    (d / "Audit.lean").write_text(probe)
    r = judge.in_container(d, "lake build Solution >/tmp/b.log 2>&1 || { tail -c 3000 /tmp/b.log; exit 3; }; "
                              "lake env lean Audit.lean 2>&1")
    shutil.rmtree(d, ignore_errors=True)
    if r["exit_code"] == 3:
        return {"accepted": False, "reason": "build failed"}
    out = r["output_tail"]
    for x in t.theorems:
        blk = re.search(rf"'{re.escape(t.ns)}\.{re.escape(x)}'(.*?)(?='{re.escape(t.ns)}\.|\Z)", out, re.S)
        if not blk:
            return {"accepted": False, "reason": f"{x} missing"}
        axioms = set(re.findall(r"[\w.]+", blk.group(1).split("axioms:")[-1])) if "axioms:" in blk.group(1) else set()
        if "sorryAx" in axioms:
            return {"accepted": False, "reason": f"{x} uses sorry"}
        if "error" in blk.group(1):
            return {"accepted": False, "reason": f"{x}: {blk.group(1).strip()[:120]}"}
        extra = axioms - PERMITTED - {"axioms", "depends", "on", "does", "not", "depend", "any"}
        if extra:
            return {"accepted": False, "reason": f"{x} uses axioms {sorted(extra)}"}
    return {"accepted": True, "reason": ""}
