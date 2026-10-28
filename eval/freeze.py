#!/usr/bin/env python3
"""Freeze the test set: record the hash of every file of every test task, so that the
final E1 runs can be checked against what was reviewed.

Usage: freeze.py --approvals approvals.json [--out results/test-freeze.json]
approvals.json maps each test base specification (task id without the -bN suffix) to the
owner's decision {"decision": "approve", ...}; every base must be approved.
"""
import argparse, hashlib, json, pathlib, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
sys.path.insert(0, str(ROOT / "eval"))
import task as taskmod  # noqa: E402
from e1 import base_of  # noqa: E402


def task_files(t):
    return {str(p.relative_to(t.root)): taskmod.sha256(p) for p in sorted(t.root.rglob("*"))
            if p.is_file() and ".lake" not in p.parts and "__pycache__" not in p.parts and p.name != "validation.json"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--approvals", required=True)
    ap.add_argument("--out", default=str(ROOT / "results" / "test-freeze.json"))
    a = ap.parse_args()
    approvals = json.loads(pathlib.Path(a.approvals).read_text())
    tests = taskmod.all_tasks("test")
    bases = sorted({base_of(t.id) for t in tests})
    missing = [b for b in bases if approvals.get(b, {}).get("decision") != "approve"]
    if missing:
        raise SystemExit(f"not approved: {missing}")
    for t in tests:
        v = json.loads((t.root / "validation.json").read_text())
        if not v.get("passed"):
            raise SystemExit(f"{t.id} does not validate")
    dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no", "--", "tasks"],
                           cwd=ROOT, capture_output=True, text=True).stdout.strip()
    if dirty:
        raise SystemExit("uncommitted changes under tasks/:\n" + dirty)
    record = {
        "frozen_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "git_commit": subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip(),
        "bases": {b: {"decision": approvals[b]["decision"], "notes": approvals[b].get("notes", ""),
                      "updatedAt": approvals[b].get("updatedAt")} for b in bases},
        "tasks": {t.id: {"manifest_sha256": t.locked()["manifest_sha256"], "files": task_files(t)} for t in tests},
    }
    record["freeze_sha256"] = hashlib.sha256(json.dumps(record["tasks"], sort_keys=True).encode()).hexdigest()
    pathlib.Path(a.out).write_text(json.dumps(record, indent=2) + "\n")
    print(f"froze {len(tests)} test tasks from {len(bases)} approved bases: {record['freeze_sha256']}")


if __name__ == "__main__":
    main()
