#!/usr/bin/env python3
"""Freeze the test set: record the hash of every file of every test task, so that the
final E1 runs can be checked against what was reviewed.

Usage: freeze.py --approvals approvals.json [--out results/test-freeze.json]
approvals.json maps each test base specification (task id without the -bN suffix) to the
owner's decision {"decision": "approve", ...}; every base must be approved.
"""
import argparse, hashlib, io, json, pathlib, subprocess, sys, tarfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
sys.path.insert(0, str(ROOT / "eval"))
import task as taskmod  # noqa: E402


def base_of(task_id):
    parts = task_id.rsplit("-", 1)
    return parts[0] if len(parts) == 2 and parts[1][:1] == "b" and parts[1][1:].isdigit() else task_id


def task_files(t):
    return {str(p.relative_to(t.root)): taskmod.sha256(p) for p in sorted(t.root.rglob("*"))
            if p.is_file() and ".lake" not in p.parts and "__pycache__" not in p.parts and p.name != "validation.json"}


def validation_receipt(t):
    """Bind an existing validation report to the unchanged task snapshot committed with it.

    This is provenance for recorded validation, not a claim of rerunning Lean now.
    Changed or untracked inputs require a new validated, committed snapshot.
    """
    report = t.root / "validation.json"
    if not json.loads(report.read_text()).get("passed"):
        raise ValueError(f"{t.id}: validation did not pass")
    rel = t.root.relative_to(ROOT).as_posix()
    commit = subprocess.check_output(
        ["git", "log", "-1", "--format=%H", "--", f"{rel}/validation.json"], cwd=ROOT, text=True).strip()
    if not commit:
        raise ValueError(f"{t.id}: validation report has not been committed")
    archive = subprocess.check_output(["git", "archive", commit, "--", rel], cwd=ROOT)
    recorded = {}
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        for member in tar.getmembers():
            if member.isfile():
                name = member.name.removeprefix(rel + "/")
                recorded[name] = hashlib.sha256(tar.extractfile(member).read()).hexdigest()
    if recorded.pop("validation.json", None) != taskmod.sha256(report) or recorded != task_files(t):
        raise ValueError(f"{t.id}: files differ from the committed validation snapshot; revalidate and commit")
    return {"commit": commit, "report_sha256": taskmod.sha256(report)}


def verify_record(path, tasks):
    """Fail closed before model calls unless selected test tasks match the approved freeze."""
    record = json.loads(pathlib.Path(path).read_text())
    digest = hashlib.sha256(json.dumps(record["tasks"], sort_keys=True).encode()).hexdigest()
    if digest != record.get("freeze_sha256"):
        raise ValueError("freeze hash does not match its task records")
    for t in tasks:
        if t.split != "test":
            continue
        if record.get("bases", {}).get(base_of(t.id), {}).get("decision") != "approve":
            raise ValueError(f"{t.id}: base specification not approved")
        saved = record["tasks"].get(t.id)
        if not saved or saved.get("files") != task_files(t) or saved.get("manifest_sha256") != t.locked()["manifest_sha256"]:
            raise ValueError(f"{t.id}: task differs from approved freeze")
        receipt = saved.get("validation", {})
        if receipt.get("report_sha256") != taskmod.sha256(t.root / "validation.json"):
            raise ValueError(f"{t.id}: validation receipt differs from approved freeze")
        if not json.loads((t.root / "validation.json").read_text()).get("passed"):
            raise ValueError(f"{t.id}: validation did not pass")
    return taskmod.sha256(pathlib.Path(path))


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
    receipts = {t.id: validation_receipt(t) for t in tests}
    dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no", "--", "tasks"],
                           cwd=ROOT, capture_output=True, text=True).stdout.strip()
    if dirty:
        raise SystemExit("uncommitted changes under tasks/:\n" + dirty)
    record = {
        "frozen_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "git_commit": subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip(),
        "bases": {b: {"decision": approvals[b]["decision"], "notes": approvals[b].get("notes", ""),
                      "updatedAt": approvals[b].get("updatedAt")} for b in bases},
        "tasks": {t.id: {"manifest_sha256": t.locked()["manifest_sha256"], "files": task_files(t),
                         "validation": receipts[t.id]} for t in tests},
    }
    record["freeze_sha256"] = hashlib.sha256(json.dumps(record["tasks"], sort_keys=True).encode()).hexdigest()
    pathlib.Path(a.out).write_text(json.dumps(record, indent=2) + "\n")
    print(f"froze {len(tests)} test tasks from {len(bases)} approved bases: {record['freeze_sha256']}")


if __name__ == "__main__":
    main()
