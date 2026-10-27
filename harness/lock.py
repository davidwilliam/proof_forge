#!/usr/bin/env python3
"""Owner-only: hash a task's protected files and write its spec/locked.json.

Run after reviewing the spec and challenge. The judge refuses any workspace whose
protected files don't match these hashes.

Usage: lock.py [TASK]   (default: the flagship task in formal/)
"""
import hashlib, json, pathlib, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import task as taskmod  # noqa: E402


def manifest(task) -> dict:
    return {rel: taskmod.sha256(task.root / rel) for rel in task.protected()}


if __name__ == "__main__":
    t = taskmod.load(sys.argv[1] if len(sys.argv) > 1 else None)
    files = manifest(t)
    digest = hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()
    out = {"schema_version": 1, "files": files, "manifest_sha256": digest}
    (t.root / "spec" / "locked.json").write_text(json.dumps(out, indent=2) + "\n")
    print(f"{t.id}: locked {len(files)} files, manifest_sha256={digest}")
