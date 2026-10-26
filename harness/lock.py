#!/usr/bin/env python3
"""Owner-only: hash the protected files and write spec/locked.json.

Run after reviewing the spec and challenge. The judge refuses any workspace whose
protected files don't match these hashes.
"""
import hashlib, json, pathlib, sys

FORMAL = pathlib.Path(__file__).resolve().parent.parent / "formal"
PROTECTED = [
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "spec/Payout/Spec.lean",
    "spec/Payout/Lemmas.lean",
    "spec/Payout/Challenge.lean",
    "spec/comparator.json",
    "app/Main.lean",
]


def sha256(p: pathlib.Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def manifest(root: pathlib.Path) -> dict:
    return {rel: sha256(root / rel) for rel in PROTECTED}


if __name__ == "__main__":
    files = manifest(FORMAL)
    digest = hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()
    out = {"schema_version": 1, "files": files, "manifest_sha256": digest}
    (FORMAL / "spec" / "locked.json").write_text(json.dumps(out, indent=2) + "\n")
    print(f"locked {len(files)} files, manifest_sha256={digest}")
    sys.exit(0)
