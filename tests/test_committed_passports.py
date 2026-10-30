"""Every committed Passport's passport_sha256 matches its content; no model or Docker calls.

A Passport edited after issue (for example by text normalization) no longer reproduces, so this
check guards the committed record. It reads every tracked passport JSON under results/ and formal/.
"""
import json, pathlib, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "harness"))
import passport


def committed_passports():
    out = subprocess.run(["git", "ls-files", "results", "formal"], cwd=ROOT, capture_output=True, text=True, check=True).stdout
    for rel in out.split():
        if rel.endswith(".json") and ("passport" in pathlib.Path(rel).name or "/passports/" in rel):
            data = json.loads((ROOT / rel).read_text())
            if isinstance(data, dict) and "passport_sha256" in data:
                yield rel, data


def test_every_committed_passport_matches_its_content_hash():
    found = list(committed_passports())
    assert len(found) >= 50, len(found)
    bad = [rel for rel, p in found if p["passport_sha256"] != passport.content_hash(p)]
    assert not bad, bad


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
