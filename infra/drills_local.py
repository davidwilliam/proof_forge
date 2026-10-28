#!/usr/bin/env python3
"""Failure drills on the local judge (needs Docker and the pinned Lean image): an edited or
stale Passport, source changed after the check, and a missing or modified Comparator
configuration. A drill passes when the outcome is an honest status or an explicit refusal:
never VERIFIED for a bad setup and never "reproduced" for a Passport that does not match.

Usage: infra/drills_local.py [--out reports/drills/local-<n>.json]
"""
import argparse, json, pathlib, shutil, subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import passport  # noqa: E402

GOOD = ROOT / "formal/evidence/muse-repair-002/Solution.lean"
BUGGY = ROOT / "formal/attacks/buggy_original.lean"


def cli(args, root=ROOT):
    t0 = time.time()
    p = subprocess.run([sys.executable, str(root / "bin/proofforge"), *map(str, args)],
                       cwd=root, capture_output=True, text=True)
    out = p.stdout + p.stderr
    return p.returncode, out, round(time.time() - t0, 1)


def staged_checkout(work):
    """A copy of the committed tree, as a trusted checker checkout would be."""
    dest = work / "checkout"
    dest.mkdir()
    archive = subprocess.run(["git", "-C", str(ROOT), "archive", "HEAD"], capture_output=True, check=True).stdout
    subprocess.run(["tar", "-x", "-C", str(dest)], input=archive, check=True)
    return dest


def rehash(p):
    p["passport_sha256"] = passport.content_hash(p)
    return p


def tail(out, n=4):
    return [line for line in out.strip().splitlines() if line.strip()][-n:]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    a = ap.parse_args()
    work = pathlib.Path(tempfile.mkdtemp(prefix="pf-local-drills-"))
    results = []

    def record(name, expected, code, out, secs, passed):
        results.append({"drill": name, "expected": expected, "exit_code": code, "seconds": secs,
                        "output_tail": tail(out), "passed": bool(passed)})
        print(f"{'PASS' if passed else 'FAIL'}  {name}  exit {code}  {secs} s")

    # Control: a correct repair is VERIFIED and its Passport reproduces.
    pp = work / "passport.json"
    code, out, secs = cli(["check", "--candidate", GOOD, "--out", pp])
    record("control: check a correct repair", "exit 0, VERIFIED", code, out, secs,
           code == 0 and json.loads(pp.read_text())["status"] == "VERIFIED")
    code, out, secs = cli(["verify", pp, "--candidate", GOOD])
    record("control: reproduce its Passport", "exit 0, reproduced", code, out, secs,
           code == 0 and out.strip().endswith("reproduced"))
    issued = json.loads(pp.read_text())

    # A Passport edited after it was issued, without recomputing its content hash.
    edited = json.loads(json.dumps(issued))
    edited["executable"]["sha256"] = "0" * 64
    (work / "edited.json").write_text(json.dumps(edited, indent=2))
    code, out, secs = cli(["verify", work / "edited.json", "--candidate", GOOD])
    record("Passport edited after issue", "exit 1, content hash differs", code, out, secs,
           code == 1 and "content hash differs" in out)

    # A stale Passport: issued under an earlier lock and statement, internally consistent.
    stale = json.loads(json.dumps(issued))
    stale["locked"]["manifest_sha256"] = "1" * 64
    stale["requirements"][4]["statement_sha256"] = "2" * 64
    (work / "stale.json").write_text(json.dumps(rehash(stale), indent=2))
    code, out, secs = cli(["verify", work / "stale.json", "--candidate", GOOD])
    record("stale Passport from an earlier lock", "exit 1, manifest and statement DIFFERENT", code, out, secs,
           code == 1 and "DIFFERENT  locked manifest" in out and "statement" in out and "NOT reproduced" in out)

    # Source changed after the check: a comment only, then the buggy code.
    commented = work / "commented.lean"
    commented.write_text(GOOD.read_text() + "\n-- edited after the check\n")
    code, out, secs = cli(["verify", pp, "--candidate", commented])
    record("source changed after check (comment only)", "exit 1, solution tree DIFFERENT", code, out, secs,
           code == 1 and "DIFFERENT  solution tree" in out)
    code, out, secs = cli(["verify", pp, "--candidate", BUGGY])
    record("source changed after check (buggy code)", "exit 1, statuses DIFFERENT", code, out, secs,
           code == 1 and "DIFFERENT  component status" in out)

    # Comparator configuration missing from the trusted checkout.
    checkout = staged_checkout(work)
    (checkout / "formal/spec/comparator.json").unlink()
    code, out, secs = cli(["check", "--candidate", GOOD, "--out", work / "missing.json"], root=checkout)
    status = json.loads((work / "missing.json").read_text())["status"] if (work / "missing.json").exists() else None
    record("comparator config missing", "nonzero exit, not VERIFIED, missing file named", code, out, secs,
           code != 0 and status not in (None, "VERIFIED") and "protected file missing: spec/comparator.json" in out)

    # Comparator configuration widened in the trusted checkout (sorryAx permitted).
    shutil.rmtree(checkout)
    checkout = staged_checkout(work)
    cfg = checkout / "formal/spec/comparator.json"
    c = json.loads(cfg.read_text())
    c["permitted_axioms"].append("sorryAx")
    cfg.write_text(json.dumps(c, indent=2) + "\n")
    code, out, secs = cli(["check", "--candidate", GOOD, "--out", work / "widened.json"], root=checkout)
    status = json.loads((work / "widened.json").read_text())["status"] if (work / "widened.json").exists() else None
    record("comparator config widened in the checkout", "nonzero exit, not VERIFIED", code, out, secs,
           code != 0 and status != "VERIFIED")

    # A candidate workspace that ships its own widened configuration.
    ws = work / "workspace"
    (ws / "spec").mkdir(parents=True)
    (ws / "candidate").mkdir()
    shutil.copy(GOOD, ws / "candidate/Solution.lean")
    (ws / "spec/comparator.json").write_text(json.dumps(c, indent=2) + "\n")
    code, out, secs = cli(["check", "--candidate", ws, "--out", work / "shipped.json"])
    status = json.loads((work / "shipped.json").read_text())["status"] if (work / "shipped.json").exists() else None
    record("candidate ships its own comparator config", "nonzero exit, not VERIFIED", code, out, secs,
           code != 0 and status != "VERIFIED")

    report = {"recorded_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
              "passed": all(r["passed"] for r in results), "results": results}
    if a.out:
        pathlib.Path(a.out).parent.mkdir(parents=True, exist_ok=True)
        pathlib.Path(a.out).write_text(json.dumps(report, indent=2) + "\n")
    shutil.rmtree(work, ignore_errors=True)
    raise SystemExit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
