#!/usr/bin/env python3
"""The newest compiling snapshot of a Muse Code run, and its sorry status.

The runner judges the file on disk when a run stops (`final.lean`); a run stopped by a cap can
stop in the middle of an edit, with a file that does not compile. For such runs this reports,
without changing the run's outcome, the newest snapshot (`candidate_vNNN.lean`, saved whenever
the file changed) that compiles in the arm's workspace, and the status of each required theorem
in it (PROVED, SORRY, MISSING), as `last_compiling.json` in the run directory. The A0, A1 and A2
agents report the same quantity for their newest compiling version.

Usage: last_compiling.py RUN_DIR...
"""
import json, pathlib, shutil, sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse")]
import muse_code, proofforge_mcp  # noqa: E402
import task as taskmod  # noqa: E402


def main():
    for run in map(pathlib.Path, sys.argv[1:]):
        s = json.loads((run / "summary.json").read_text())
        t = taskmod.load(s["task"])
        snaps = sorted(run.glob("candidate_v*.lean"), reverse=True)
        ws = muse_code.make_workspace(t, s["arm"])
        server = proofforge_mcp.Server(ws, t.id, "lean")
        found = None
        for snap in snaps:
            shutil.copy(snap, ws / "candidate/Solution.lean")
            r = server.lean("lake build Solution 2>&1 | tail -c 4000")
            if muse_code.unavailable(r):   # Docker failure or time limit: no verdict, so no result
                sys.exit(f"{run}: Lean gave no verdict on {snap.name}; rerun when Docker is available")
            if "error:" not in proofforge_mcp.clean_lean(r["output_tail"]) and r["exit_code"] == 0:
                status = server.theorem_status(t)
                found = {"snapshot": snap.name, "of": len(snaps), "theorem_status": status,
                         "proved": sum(v == "PROVED" for v in status.values()), "required": len(status)}
                break
        rec = found or {"snapshot": None, "of": len(snaps), "proved": 0, "required": len(t.theorems)}
        (run / "last_compiling.json").write_text(json.dumps(rec, indent=2) + "\n")
        print(run, rec.get("snapshot"), f"{rec['proved']}/{rec['required']}", flush=True)
        shutil.rmtree(ws, ignore_errors=True)


if __name__ == "__main__":
    main()
