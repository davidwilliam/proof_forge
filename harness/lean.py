#!/usr/bin/env python3
"""Run a shell command inside the pinned Lean image for a project directory, sharing the
judge's container slots. For authoring and debugging; statuses come only from judge.py.

Usage: lean.py <project-dir> [command]   (default command: lake build Solution)
"""
import pathlib, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import judge  # noqa: E402

if __name__ == "__main__":
    project = pathlib.Path(sys.argv[1]).resolve()
    cmd = sys.argv[2] if len(sys.argv) > 2 else "lake build Solution"
    r = judge.in_container(project, f"{cmd} 2>&1 | tail -c 12000", timeout=900)
    print(r["output_tail"])
    print(f"[exit {r['exit_code']}, {r['elapsed_ms']} ms]")
