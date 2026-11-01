#!/usr/bin/env python3
"""Run a queue of Muse Code runs (agents/muse_code.py), at most N at a time, with equal caps.

At most N runs of agents/muse_code.py run on the host at once, counting runs started elsewhere.
Each item is TASK:ARM:N[:DIR,DIR...] and writes <results>/<TASK>/<ARM>-<N>/; the optional fourth
field is the run directories the run resumes from (`--resume-from`). An item whose summary.json
exists is skipped. The arms are interleaved in the given order so that they see the same host
load.

Usage: measure.py [--parallel 4] [--results results/muse-code-1] [--budget-usd 10]
                  [--budget-wall 14400] TASK:ARM:N[:RESUME_DIRS] ...
"""
import argparse, os, pathlib, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parents[2]


def active():
    """Runs of agents/muse_code.py on this host, including those started outside this queue."""
    r = subprocess.run(["ps", "-axo", "command="], capture_output=True, text=True)
    return sum(1 for line in r.stdout.splitlines()
               if "agents/muse_code.py" in line and pathlib.Path(line.split()[0]).name.lower().startswith("python"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("items", nargs="+")
    ap.add_argument("--parallel", type=int, default=4)
    ap.add_argument("--results", default="results/muse-code-1")
    ap.add_argument("--budget-usd", default="10")
    ap.add_argument("--budget-wall", default="14400")
    a = ap.parse_args()
    queue = []
    for item in a.items:
        task, arm, n, *resume = item.split(":", 3)
        out = ROOT / a.results / task / f"{arm}-{n}"
        if (out / "summary.json").is_file():
            print(f"skip {item}: done", flush=True)
            continue
        queue.append((item, task, arm, out, resume[0] if resume else None))
    logs = ROOT / "runs" / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    running = {}
    while queue or running:
        while queue and active() < a.parallel:
            item, task, arm, out, resume = queue.pop(0)
            log = (logs / f"{task}-{out.name}.log").open("w")
            p = subprocess.Popen([sys.executable, str(ROOT / "agents/muse_code.py"), "--task", task, "--arm", arm,
                                  "--budget-usd", a.budget_usd, "--budget-wall", a.budget_wall, "--out", str(out)]
                                 + (["--resume-from", resume] if resume else []),
                                 stdout=log, stderr=subprocess.STDOUT, cwd=ROOT, env=os.environ.copy())
            running[item] = p
            print(f"{time.strftime('%H:%M:%S')} start {item}", flush=True)
            time.sleep(3)
        for item, p in list(running.items()):
            if p.poll() is not None:
                print(f"{time.strftime('%H:%M:%S')} done {item} exit {p.returncode}", flush=True)
                del running[item]
        time.sleep(10)


if __name__ == "__main__":
    main()
