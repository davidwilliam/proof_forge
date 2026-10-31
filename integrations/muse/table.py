#!/usr/bin/env python3
"""Markdown table of Muse Code runs from their summary.json files.

Usage: table.py <results-dir>   (each run in <results-dir>/<task>/<run>/summary.json)
"""
import json, pathlib, re, sys

ARM = {"alone": "Muse Code alone", "proofforge": "Muse Code + ProofForge"}


def rows(base):
    for f in sorted(pathlib.Path(base).glob("*/*/summary.json")):
        if not re.fullmatch(r"(alone|proofforge)-\d+", f.parent.name):   # measured runs only
            continue
        s = json.loads(f.read_text())
        p = s.get("passport") or {}
        m = s["meter"]
        n = len(p.get("requirements") or {}) or len(s.get("final_theorem_status") or {})
        last = f.parent / "last_compiling.json"
        proved = (f"{p.get('verified', 0)}/{n}" if p.get("status") == "VERIFIED" else
                  f"{s.get('requirements_proved_in_run', 0)}/{n}" if s.get("final_theorem_status") else
                  "{proved}/{required} last compiling".format(**json.loads(last.read_text())) if last.is_file() else f"0/{n}")
        yield {
            "task": s["task"], "run": f.parent.name, "arm": ARM.get(s["arm"], s["arm"]),
            "outcome": p.get("status", "not checked"),
            "proved": proved,
            "time": f"{s['elapsed_s']:,.0f}",
            "list": f"{m['usd_list']:.2f}", "charged": f"{m['usd_actual']:.2f}",
            "calls": f"{m['calls']} ({s.get('main_agent_calls', 0)})",
            "stop": {"accepted": "", "usd": "dollars", "wall": "wall"}.get(s["ended_by"], s["ended_by"]),
            "passport": (p.get("passport_sha256") or "")[:16] if p.get("status") == "VERIFIED" else "",
        }


def main():
    base = sys.argv[1] if len(sys.argv) > 1 else "results/muse-code-1"
    head = ["Task", "Run", "Arm", "Outcome", "Requirements proved", "Time s", "List $", "Charged $",
            "Model calls (main agent)", "Stop", "Passport"]
    print("| " + " | ".join(head) + " |")
    print("|" + "---|" * len(head))
    for r in rows(base):
        print("| " + " | ".join([r["task"], r["run"], r["arm"], r["outcome"], r["proved"], r["time"], r["list"],
                                 r["charged"], r["calls"], r["stop"], f"`{r['passport']}`" if r["passport"] else ""]) + " |")


if __name__ == "__main__":
    main()
