#!/usr/bin/env python3
"""Arm A0 (E1 baseline): compile-and-retry.

The model receives the task brief, the protected spec and the buggy candidate, and replies
with a complete candidate/Solution.lean. The harness compiles it and returns only what
ordinary checking gives: Lean errors, or, when the file compiles, the axiom audit of each
required theorem (`#print axioms`) and the implementation-scan violations. No tests, no
snippets, no planner. It repeats until the official judge accepts or the budget runs out.

Usage: baseline.py [--task T] [--model M] [--budget-usd X] [--budget-wall S] [--out DIR]
"""
import argparse, json, pathlib, re, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "agents"))
sys.path.insert(0, str(ROOT / "harness"))
from meta_client import APIError  # noqa: E402
from budget import Budget, BudgetExceeded  # noqa: E402
import repair, task as taskmod  # noqa: E402

PROTOCOL = """

Protocol: reply with the complete content of candidate/Solution.lean in exactly one ```lean code block. The harness compiles it and replies with the Lean errors, or, if it compiles, with the axiom audit of each required theorem. Then reply with a corrected complete file. Repeat until the file is accepted."""
KEEP_FILES = 3   # most recent assistant files kept verbatim in the conversation


class FileSession(repair.Session):
    def _normalize(self, text):   # A0 gets no declaration reordering
        return text


def audit(s):
    """Ordinary checking: compile, then `#print axioms` per required theorem, plus the scan."""
    r = s.compile(16000)
    text = s._clean(r["output_tail"])
    if "error:" in text:
        return False, "The file does not compile. Lean output:\n" + text[-7000:]
    scan = repair.judge.impl_scan([s.ws / "candidate/Solution.lean"], s.task)
    status = s.theorem_status()
    lines = [f"{t}: {'uses sorry' if v == 'SORRY' else 'missing' if v == 'MISSING' else 'no sorry'}"
             for t, v in status.items()]
    if scan["problems"]:
        lines.append("Rule violations:\n" + "\n".join(scan["problems"]))
    if any(v != "PROVED" for v in status.values()) or scan["problems"]:
        return False, "The file compiles. Axiom audit:\n" + "\n".join(lines)
    verdict = s.check()
    return s.accepted, verdict


def run(s, a, state="current, buggy", track_best=False):
    """Compile-and-retry loop. With track_best (the harness's whole-file phase), feedback on an
    attempt that proves fewer required theorems than the best version so far says so; the
    baseline arm A0 runs without it."""
    system = repair.task_brief(s.task, getattr(s, "mode", "repair")) + PROTOCOL
    user = (repair.spec_text(s) + f"\n\n=== candidate/Solution.lean ({state}) ===\n" + s._source())
    messages = [{"role": "system", "content": system}, {"role": "user", "content": user}]
    extra = {} if a.effort == "default" else {"reasoning_effort": a.effort}
    for turn in range(a.max_turns):
        try:
            r, u = s.call(a.model, messages, f"baseline:{s.task.id}:turn{turn}", **extra)
        except APIError as e:
            s.log(kind="api_error", status=e.status, body=e.body[:300])
            if e.status in (0, 429, 500, 502, 503, 504):
                s.pause(20)
                continue
            return
        text = r["choices"][0]["message"].get("content") or ""
        messages.append({"role": "assistant", "content": text})
        m = re.findall(r"```lean\s*\n(.*?)```", text, re.S)
        if not m:
            feedback = "Your reply had no ```lean code block. Reply with the complete file."
        else:
            s._save(m[-1].strip() + "\n", "attempt")
            ok, feedback = audit(s)
            if track_best and not ok and s.best and s.best[1] != s.version:
                feedback += (f"\n\nThe best version so far (version {s.best[1]}) proves {s.best[0]} of "
                             f"{len(s.theorems)} required theorems; it remains the result unless a later version "
                             "proves more. Keep the proofs that worked there.")
            s.log(kind="attempt", turn=turn, version=s.version, accepted=ok,
                  **({"best": s.best_score()} if track_best else {}))
            print(f"[A0] turn {turn}: version {s.version} accepted={ok}", flush=True)
            if ok:
                return
        messages.append({"role": "user", "content": feedback})
        # Elide older files so the conversation stays bounded; the latest ones stay verbatim.
        files = [i for i, msg in enumerate(messages) if msg["role"] == "assistant" and "```lean" in msg["content"]]
        for i in files[:-KEEP_FILES]:
            messages[i] = {"role": "assistant", "content": "[earlier attempt omitted]"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--task")
    ap.add_argument("--model", default="muse-spark-1.3-contributor")
    ap.add_argument("--effort", default="medium", choices=["low", "medium", "high", "default"])
    ap.add_argument("--max-turns", type=int, default=200)
    ap.add_argument("--budget-usd", type=float)
    ap.add_argument("--budget-wall", type=float)
    ap.add_argument("--out")
    a = ap.parse_args()
    task = taskmod.load(a.task)
    out = pathlib.Path(a.out) if a.out else ROOT / "runs" / f"repair-{time.strftime('%Y%m%d-%H%M%S')}-{task.id}-A0"
    out.mkdir(parents=True, exist_ok=True)
    s = FileSession(task, a.model, task.start, out, Budget(a.budget_usd, a.budget_wall))
    s.log(kind="start", arm="A0", **vars(a))
    try:
        run(s, a)
    except BudgetExceeded as e:
        s.log(kind="budget_stop", reason=str(e))
        print(f"budget exhausted: {e}", flush=True)
    print(json.dumps(repair.finish(s, out, "A0", {"effort": a.effort})))


if __name__ == "__main__":
    main()
