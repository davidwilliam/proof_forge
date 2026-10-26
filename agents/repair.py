#!/usr/bin/env python3
"""Repair agent v0: a Meta model fixes `Payout.step` and proves the locked requirements.

The agent works in its own sandbox workspace (a copy of formal/ without reference
solutions). It can read the protected spec, replace candidate/Solution.lean, compile it,
and run binary property tests. Acceptance is decided only by harness/judge.py.

Usage: repair.py [--model muse-spark-1.3-contributor] [--max-turns 40] [--start FILE]
"""
import argparse, json, pathlib, re, shutil, subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "agents"))
sys.path.insert(0, str(ROOT / "harness"))
from meta_client import chat, APIError  # noqa: E402
import judge, binary_check  # noqa: E402

READABLE = ["spec/Payout/Spec.lean", "spec/Payout/Lemmas.lean", "spec/Payout/Challenge.lean",
            "candidate/Solution.lean"]
THEOREMS = ["req_valid_succeeds", "req_invalid_noop", "req_fair_shares", "req_effects",
            "req_conservation", "req_nonnegative", "req_authorization", "req_idempotency"]

SYSTEM = """You are a software repair agent working in Lean 4 (v4.35.0, core library only, no Mathlib).

A payout routine `Payout.step` in candidate/Solution.lean has a bug: the existing unit tests pass, but when an amount does not divide evenly among recipients, cents disappear. Your job:
1. Fix `Payout.step` so it satisfies the locked requirements in spec/Payout/Spec.lean.
2. Prove all eight theorems of spec/Payout/Challenge.lean in candidate/Solution.lean, with exactly the same names and statements, and no `sorry`.

Rules (enforced by an independent judge; violations are rejected):
- Never edit files under spec/. You may only replace candidate/Solution.lean.
- candidate/Solution.lean must define `Payout.step : Impl` and the eight theorems in `namespace Payout`.
- Allowed imports: Payout.Spec, Payout.Lemmas, Init.*, Std.*.
- Forbidden: sorry, axiom, opaque, implemented_by, extern, unsafe, export, macro, elab, syntax, initialize, #eval, run_cmd, native_decide, set_option.
- Weakening or restating a theorem differently is rejected. Changing behavior to avoid hard inputs (for example rejecting valid payouts) cannot satisfy REQ-VALID-SUCCEEDS.
- Payout.Lemmas contains proved helper lemmas you may use (sumOver_add, sumOver_sub, sumOver_congr, sumOver_ite_eq, indexOf?_eq_none, indexOf?_getElem).

Workflow: read the spec, write a full candidate with write_solution, call check, fix errors, repeat. Prove helper lemmas first. Use run_tests to see concrete counterexamples on the compiled binary. Stop when check reports ACCEPTED."""

TOOLS = [
    {"type": "function", "function": {"name": "read_file", "description": "Read a file from the workspace.",
     "parameters": {"type": "object", "properties": {"path": {"type": "string", "enum": READABLE}}, "required": ["path"]}}},
    {"type": "function", "function": {"name": "write_solution", "description": "Replace candidate/Solution.lean with the full given content.",
     "parameters": {"type": "object", "properties": {"content": {"type": "string"}}, "required": ["content"]}}},
    {"type": "function", "function": {"name": "check", "description": "Compile candidate/Solution.lean. Returns Lean errors with goal states, remaining sorries and rule violations. If it compiles cleanly, runs the official judge and returns ACCEPTED or the rejection reason.",
     "parameters": {"type": "object", "properties": {}}}},
    {"type": "function", "function": {"name": "run_tests", "description": "Build the executable from the current candidate and run property tests against the requirements. Returns violated requirements and counterexamples.",
     "parameters": {"type": "object", "properties": {}}}},
]


class Session:
    def __init__(self, model, start, out):
        self.model, self.out = model, out
        self.ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-repair-"))
        for rel in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "spec", "app"]:
            src = ROOT / "formal" / rel
            (shutil.copytree if src.is_dir() else shutil.copy)(src, self.ws / rel)
        (self.ws / "candidate").mkdir()
        shutil.copy(start, self.ws / "candidate/Solution.lean")
        self.version = 0
        self.accepted = False
        self.events = []

    def log(self, **kw):
        kw["t"] = round(time.time(), 3)
        self.events.append(kw)
        with (self.out / "events.jsonl").open("a") as f:
            f.write(json.dumps(kw) + "\n")

    def read_file(self, path):
        if path not in READABLE:
            return "error: not readable"
        return (self.ws / path).read_text()

    def write_solution(self, content):
        if len(content) > 80_000:
            return "error: file too large"
        self.version += 1
        (self.ws / "candidate/Solution.lean").write_text(content)
        (self.out / f"candidate_v{self.version:03d}.lean").write_text(content)
        self.log(kind="write", version=self.version, bytes=len(content))
        return f"written (version {self.version}, {len(content)} bytes)"

    def check(self):
        files = [self.ws / "candidate/Solution.lean"]
        scan = judge.impl_scan(files)
        r = judge.in_container(self.ws, "lake build Solution 2>&1 | grep -v '^✔' | tail -c 12000", timeout=600)
        text = r["output_tail"]
        errors = "error:" in text
        sorries = re.findall(r"declaration uses `sorry`", text)
        self.log(kind="check", version=self.version, errors=errors, sorries=len(sorries),
                 scan=scan["problems"], ms=r["elapsed_ms"])
        if errors or sorries or not scan["passed"]:
            msg = text[-8000:]
            if scan["problems"]:
                msg = "RULE VIOLATIONS:\n" + "\n".join(scan["problems"]) + "\n\n" + msg
            return "NOT ACCEPTED (compile stage)\n" + msg
        j = judge.judge(str(self.ws / "candidate/Solution.lean"))
        self.log(kind="judge", version=self.version, accepted=j["accepted"], ms=j["elapsed_ms"])
        (self.out / f"judge_v{self.version:03d}.json").write_text(json.dumps(j, indent=2))
        if j["accepted"]:
            self.accepted = True
            return "ACCEPTED by the official judge (comparator + leanchecker). All eight requirements VERIFIED."
        cmp_ = j["checks"].get("comparator", {}).get("output_tail", "")
        reasons = j["checks"]["tree"]["problems"] + j["checks"]["impl_scan"]["problems"]
        return "NOT ACCEPTED by judge: " + "; ".join(reasons) + "\n" + "\n".join(
            l for l in cmp_.splitlines() if "error" in l.lower())[-3000:]

    def run_tests(self):
        b = binary_check.check_binary(str(self.ws / "candidate/Solution.lean"), n_cases=300, seed=self.version)
        self.log(kind="tests", version=self.version, status=b["status"], violations=b.get("violations"))
        if b["status"] == "BUILD_FAILED":
            return "executable build failed:\n" + b["build"].get("output_tail", "")[-3000:]
        ws = [{"requirement": w["requirement"], "message": w["message"],
               "request": w["input"]["request"], "state_in": w["input"]["state"],
               "outcome": w["output"].get("outcome"), "state_out": w["output"].get("state")}
              for w in b["witnesses"][:3]]
        return json.dumps({"status": b["status"], "violations": b["violations"], "examples": ws})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="muse-spark-1.3-contributor")
    ap.add_argument("--max-turns", type=int, default=40)
    ap.add_argument("--start", default=str(ROOT / "formal/attacks/buggy_original.lean"))
    a = ap.parse_args()
    out = ROOT / "runs" / f"repair-{time.strftime('%Y%m%d-%H%M%S')}-{a.model}"
    out.mkdir(parents=True)
    s = Session(a.model, a.start, out)
    s.log(kind="start", model=a.model, start=a.start, max_turns=a.max_turns)
    messages = [{"role": "system", "content": SYSTEM},
                {"role": "user", "content": "Begin. The current candidate is candidate/Solution.lean."}]
    t0 = time.monotonic()
    usage = {"prompt": 0, "completion": 0, "cached": 0}
    for turn in range(a.max_turns):
        try:
            r = chat(a.model, messages, f"repair:turn{turn}", tools=TOOLS, max_tokens=32000, timeout=600)
        except APIError as e:
            s.log(kind="api_error", status=e.status, body=e.body[:300])
            if e.status in (429, 500, 502, 503):
                time.sleep(20); continue
            break
        u = r.get("usage") or {}
        usage["prompt"] += u.get("prompt_tokens", 0); usage["completion"] += u.get("completion_tokens", 0)
        usage["cached"] += (u.get("prompt_tokens_details") or {}).get("cached_tokens", 0)
        msg = r["choices"][0]["message"]
        assistant = {"role": "assistant", "content": msg.get("content") or ""}
        if msg.get("tool_calls"):
            assistant["tool_calls"] = msg["tool_calls"]
        messages.append(assistant)
        calls = msg.get("tool_calls") or []
        s.log(kind="turn", turn=turn, tools=[c["function"]["name"] for c in calls],
              text=(msg.get("content") or "")[:300], usage=u)
        print(f"turn {turn}: {[c['function']['name'] for c in calls]} {(msg.get('content') or '')[:120]!r}", flush=True)
        if not calls:
            messages.append({"role": "user", "content": "Continue: use the tools until check reports ACCEPTED."})
            continue
        for c in calls:
            name = c["function"]["name"]
            try:
                args = json.loads(c["function"].get("arguments") or "{}")
            except json.JSONDecodeError:
                args = {}
            fn = {"read_file": lambda: s.read_file(args.get("path", "")),
                  "write_solution": lambda: s.write_solution(args.get("content", "")),
                  "check": s.check, "run_tests": s.run_tests}.get(name)
            result = fn() if fn else f"error: unknown tool {name}"
            print(f"   {name} -> {result[:160]!r}", flush=True)
            messages.append({"role": "tool", "tool_call_id": c["id"], "content": result})
        if s.accepted:
            break
    summary = {"model": a.model, "accepted": s.accepted, "turns": turn + 1, "versions": s.version,
               "elapsed_s": int(time.monotonic() - t0), "usage": usage}
    (out / "summary.json").write_text(json.dumps(summary, indent=2))
    (out / "messages.json").write_text(json.dumps(messages, indent=2))
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
