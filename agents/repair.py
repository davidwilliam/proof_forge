#!/usr/bin/env python3
"""Repair agent v1: a Meta model fixes `Payout.step` and proves the locked requirements.

The agent works in its own sandbox workspace (a copy of formal/ without reference
solutions). It can read the protected spec, replace candidate/Solution.lean, compile it,
and run binary property tests. Acceptance is decided only by harness/judge.py.

Usage: repair.py [--model muse-spark-1.3-contributor] [--max-turns 40] [--effort medium] [--start FILE]
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

Workflow:
- Read the spec, then write a first full candidate with write_solution (use `sorry` for proofs you have not done yet so the file compiles).
- call check: it reports, per required theorem, PROVED / SORRY / ERROR, plus compiler errors with goal states.
- Work on one obligation at a time. Develop a lemma or proof with try_snippet: it compiles your snippet after the current candidate, and if the snippet compiles with no errors and no sorry, its new declarations are banked into candidate/Solution.lean automatically (a required theorem that is still `sorry` is replaced by your proved version). Give helper lemmas unique names. Use replace_declaration to change existing declarations. Never rewrite theorems that are already PROVED.
- Prove easy obligations first. For hard ones, state and prove small helper lemmas by induction.
- Use run_tests to see concrete counterexamples on the compiled binary.
- Stop when check reports ACCEPTED."""

TOOLS = [
    {"type": "function", "function": {"name": "read_file", "description": "Read a file from the workspace.",
     "parameters": {"type": "object", "properties": {"path": {"type": "string", "enum": READABLE}}, "required": ["path"]}}},
    {"type": "function", "function": {"name": "write_solution", "description": "Replace candidate/Solution.lean with the full given content.",
     "parameters": {"type": "object", "properties": {"content": {"type": "string"}}, "required": ["content"]}}},
    {"type": "function", "function": {"name": "replace_declaration", "description": "Replace one top-level declaration (def, theorem, lemma, instance) in candidate/Solution.lean, identified by its name, with the given full text. If no declaration has that name, the text is inserted before `end Payout`.",
     "parameters": {"type": "object", "properties": {"name": {"type": "string"}, "text": {"type": "string"}}, "required": ["name", "text"]}}},
    {"type": "function", "function": {"name": "try_snippet", "description": "Compile the given Lean code appended inside `namespace Payout` after the current candidate, without modifying the file. Returns errors and unsolved goals in the snippet.",
     "parameters": {"type": "object", "properties": {"code": {"type": "string"}}, "required": ["code"]}}},
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
        self._save(content, "write_solution")
        return f"written (version {self.version}, {len(content)} bytes)"

    DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                      r"(?:theorem|lemma|def|instance|abbrev)\s+([^\s:({\[]+)", re.M)

    def _source(self):
        return (self.ws / "candidate/Solution.lean").read_text()

    def _normalize(self, text):
        """Keep the eight required theorems at the end of the file, after every helper."""
        chunks = []
        for t in THEOREMS:
            m = re.search(rf"^theorem\s+{t}\b", text, re.M)
            if not m:
                continue
            rest = text[m.end():]
            n = re.search(r"^(?:@\[|/--|private |protected |theorem |lemma |def |instance |abbrev |end Payout)", rest, re.M)
            end = m.end() + (n.start() if n else len(rest))
            chunks.append(text[m.start():end].rstrip("\n"))
            text = text[:m.start()] + text[end:]
        if "end Payout" in text:
            head, tail = text.rsplit("end Payout", 1)
            return head.rstrip("\n") + "\n\n" + "\n\n".join(chunks) + "\n\nend Payout" + tail
        return text.rstrip("\n") + "\n\n" + "\n\n".join(chunks) + "\n"

    def _save(self, text, why):
        text = self._normalize(text)
        self.version += 1
        (self.ws / "candidate/Solution.lean").write_text(text)
        (self.out / f"candidate_v{self.version:03d}.lean").write_text(text)
        self.log(kind="write", version=self.version, bytes=len(text), why=why)

    def _replace_in(self, src, name, text):
        """Return (new_source, action): replace declaration `name` with `text`, or insert it."""
        lines = src.split("\n")
        starts = [(i, m.group(1)) for i, l in enumerate(lines) for m in [self.DECL.match(l)] if m]
        ends_at = [i for i, l in enumerate(lines) if l.startswith("end Payout")]
        short = name.split(".")[-1]
        hit = [k for k, (i, n) in enumerate(starts) if n.split(".")[-1] == short]
        body = text.rstrip("\n").split("\n") if text else []
        if hit:
            k = hit[0]
            a = starts[k][0]
            while a > 0 and (lines[a - 1].startswith("@[") or lines[a - 1].rstrip().endswith("-/")):
                if lines[a - 1].rstrip().endswith("-/"):
                    while a > 0 and not lines[a - 1].lstrip().startswith("/-"):
                        a -= 1
                a -= 1
            b = starts[k + 1][0] if k + 1 < len(starts) else (ends_at[-1] if ends_at else len(lines))
            while b - 1 > a and (lines[b - 1].startswith("@[") or lines[b - 1].strip() == ""):
                b -= 1
            return "\n".join(lines[:a] + body + [""] + lines[b:]), "replaced"
        e = ends_at[-1] if ends_at else len(lines)
        return "\n".join(lines[:e] + body + [""] + lines[e:]), "inserted"

    def replace_declaration(self, name, text):
        new, action = self._replace_in(self._source(), name, text)
        self._save(new, f"{action} {name}")
        return f"{action} declaration {name} (version {self.version})"

    @staticmethod
    def _clean(text):
        keep = [l for l in text.splitlines()
                if not l.startswith("trace:") and not re.match(r"^[✔✖⚠] \[\d+/\d+\]", l)
                and "linter" not in l and "Hint:" not in l and "deprecated" not in l]
        return "\n".join(keep)

    def try_snippet(self, code):
        src = self._source()
        # Declarations redefined by the snippet are removed from the context first.
        for m in self.DECL.finditer(code):
            if re.search(rf"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma|def|instance|abbrev)\s+{re.escape(m.group(1).split('.')[-1])}\b", src, re.M):
                src, _ = self._replace_in(src, m.group(1), "")
        body = src.rsplit("end Payout", 1)[0] if "end Payout" in src else src
        offset = body.count("\n") + 1
        scratch = body + "\n" + code + "\n\nend Payout\n"
        (self.ws / "Scratch.lean").write_text(scratch)
        r = judge.in_container(self.ws, "lake build Payout >/dev/null 2>&1; lake env lean Scratch.lean 2>&1 | tail -c 9000", timeout=300)
        out = self._clean(r["output_tail"])
        # Keep only messages located in the snippet, renumbered from 1.
        msgs, cur = [], None
        for l in out.splitlines():
            m = re.match(r"^Scratch\.lean:(\d+):(\d+): (error|warning)", l)
            if m:
                ln = int(m.group(1)) - offset
                cur = ln >= 0
                if cur:
                    l = re.sub(r"^Scratch\.lean:\d+", f"snippet:{ln}", l)
            if cur:
                msgs.append(l)
        clean = not any(re.search(r": (error|warning)", m) for m in msgs)
        self.log(kind="snippet", version=self.version, ok=clean, ms=r["elapsed_ms"])
        if not clean:
            return "\n".join(msgs)[-6000:]
        banked = self.bank(code)
        return "snippet compiles with no errors or warnings" + (
            f"; banked into candidate/Solution.lean: {', '.join(banked)} (version {self.version})" if banked else "")

    def bank(self, code):
        """Install declarations from a clean snippet: new names are appended, and a required
        theorem that is currently `sorry` is replaced by the proved version."""
        lines = code.split("\n")
        starts = [i for i, l in enumerate(lines) if self.DECL.match(l)]
        src = self._source()
        existing = {m.group(1).split(".")[-1]: m.start() for m in self.DECL.finditer(src)}
        banked = []
        for k, a in enumerate(starts):
            while a > 0 and (lines[a - 1].startswith("@[") or lines[a - 1].lstrip().startswith("/--")):
                a -= 1
            b = starts[k + 1] if k + 1 < len(starts) else len(lines)
            while b > 0 and b - 1 > a and (lines[b - 1].startswith("@[") or lines[b - 1].lstrip().startswith("/--")):
                b -= 1
            chunk = "\n".join(lines[a:b]).strip("\n")
            name = self.DECL.match(lines[starts[k]]).group(1).split(".")[-1]
            if "sorry" in chunk:
                continue
            if name not in existing:
                self.replace_declaration(name, chunk)
                banked.append(name)
            elif name in THEOREMS:
                decl = re.search(rf"theorem\s+{re.escape(name)}\b.*?(?=\n(?:@\[|/--|private |theorem |lemma |def |instance |abbrev |end Payout))",
                                 self._source(), re.S)
                if decl and "sorry" in decl.group(0):
                    # Move the proved theorem to the end so it follows the helpers it uses.
                    removed, _ = self._replace_in(self._source(), name, "")
                    moved, _ = self._replace_in(removed, name, chunk)
                    self._save(moved, f"banked {name}")
                    banked.append(name)
            src = self._source()
            existing = {m.group(1).split(".")[-1]: m.start() for m in self.DECL.finditer(src)}
        return banked

    def theorem_status(self):
        """Per-requirement status from `#print axioms` on the compiled candidate."""
        probe = "import Solution\n" + "\n".join(f"#print axioms Payout.{t}" for t in THEOREMS) + "\n"
        (self.ws / "Status.lean").write_text(probe)
        r = judge.in_container(self.ws, "lake env lean Status.lean 2>&1", timeout=300)
        status, blocks = {}, re.split(r"(?='Payout\.)", r["output_tail"])
        for t in THEOREMS:
            blk = next((b for b in blocks if b.startswith(f"'Payout.{t}'")), "")
            if not blk:
                status[t] = "MISSING"
            elif "sorryAx" in blk:
                status[t] = "SORRY"
            else:
                status[t] = "PROVED"
        return status

    def check_status(self):
        r = judge.in_container(self.ws, "lake build Solution 2>&1 | tail -c 2000", timeout=600)
        if "error:" in r["output_tail"]:
            return {t: "ERROR" for t in THEOREMS}
        return self.theorem_status()

    def check(self):
        files = [self.ws / "candidate/Solution.lean"]
        scan = judge.impl_scan(files)
        r = judge.in_container(self.ws, "lake build Solution 2>&1 | tail -c 16000", timeout=600)
        text = self._clean(r["output_tail"])
        errors = "error:" in text
        status = {} if errors else self.theorem_status()
        self.log(kind="check", version=self.version, errors=errors, status=status,
                 scan=scan["problems"], ms=r["elapsed_ms"])
        if errors or not scan["passed"] or any(v != "PROVED" for v in status.values()):
            parts = ["NOT ACCEPTED"]
            if scan["problems"]:
                parts.append("RULE VIOLATIONS:\n" + "\n".join(scan["problems"]))
            if status:
                parts.append("Requirement status: " + ", ".join(f"{k}={v}" for k, v in status.items()))
            if errors:
                parts.append("The file does not compile, so no requirement counts yet. Errors:\n" + text[-7000:])
            return "\n\n".join(parts)
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


ORDER = ["req_valid_succeeds", "req_invalid_noop", "req_authorization", "req_effects",
         "req_idempotency", "req_nonnegative", "req_fair_shares", "req_conservation"]


def dialog(s, model, effort, system, user, tool_names, max_turns, done, usage, label):
    """Run one tool-using dialog until done() or the turn budget is spent."""
    tools = [t for t in TOOLS if t["function"]["name"] in tool_names]
    messages = [{"role": "system", "content": system}, {"role": "user", "content": user}]
    extra = {} if effort == "default" else {"reasoning_effort": effort}
    for turn in range(max_turns):
        try:
            r = chat(model, messages, f"repair:{label}:turn{turn}", tools=tools, max_tokens=32000,
                     timeout=600, **extra)
        except APIError as e:
            s.log(kind="api_error", status=e.status, body=e.body[:300])
            if e.status in (429, 500, 502, 503):
                time.sleep(20)
                continue
            return False, messages
        u = r.get("usage") or {}
        usage["prompt"] += u.get("prompt_tokens", 0)
        usage["completion"] += u.get("completion_tokens", 0)
        usage["cached"] += (u.get("prompt_tokens_details") or {}).get("cached_tokens", 0)
        msg = r["choices"][0]["message"]
        assistant = {"role": "assistant", "content": msg.get("content") or ""}
        if msg.get("tool_calls"):
            assistant["tool_calls"] = msg["tool_calls"]
        messages.append(assistant)
        calls = msg.get("tool_calls") or []
        s.log(kind="turn", label=label, turn=turn, tools=[c["function"]["name"] for c in calls],
              text=(msg.get("content") or "")[:300], usage=u)
        print(f"[{label}] turn {turn}: {[c['function']['name'] for c in calls]}", flush=True)
        if not calls:
            messages.append({"role": "user", "content": "Continue with the tools."})
            continue
        for c in calls:
            name = c["function"]["name"]
            try:
                args = json.loads(c["function"].get("arguments") or "{}")
            except json.JSONDecodeError:
                args = {}
            fn = {"read_file": lambda: s.read_file(args.get("path", "")),
                  "write_solution": lambda: s.write_solution(args.get("content", "")),
                  "replace_declaration": lambda: s.replace_declaration(args.get("name", ""), args.get("text", "")),
                  "try_snippet": lambda: s.try_snippet(args.get("code", "")),
                  "check": s.check, "run_tests": s.run_tests}.get(name) if name in tool_names else None
            result = fn() if fn else f"error: tool {name} is not available in this phase"
            print(f"   {name} -> {result[:150]!r}", flush=True)
            messages.append({"role": "tool", "tool_call_id": c["id"], "content": result})
        if done():
            return True, messages
    return done(), messages


def orchestrate(s, a, usage):
    spec = "\n\n".join(f"=== {p} ===\n{s.read_file(p)}" for p in READABLE[:3])
    # Phase 0: behavior first. The binary must pass the requirement-derived tests.
    tests_ok = {"v": False}
    orig_run_tests = s.run_tests
    def run_tests_tracked():
        out = orig_run_tests()
        tests_ok["v"] = out.startswith('{"status": "PASS"')
        return out
    s.run_tests = run_tests_tracked
    user0 = (f"{spec}\n\n=== candidate/Solution.lean (current, buggy) ===\n{s._source()}\n\n"
             "Phase 1 of 2: fix `Payout.step` so it meets the requirements. Keep every required theorem in the file "
             "(use `sorry` proofs for now). Write the file with write_solution, then call run_tests until it reports PASS.")
    ok0, _ = dialog(s, a.model, a.effort, SYSTEM, user0, {"write_solution", "run_tests", "read_file"},
                    a.phase0_turns, lambda: tests_ok["v"], usage, "implement")
    s.log(kind="phase", phase="implement", ok=ok0)
    if not ok0:
        return
    # Phase 1: one focused dialog per obligation, easy ones first, then a second pass.
    for budget, label in ((a.obligation_turns, "pass1"), (a.obligation_turns * 2, "pass2")):
        status = s.check_status()
        for t in ORDER:
            if status.get(t) == "PROVED":
                continue
            stmt = re.search(rf"theorem\s+{t}\s*:[^\n]*", s.read_file("spec/Payout/Challenge.lean")).group(0)
            user = (f"{spec}\n\n=== candidate/Solution.lean (current) ===\n{s._source()}\n\n"
                    f"Current requirement status: {', '.join(f'{k}={v}' for k, v in status.items())}\n\n"
                    f"Your task now: prove `{stmt.replace(' := sorry', '')}`. Do not change `step` or theorems that are PROVED. "
                    "Develop helper lemmas and the proof with try_snippet; a clean snippet that proves "
                    f"`{t}` replaces its sorry automatically. Call check to confirm.")
            ok, _ = dialog(s, a.model, a.effort, SYSTEM, user,
                           {"try_snippet", "replace_declaration", "check", "read_file"},
                           budget, lambda t=t: s.check_status().get(t) == "PROVED", usage, f"{label}:{t}")
            status = s.check_status()
            s.log(kind="obligation", label=label, theorem=t, ok=ok, status=status)
        if all(v == "PROVED" for v in status.values()):
            break
    s.check()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="muse-spark-1.3-contributor")
    ap.add_argument("--mode", default="orchestrated", choices=["orchestrated", "free"])
    ap.add_argument("--max-turns", type=int, default=40, help="free mode only")
    ap.add_argument("--phase0-turns", type=int, default=12)
    ap.add_argument("--obligation-turns", type=int, default=12)
    ap.add_argument("--start", default=str(ROOT / "formal/attacks/buggy_original.lean"))
    ap.add_argument("--effort", default="medium", choices=["low", "medium", "high", "default"])
    a = ap.parse_args()
    out = ROOT / "runs" / f"repair-{time.strftime('%Y%m%d-%H%M%S')}-{a.mode}-{a.model}"
    out.mkdir(parents=True)
    s = Session(a.model, a.start, out)
    s.log(kind="start", **vars(a))
    t0 = time.monotonic()
    usage = {"prompt": 0, "completion": 0, "cached": 0}
    if a.mode == "orchestrated":
        orchestrate(s, a, usage)
    else:
        dialog(s, a.model, a.effort, SYSTEM, "Begin. The current candidate is candidate/Solution.lean.",
               {t["function"]["name"] for t in TOOLS}, a.max_turns, lambda: s.accepted, usage, "free")
    summary = {"model": a.model, "mode": a.mode, "effort": a.effort, "accepted": s.accepted,
               "versions": s.version, "elapsed_s": int(time.monotonic() - t0), "usage": usage,
               "final_status": s.check_status()}
    (out / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
