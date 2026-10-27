#!/usr/bin/env python3
"""Repair agent: a Meta model fixes a task's definition and proves its locked requirements.

The agent works in its own sandbox workspace (a copy of the task's Lean project without
reference solutions). It can read the protected spec, edit candidate/Solution.lean,
compile it, and run binary property tests. Acceptance is decided only by harness/judge.py.

Arms (E1): A1 is `--planner none`; A2 adds the planner model. A0 is agents/baseline.py.

Usage: repair.py [--task T] [--model muse-spark-1.3-contributor] [--planner muse-wonder-1.0|none]
                 [--budget-usd X] [--budget-wall S] [--out DIR] [--start FILE]
"""
import argparse, json, pathlib, re, shutil, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "agents"))
sys.path.insert(0, str(ROOT / "harness"))
from meta_client import chat, APIError  # noqa: E402
from budget import Budget, BudgetExceeded  # noqa: E402
import judge, binary_check, task as taskmod  # noqa: E402

FORBIDDEN_TEXT = ("sorry, axiom, opaque, implemented_by, extern, unsafe, export, macro, elab, syntax, "
                  "initialize, #eval, run_cmd, native_decide, set_option")


def task_brief(task):
    """Task description and rules shared by every arm."""
    defs = ", ".join(f"`{task.ns}.{d}`" for d in task.definitions)
    n = len(task.theorems)
    lemmas = ""
    lp = task.root / task.spec_dir / "Lemmas.lean"
    if lp.exists():
        names = re.findall(r"^(?:@\[[^\]]*\]\s*)?theorem\s+(\S+)", lp.read_text(), re.M)
        lemmas = (f"\n- {task.lib}.Lemmas contains proved helper lemmas you may use "
                  f"({', '.join(names)}).")
    return f"""You are a software repair agent working in Lean 4 (v4.35.0, core library only, no Mathlib).

Issue report: {task.issue}

Your job:
1. Fix {defs} in candidate/Solution.lean so it satisfies the locked requirements in {task.spec_dir}/Spec.lean.
2. Prove all {n} theorems of {task.spec_dir}/Challenge.lean in candidate/Solution.lean, with exactly the same names and statements, and no `sorry`.

Rules (enforced by an independent judge; violations are rejected):
- Never edit files under spec/. You may only change candidate/Solution.lean.
- candidate/Solution.lean must define {defs} and the {n} theorems in `namespace {task.ns}`.
- Allowed imports: {task.lib}.Spec, {task.lib}.Lemmas, Init.*, Std.*.
- Forbidden: {FORBIDDEN_TEXT}.
- Weakening or restating a theorem differently is rejected. Changing behavior to avoid hard inputs cannot satisfy requirements that demand success on valid inputs.{lemmas}"""


WORKFLOW = """

Workflow:
- Read the spec, then write a first full candidate with write_solution (use `sorry` for proofs you have not done yet so the file compiles).
- call check: it reports, per required theorem, PROVED / SORRY / ERROR, plus compiler errors with goal states.
- Work on one obligation at a time. Develop a lemma or proof with try_snippet: it compiles your snippet after the current candidate, and if the snippet compiles with no errors and no sorry, its new declarations are banked into candidate/Solution.lean automatically (a required theorem that is still `sorry` is replaced by your proved version). Give helper lemmas unique names. Use replace_declaration to change existing declarations. Never rewrite theorems that are already PROVED.
- Prove easy obligations first. For hard ones, state and prove small helper lemmas by induction.
- Use run_tests to see concrete counterexamples on the compiled binary.
- Stop when check reports ACCEPTED."""


def tools_for(task):
    return [
        {"type": "function", "function": {"name": "read_file", "description": "Read a file from the workspace.",
         "parameters": {"type": "object", "properties": {"path": {"type": "string", "enum": task.readable}}, "required": ["path"]}}},
        {"type": "function", "function": {"name": "write_solution", "description": "Replace candidate/Solution.lean with the full given content.",
         "parameters": {"type": "object", "properties": {"content": {"type": "string"}}, "required": ["content"]}}},
        {"type": "function", "function": {"name": "replace_declaration", "description": f"Replace one top-level declaration (def, theorem, lemma, instance) in candidate/Solution.lean, identified by its name, with the given full text. If no declaration has that name, the text is inserted before `end {task.ns}`.",
         "parameters": {"type": "object", "properties": {"name": {"type": "string"}, "text": {"type": "string"}}, "required": ["name", "text"]}}},
        {"type": "function", "function": {"name": "try_snippet", "description": f"Compile the given Lean code appended inside `namespace {task.ns}` after the current candidate, without modifying the file. Returns errors and unsolved goals in the snippet.",
         "parameters": {"type": "object", "properties": {"code": {"type": "string"}}, "required": ["code"]}}},
        {"type": "function", "function": {"name": "check", "description": "Compile candidate/Solution.lean. Returns Lean errors with goal states, remaining sorries and rule violations. If it compiles cleanly, runs the official judge and returns ACCEPTED or the rejection reason.",
         "parameters": {"type": "object", "properties": {}}}},
        {"type": "function", "function": {"name": "run_tests", "description": "Build the executable from the current candidate and run property tests against the requirements. Returns violated requirements and counterexamples.",
         "parameters": {"type": "object", "properties": {}}}},
    ]


class Session:
    def __init__(self, task, model, start, out, budget=None):
        self.task, self.model, self.out = task, model, out
        self.ns, self.theorems = task.ns, task.theorems
        self.end = f"end {task.ns}"
        self.budget = budget or Budget()
        self.ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-repair-"))
        for rel in taskmod.PROJECT_FILES:
            src = task.root / rel
            (shutil.copytree if src.is_dir() else shutil.copy)(src, self.ws / rel)
        (self.ws / "candidate").mkdir()
        shutil.copy(start, self.ws / "candidate/Solution.lean")
        self.version = 0
        self.targets = set()   # planned helper lemmas the bank may replace while they are sorry
        self.plan_count = 0
        self.accepted = False
        self.events = []
        # Declaration boundary: the next top-level item or the namespace end.
        self.boundary = rf"(?:@\[|/--|private |protected |theorem |lemma |def |instance |abbrev |{re.escape(self.end)})"

    def log(self, **kw):
        kw["t"] = round(time.time(), 3)
        self.events.append(kw)
        with (self.out / "events.jsonl").open("a") as f:
            f.write(json.dumps(kw) + "\n")

    def read_file(self, path):
        if path not in self.task.readable:
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
        """Keep the required theorems at the end of the file, after every helper."""
        chunks = []
        for t in self.theorems:
            m = re.search(rf"^theorem\s+{re.escape(t)}\b", text, re.M)
            if not m:
                continue
            rest = text[m.end():]
            n = re.search(rf"^{self.boundary}", rest, re.M)
            end = m.end() + (n.start() if n else len(rest))
            chunks.append(text[m.start():end].rstrip("\n"))
            text = text[:m.start()] + text[end:]
        if self.end in text:
            head, tail = text.rsplit(self.end, 1)
            return head.rstrip("\n") + "\n\n" + "\n\n".join(chunks) + f"\n\n{self.end}" + tail
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
        ends_at = [i for i, l in enumerate(lines) if l.startswith(self.end)]
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

    def compile(self, tail=9000):
        return judge.in_container(self.ws, f"lake build Solution 2>&1 | tail -c {tail}", timeout=600)

    def replace_declaration(self, name, text):
        """Transactional edit: kept only if the file still compiles."""
        before = self._source()
        new, action = self._replace_in(before, name, text)
        self._save(new, f"{action} {name}")
        r = self.compile()
        if "error:" in r["output_tail"]:
            self._save(before, f"revert {name}")
            return (f"REVERTED: the edit to {name} broke compilation, so the file is unchanged "
                    f"(version {self.version}). Errors:\n" + self._clean(r["output_tail"])[-5000:])
        return f"{action} declaration {name} (version {self.version}); file compiles"

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
        body = src.rsplit(self.end, 1)[0] if self.end in src else src
        offset = body.count("\n") + 1
        scratch = body + "\n" + code + f"\n\n{self.end}\n"
        (self.ws / "Scratch.lean").write_text(scratch)
        r = judge.in_container(self.ws, f"lake build {self.task.lib} >/dev/null 2>&1; lake env lean Scratch.lean 2>&1 | tail -c 9000", timeout=300)
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
            elif name in self.theorems or name in self.targets:
                decl = re.search(rf"theorem\s+{re.escape(name)}\b.*?(?=\n{self.boundary})", self._source(), re.S)
                if decl and "sorry" in decl.group(0):
                    # Move the proved theorem to the end so it follows the helpers it uses.
                    removed, _ = self._replace_in(self._source(), name, "")
                    moved, _ = self._replace_in(removed, name, chunk)
                    self._save(moved, f"banked {name}")
                    banked.append(name)
            src = self._source()
            existing = {m.group(1).split(".")[-1]: m.start() for m in self.DECL.finditer(src)}
        return banked

    def theorem_status(self, names=None):
        """Per-declaration status from `#print axioms` on the compiled candidate."""
        names = names or self.theorems
        probe = "import Solution\n" + "\n".join(f"#print axioms {self.ns}.{t}" for t in names) + "\n"
        (self.ws / "Status.lean").write_text(probe)
        r = judge.in_container(self.ws, "lake env lean Status.lean 2>&1", timeout=300)
        status, blocks = {}, re.split(rf"(?='{re.escape(self.ns)}\.)", r["output_tail"])
        for t in names:
            blk = next((b for b in blocks if b.startswith(f"'{self.ns}.{t}'")), "")
            if not blk:
                status[t] = "MISSING"
            elif "sorryAx" in blk:
                status[t] = "SORRY"
            else:
                status[t] = "PROVED"
        return status

    def check_status(self, names=None):
        r = self.compile(2000)
        if "error:" in r["output_tail"]:
            return {t: "ERROR" for t in (names or self.theorems)}
        return self.theorem_status(names)

    def check(self):
        files = [self.ws / "candidate/Solution.lean"]
        scan = judge.impl_scan(files, self.task)
        r = self.compile(16000)
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
        j = judge.judge(str(self.ws / "candidate/Solution.lean"), task=self.task)
        self.log(kind="judge", version=self.version, accepted=j["accepted"], ms=j["elapsed_ms"])
        (self.out / f"judge_v{self.version:03d}.json").write_text(json.dumps(j, indent=2))
        if j["accepted"]:
            self.accepted = True
            return f"ACCEPTED by the official judge (comparator + leanchecker). All {len(self.theorems)} requirements VERIFIED."
        cmp_ = j["checks"].get("comparator", {}).get("output_tail", "")
        reasons = j["checks"]["tree"]["problems"] + j["checks"]["impl_scan"]["problems"]
        return "NOT ACCEPTED by judge: " + "; ".join(reasons) + "\n" + "\n".join(
            l for l in cmp_.splitlines() if "error" in l.lower())[-3000:]

    def run_tests(self):
        b = binary_check.check_binary(str(self.ws / "candidate/Solution.lean"), n_cases=300,
                                      seed=self.version, task=self.task)
        self.log(kind="tests", version=self.version, status=b["status"], violations=b.get("violations"))
        if b["status"] == "BUILD_FAILED":
            return "executable build failed:\n" + b["build"].get("output_tail", "")[-3000:]
        ws = [{"requirement": w["requirement"], "message": w["message"],
               "input": w["input"], "output": w["output"]} for w in b["witnesses"][:3]]
        return json.dumps({"status": b["status"], "violations": b["violations"], "examples": ws})


def dialog(s, model, effort, system, user, tool_names, max_turns, done, label):
    """Run one tool-using dialog until done() or the turn budget is spent."""
    tools = [t for t in tools_for(s.task) if t["function"]["name"] in tool_names]
    messages = [{"role": "system", "content": system}, {"role": "user", "content": user}]
    extra = {} if effort == "default" else {"reasoning_effort": effort}
    for turn in range(max_turns):
        s.budget.check()
        try:
            r = chat(model, messages, f"repair:{s.task.id}:{label}:turn{turn}", tools=tools, max_tokens=32000,
                     timeout=600, **extra)
        except APIError as e:
            s.log(kind="api_error", status=e.status, body=e.body[:300])
            if e.status in (429, 500, 502, 503):
                time.sleep(20)
                continue
            return False, messages
        u = r.get("usage") or {}
        s.budget.charge(model, u)
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


def spec_text(s):
    return "\n\n".join(f"=== {p} ===\n{s.read_file(p)}" for p in s.task.readable[:-1])


def orchestrate(s, a):
    system = task_brief(s.task) + WORKFLOW
    spec = spec_text(s)
    defs = ", ".join(f"`{s.ns}.{d}`" for d in s.task.definitions)
    # Phase 0: behavior first. The binary must pass the requirement-derived tests.
    tests_ok = {"v": False}
    orig_run_tests = s.run_tests
    def run_tests_tracked():
        out = orig_run_tests()
        tests_ok["v"] = out.startswith('{"status": "PASS"')
        return out
    s.run_tests = run_tests_tracked
    if orig_run_tests().startswith('{"status": "PASS"'):
        s.log(kind="phase", phase="implement", ok=True, skipped="start candidate already passes tests")
        tests_ok["v"] = True
    user0 = (f"{spec}\n\n=== candidate/Solution.lean (current, buggy) ===\n{s._source()}\n\n"
             f"Phase 1 of 2: fix {defs} so it meets the requirements. Keep every required theorem in the file "
             "(use `sorry` proofs for now). Write the file with write_solution, then call run_tests until it reports PASS.")
    ok0 = tests_ok["v"] or dialog(s, a.model, a.effort, system, user0, {"write_solution", "run_tests", "read_file"},
                                  a.phase0_turns, lambda: tests_ok["v"], "implement")[0]
    s.log(kind="phase", phase="implement", ok=ok0)
    if not ok0:
        return
    # Phase 1: one focused dialog per obligation, in the task's listed order.
    status = s.check_status()
    for t in s.theorems:
        if status.get(t) == "PROVED" or own_sorry_free(s, t):
            continue
        prove_target(s, a, system, spec, t, a.obligation_turns, "pass1")
        status = s.check_status()
    # Phase 2: resolve what is left, decomposing hard goals with the planner.
    for t in s.theorems:
        if s.check_status([t]).get(t) != "PROVED":
            resolve(s, a, system, spec, t, 0)
    prune(s)
    s.check()


def decl_text(s, name):
    m = re.search(rf"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma|def)\s+{re.escape(name)}(?=[\s:({{\[]).*?"
                  rf"(?=^{s.boundary})", s._source(), re.S | re.M)
    return m.group(0) if m else ""


def own_sorry_free(s, name):
    text = decl_text(s, name)
    return bool(text) and "sorry" not in text


def pending_deps(s, name):
    """Helper declarations still proved by `sorry` that `name`'s proof mentions."""
    body = decl_text(s, name)
    out = []
    for m in s.DECL.finditer(s._source()):
        n = m.group(1).split(".")[-1]
        if n != name and n not in s.theorems and re.search(rf"(?<![\w.]){re.escape(n)}(?![\w?!'])", body) \
                and not own_sorry_free(s, n):
            out.append(n)
    return out


def resolve(s, a, system, spec, name, depth, plan_text=""):
    """Make `name` sorry-free: try directly, then decompose with the planner (bounded depth)."""
    if not own_sorry_free(s, name):
        prove_target(s, a, system, spec, name, a.obligation_turns, f"d{depth}", plan_text)
    if not own_sorry_free(s, name) and depth < a.max_depth and a.planner != "none":
        lemmas, text = plan(s, a, spec, name, s.plan_count)
        for l in lemmas:
            resolve(s, a, system, spec, l, depth + 1, text)
        prove_target(s, a, system, spec, name, a.obligation_turns, f"d{depth}", text)
    if own_sorry_free(s, name):
        for dep in pending_deps(s, name):
            resolve(s, a, system, spec, dep, depth + 1, plan_text)
    ok = s.check_status([name]).get(name) == "PROVED"
    s.log(kind="resolve", name=name, depth=depth, ok=ok)
    return ok


def prune(s):
    """Delete helper declarations that still use sorry and are referenced by nothing else."""
    changed = True
    while changed:
        changed = False
        src = s._source()
        for m in list(s.DECL.finditer(src)):
            n = m.group(1).split(".")[-1]
            if n in s.theorems or own_sorry_free(s, n):
                continue
            others = src.replace(decl_text(s, n), "")
            if not re.search(rf"(?<![\w.]){re.escape(n)}(?![\w?!'])", others):
                new, _ = s._replace_in(src, n, "")
                s._save(new, f"prune {n}")
                changed = True
                break


PLANNER_SYSTEM = """You are a Lean 4 proof architect (Lean v4.35.0 core library only, no Mathlib).
Given a specification, a candidate implementation, and a required theorem that a prover failed to prove,
you design a chain of helper lemmas that makes the proof routine. Each lemma must be TRUE, stated in
Lean 4 syntax that elaborates against the given file, and small enough to prove by induction or simp/omega.
Prefer general lemmas over specific ones. Avoid Mathlib names (no Finset, no linarith, no BigOperators)."""


def plan(s, a, spec, t, attempt):
    """Ask the planner model for helper lemma statements; install them as sorry targets."""
    stmt = re.search(rf"theorem\s+{re.escape(t)}\s*:[^\n]*",
                     s.read_file(f"{s.task.spec_dir}/Challenge.lean") + s._source())
    user = (f"{spec}\n\n=== candidate/Solution.lean (current) ===\n{s._source()}\n\n"
            f"The prover could not prove `{stmt.group(0).replace(' := sorry', '') if stmt else t}`.\n"
            "Reply with (1) a short proof plan in prose, then (2) exactly one ```lean code block containing 2 to 6 "
            "helper lemmas, each written as `theorem <unique_name> ... := by sorry`, in dependency order, inside no "
            f"namespace (the code is inserted inside `namespace {s.ns}`). Use names prefixed with `plan"
            f"{attempt}_` and no `?` or `!` in names.")
    extra = {} if a.planner_effort == "default" else {"reasoning_effort": a.planner_effort}
    for tries in range(3):
        s.budget.check()
        try:
            r = chat(a.planner, [{"role": "system", "content": PLANNER_SYSTEM}, {"role": "user", "content": user}],
                     f"plan:{s.task.id}:{t}:{attempt}", max_tokens=32000, timeout=900, **extra)
        except APIError as e:
            s.log(kind="api_error", status=e.status, body=e.body[:300])
            time.sleep(20)
            continue
        s.budget.charge(a.planner, r.get("usage") or {})
        text = r["choices"][0]["message"].get("content") or ""
        m = re.search(r"```lean\s*\n(.*?)```", text, re.S)
        if not m:
            user += "\n\nYour reply had no ```lean code block. Reply again in the required format."
            continue
        code = m.group(1).strip()
        names = [d.group(1).split(".")[-1] for d in s.DECL.finditer(code)]
        before = s._source()
        new = before
        for d in re.split(r"\n(?=(?:theorem|lemma) )", code):
            dm = s.DECL.match(d.strip())
            if dm:
                new, _ = s._replace_in(new, dm.group(1), d.strip())
        s._save(new, f"plan {t} {attempt}")
        st = s.check_status(names)
        if any(v == "ERROR" for v in st.values()):
            r2 = s.compile(6000)
            s._save(before, f"revert plan {t} {attempt}")
            user += ("\n\nThese lemma statements do not elaborate. Fix them. Compiler output:\n"
                     + s._clean(r2["output_tail"])[-3000:])
            continue
        s.targets.update(names)
        s.plan_count += 1
        prose = text[: m.start()].strip()[-3000:]
        (s.out / f"plan_{t}_{attempt}.md").write_text(text)
        s.log(kind="plan", theorem=t, attempt=attempt, lemmas=names, model=a.planner)
        print(f"[plan {t}] {names}", flush=True)
        return names, prose
    return [], ""


def prove_target(s, a, system, spec, t, budget, label, plan_text=""):
    src = s._source()
    m = re.search(rf"theorem\s+{re.escape(t)}\b[^\n]*(?:\n(?!theorem|lemma|def|end )[^\n]*)*", src)
    stmt = (m.group(0).split(":= by")[0].split(":= sorry")[0] if m else t).strip()
    status = s.check_status()
    defs = ", ".join(f"`{d}`" for d in s.task.definitions)
    user = (f"{spec}\n\n=== candidate/Solution.lean (current) ===\n{src}\n\n"
            f"Current requirement status: {', '.join(f'{k}={v}' for k, v in status.items())}\n\n"
            + (f"Proof plan from the architect:\n{plan_text}\n\n" if plan_text else "")
            + f"Your task now: prove `{stmt}`. Do not change {defs} or anything already proved. "
            "Develop the proof with try_snippet; a clean snippet that proves "
            f"`{t}` replaces its sorry automatically. You may use the other helper lemmas in the file even if "
            "they are still sorry; they are proved separately.")
    def own_proof_done():
        """The target's own proof is sorry-free and the file compiles (dependencies may be pending)."""
        m2 = re.search(rf"^(?:private\s+)?theorem\s+{re.escape(t)}\b.*?(?=^{s.boundary})", s._source(), re.S | re.M)
        return bool(m2) and "sorry" not in m2.group(0) and s.check_status([t]).get(t) != "ERROR"
    ok, _ = dialog(s, a.model, a.effort, system, user, {"try_snippet", "replace_declaration", "check", "read_file"},
                   budget, own_proof_done, f"{label}:{t}")
    s.log(kind="obligation", label=label, theorem=t, ok=ok)
    return ok


def finish(s, out, arm, extra):
    """Write summary.json and the final candidate; final judging is done by the evaluator."""
    shutil.copy(s.ws / "candidate/Solution.lean", out / "final.lean")
    summary = {"task": s.task.id, "arm": arm, "model": s.model, **extra, "accepted_in_session": s.accepted,
               "versions": s.version, "budget": s.budget.summary(), "final_status": s.check_status()}
    (out / "summary.json").write_text(json.dumps(summary, indent=2))
    shutil.rmtree(s.ws, ignore_errors=True)
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", help="task id or directory (default: flagship)")
    ap.add_argument("--model", default="muse-spark-1.3-contributor")
    ap.add_argument("--mode", default="orchestrated", choices=["orchestrated", "free"])
    ap.add_argument("--max-turns", type=int, default=40, help="free mode only")
    ap.add_argument("--phase0-turns", type=int, default=12)
    ap.add_argument("--obligation-turns", type=int, default=12)
    ap.add_argument("--start", help="starting candidate (default: the task's candidate/Solution.lean)")
    ap.add_argument("--effort", default="medium", choices=["low", "medium", "high", "default"])
    ap.add_argument("--planner", default="muse-wonder-1.0", help="planner model, or 'none' (arm A1)")
    ap.add_argument("--planner-effort", default="high", choices=["low", "medium", "high", "default"])
    ap.add_argument("--max-depth", type=int, default=2)
    ap.add_argument("--budget-usd", type=float, help="cap at standard-tier list prices")
    ap.add_argument("--budget-wall", type=float, help="wall-clock cap in seconds")
    ap.add_argument("--out", help="run directory (default: runs/repair-<time>-<task>-<arm>)")
    a = ap.parse_args()
    task = taskmod.load(a.task)
    arm = "A1" if a.planner == "none" else "A2"
    out = pathlib.Path(a.out) if a.out else \
        ROOT / "runs" / f"repair-{time.strftime('%Y%m%d-%H%M%S')}-{task.id}-{arm}"
    out.mkdir(parents=True, exist_ok=True)
    s = Session(task, a.model, a.start or task.start, out, Budget(a.budget_usd, a.budget_wall))
    s.log(kind="start", arm=arm, **vars(a))
    try:
        if a.mode == "orchestrated":
            orchestrate(s, a)
        else:
            dialog(s, a.model, a.effort, task_brief(task) + WORKFLOW,
                   "Begin. The current candidate is candidate/Solution.lean.",
                   {t["function"]["name"] for t in tools_for(task)}, a.max_turns, lambda: s.accepted, "free")
    except BudgetExceeded as e:
        s.log(kind="budget_stop", reason=str(e))
        print(f"budget exhausted: {e}", flush=True)
    summary = finish(s, out, arm, {"mode": a.mode, "effort": a.effort, "planner": a.planner})
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
