#!/usr/bin/env python3
"""Repair agent: a Meta model fixes a task's definition and proves its locked requirements.

The agent works in its own sandbox workspace (a copy of the task's Lean project without
reference solutions). It can read the protected spec, edit candidate/Solution.lean,
compile it, and run binary property tests. Acceptance is decided only by harness/judge.py.

Arms (E1): A1 is `--planner none`; A2 adds the planner model. A0 is agents/baseline.py.

Modes: `--mode repair` (default) starts from the task's buggy candidate and gives the issue
report. `--mode implement` starts from a stub generated from the locked challenge (every
required definition keeps its signature, its body is a neutral placeholder, every required
theorem is `sorry`) and asks for an implementation from the specification; the issue report,
the buggy candidate and the reference solutions are not used. Judging is identical.

Usage: repair.py [--task T] [--model muse-spark-1.3-contributor] [--planner muse-wonder-1.0|none]
                 [--mode repair|implement] [--loop orchestrated|free]
                 [--budget-usd X] [--budget-wall S] [--out DIR] [--start FILE]
"""
import argparse, json, pathlib, re, shutil, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "agents"))
sys.path.insert(0, str(ROOT / "harness"))
from meta_client import chat, APIError, DeadlineReached  # noqa: E402
from budget import Budget, BudgetExceeded  # noqa: E402
import judge, binary_check, task as taskmod  # noqa: E402

FORBIDDEN_TEXT = ("sorry, axiom, opaque, implemented_by, extern, unsafe, export, macro, elab, syntax, "
                  "initialize, #eval, run_cmd, native_decide, set_option")


def task_brief(task, mode="repair"):
    """Task description and rules shared by every arm. In implement mode the issue report is
    replaced by a request to implement the definitions from the specification."""
    defs = ", ".join(f"`{task.ns}.{d}`" for d in task.definitions)
    n = len(task.theorems)
    lemmas = ""
    lp = task.root / task.spec_dir / "Lemmas.lean"
    if lp.exists():
        names = re.findall(r"^(?:@\[[^\]]*\]\s*)?theorem\s+(\S+)", lp.read_text(), re.M)
        lemmas = (f"\n- {task.lib}.Lemmas contains proved helper lemmas you may use "
                  f"({', '.join(names)}).")
    if mode == "implement":
        intro = f"""You are a software implementation agent working in Lean 4 (v4.35.0, core library only, no Mathlib).

Request: implement {defs} from its specification. {task.spec_dir}/Spec.lean is the source of truth: it defines the types and every locked requirement. The current body of {defs} in candidate/Solution.lean is a placeholder that compiles but does not meet the requirements; replace it with a real implementation.

Your job:
1. Implement {defs} in candidate/Solution.lean so it satisfies the locked requirements in {task.spec_dir}/Spec.lean."""
    else:
        intro = f"""You are a software repair agent working in Lean 4 (v4.35.0, core library only, no Mathlib).

Issue report: {task.issue}

Your job:
1. Fix {defs} in candidate/Solution.lean so it satisfies the locked requirements in {task.spec_dir}/Spec.lean."""
    return intro + f"""
2. Prove all {n} theorems of {task.spec_dir}/Challenge.lean in candidate/Solution.lean, with exactly the same names and statements, and no `sorry`.

Rules (enforced by an independent judge; violations are rejected):
- Never edit files under spec/. You may only change candidate/Solution.lean.
- candidate/Solution.lean must define {defs} and the {n} theorems in `namespace {task.ns}`.
- Allowed imports: {task.lib}.Spec, {task.lib}.Lemmas, Init.*, Std.*.
- Forbidden: {FORBIDDEN_TEXT}.
- Weakening or restating a theorem differently is rejected. Changing behavior to avoid hard inputs cannot satisfy requirements that demand success on valid inputs.{lemmas}"""


# Implement mode: the starting candidate is generated from the locked challenge only.
STUB_PREFER = ("rejected", "denied", "invalid", "error", "none")


def _top_split(text, sep):
    """Split `text` at occurrences of `sep` outside parentheses, brackets and braces."""
    parts, depth, cur, i = [], 0, "", 0
    while i < len(text):
        ch = text[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0 and text.startswith(sep, i):
            parts.append(cur)
            cur, i = "", i + len(sep)
            continue
        cur += ch
        i += 1
    return [p.strip() for p in parts + [cur]]


def _unparen(ty):
    ty = ty.strip()
    while ty.startswith("(") and ty.endswith(")") and len(_top_split(ty[1:-1], ")")) == 1:
        ty = ty[1:-1].strip()
    return ty


def neutral_value(spec, ty):
    """A value of type `ty` that carries no task logic: a nullary constructor of an inductive
    declared in the spec (a rejection when there is one), or a standard default."""
    ty = _unparen(ty)
    m = re.search(rf"^inductive\s+{re.escape(ty)}\s+where\s*\n((?:[ \t]*(?:\|[^\n]*|--[^\n]*)?\n)+)", spec, re.M)
    if m:
        ctors = re.findall(r"^\s*\|\s*([A-Za-z_][\w']*)\s*(?:--.*)?$", m.group(1), re.M)
        if ctors:
            pick = next((c for p in STUB_PREFER for c in ctors if c == p), ctors[0])
            return f"{ty}.{pick}"
    simple = {"Nat": "0", "Int": "0", "Bool": "false", "String": '""', "Unit": "()"}
    if ty in simple:
        return simple[ty]
    if re.match(r"^(List|Array)\b", ty):
        return "[]" if ty.startswith("List") else "#[]"
    if re.match(r"^Option\b", ty):
        return "none"
    return "default"


def stub_body(spec, ty):
    """Body for a definition of type `ty`: a function returning its first argument (the input
    state) unchanged, paired with a neutral outcome when the result is `Outcome × State`."""
    ty = ty.strip()
    alias = re.search(rf"^(?:abbrev|def)\s+{re.escape(ty)}\s*(?::\s*Type\s*)?:=\s*([^\n]+)$", spec, re.M) \
        if re.fullmatch(r"[\w.']+", ty) else None
    full = alias.group(1).strip() if alias else ty
    parts = _top_split(full, "→")
    if len(parts) == 1:
        return neutral_value(spec, full)
    args, ret = parts[:-1], _unparen(parts[-1])
    state = _unparen(args[0])
    binders = " ".join(["s"] + ["_"] * (len(args) - 1))
    prod = _top_split(ret, "×")
    if len(prod) == 2 and _unparen(prod[1]) == state:
        return f"fun {binders} => ({neutral_value(spec, prod[0])}, s)"
    if ret == state:
        return f"fun {binders} => s"
    return f"fun {' '.join('_' for _ in args)} => {neutral_value(spec, ret)}"


def stub_candidate(task):
    """Starting candidate for implement mode, built from the locked challenge and the spec only:
    the challenge's imports (plus the protected Lemmas module when the task has one), every
    required definition with its exact signature and a neutral placeholder body, and every
    required theorem with its exact statement proved by `sorry`. Nothing is read from the
    task's candidate/, reference/ or attacks/ directories."""
    root = task.root / task.spec_dir
    challenge = (root / "Challenge.lean").read_text()
    spec = (root / "Spec.lean").read_text()
    text = re.sub(r"/-!.*?-/[ \t]*\n?", "", challenge, flags=re.S)
    for d in task.definitions:
        pat = re.compile(rf"^def\s+{re.escape(d)}\s*:\s*([^\n]+?)\s*:=\s*sorry[ \t]*$", re.M)
        m = pat.search(text)
        if not m:
            raise ValueError(f"{task.id}: no definition hole `def {d} : ... := sorry` in Challenge.lean")
        line = (f"-- Placeholder body; replace it with an implementation that meets the spec.\n"
                f"def {d} : {m.group(1)} := {stub_body(spec, m.group(1))}")
        text = text[:m.start()] + line + text[m.end():]
    if (root / "Lemmas.lean").exists() and f"import {task.lib}.Lemmas" not in text:
        text = re.sub(rf"^import {re.escape(task.lib)}\.Spec[ \t]*$", f"import {task.lib}.Spec\nimport {task.lib}.Lemmas",
                      text, count=1, flags=re.M)
    text = re.sub(r"\n{3,}", "\n\n", text).strip("\n") + "\n"
    return text


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
    def __init__(self, task, model, start, out, budget=None, mode="repair"):
        self.task, self.model, self.out, self.mode = task, model, out, mode
        self.ns, self.theorems = task.ns, task.theorems
        self.end = f"end {task.ns}"
        self.budget = budget or Budget()
        judge.DEADLINE = self.budget.deadline()   # every Lean run in this process stops at the deadline
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
        self.last_good = None  # source of the newest version known to compile
        self.best = None       # (required theorems proved, version, source) of the best compiling version
        self.notes = {}        # declaration name -> notes from dialogs that did not prove it
        self.tried = set()     # declarations already attempted in the current resolution round
        self.plan_for = {}     # helper name -> prose of the architecture or plan that introduced it
        self.level = {}        # helper name -> planner nesting level (required theorems: 0)
        self.events = []
        # Declaration boundary: the next top-level item or the namespace end.
        self.boundary = (r"(?:@\[|/--|private |protected |noncomputable |theorem |lemma |def |instance |abbrev "
                         rf"|structure |inductive |{re.escape(self.end)})")

    def call(self, model, messages, purpose, tools=None, max_tokens=32000, timeout=600, attempts=5, **extra):
        """One model call inside the budget. Every attempt is reserved at its worst case
        before it is sent and settled to the reported usage only if its full response arrives
        before the deadline. A network failure or timeout leaves the worst case charged (the
        request may have been processed). HTTP failures also retain their reservation:
        an error response does not establish that upstream usage was zero.
        A response completed after the deadline is discarded. An attempt that ends at its own
        timeout before the run's deadline is a lost attempt like a network failure (charged at
        its worst case, retried within `attempts`); only reaching the run's deadline is the
        wall stop."""
        payload_bytes = len(json.dumps({"messages": messages, "tools": tools}).encode())
        for i in range(attempts):
            mt, to = self.budget.call_limits(model, payload_bytes, len(messages), max_tokens, timeout)
            tok = self.budget.reserve(model, payload_bytes, len(messages), mt)
            try:
                r = chat(model, messages, purpose, tools=tools, max_tokens=mt, timeout=to, retries=0,
                         deadline=self.budget.deadline(), **extra)
            except DeadlineReached as e:
                self.budget.lost(tok)
                left = self.budget.remaining_wall()
                if left is not None and left < 1:
                    self.budget.stop = "wall"
                    raise BudgetExceeded("wall")
                self.log(kind="api_error", status=0, body=f"attempt timeout: {e.body}"[:300], attempt=i)
                if i < attempts - 1:
                    continue
                raise
            except APIError as e:
                self.budget.lost(tok)
                if e.status in (0, 429, 500, 502, 503, 504) and i < attempts - 1:
                    self.log(kind="api_error", status=e.status, body=e.body[:300], attempt=i)
                    self.pause(min(60, 5 * 2 ** i))
                    continue
                raise
            u = r.get("usage") or {}
            self.budget.settle(tok, u)
            return r, u

    def pause(self, seconds):
        """Back off after a transient error, never past the deadline."""
        left = self.budget.remaining_wall()
        time.sleep(seconds if left is None else max(0.0, min(seconds, left)))

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
                      r"(?:theorem|lemma|def|instance|abbrev|structure|inductive)\s+([^\s:({\[]+)", re.M)

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
        if self.budget.past_deadline() and not why.startswith(("revert", "restore")):
            self.budget.stop = "wall"
            raise BudgetExceeded("wall")
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
        src = self._source()
        r = judge.in_container(self.ws, f"lake build Solution 2>&1 | tail -c {tail}", timeout=600)
        if "error:" not in r["output_tail"]:
            self.last_good = src
        return r

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
                    # Move the proved theorem to the end so it follows the helpers it uses;
                    # kept only if the whole file still compiles.
                    before = self._source()
                    removed, _ = self._replace_in(before, name, "")
                    moved, _ = self._replace_in(removed, name, chunk)
                    self._save(moved, f"banked {name}")
                    if "error:" in self.compile(2000)["output_tail"]:
                        self._save(before, f"revert banked {name}")
                    else:
                        banked.append(name)
            src = self._source()
            existing = {m.group(1).split(".")[-1]: m.start() for m in self.DECL.finditer(src)}
        return banked

    def theorem_status(self, names=None):
        """Per-declaration status from `#print axioms` on the compiled candidate. A status of
        every required theorem also updates the best compiling version seen so far."""
        whole = not names
        names = names or self.theorems
        src = self._source()
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
        if whole and judge.TIMEOUT_MARK not in r["output_tail"]:
            self.note_best(status, src)
        return status

    def note_best(self, status, src):
        """Remember the compiling version that proves the most required theorems (the newest
        one on ties)."""
        score = sum(v == "PROVED" for v in status.values())
        if self.best is None or score >= self.best[0]:
            self.best = (score, self.version, src)

    def best_score(self):
        return self.best[0] if self.best else 0

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
        try:
            r, u = s.call(model, messages, f"repair:{s.task.id}:{label}:turn{turn}", tools=tools, **extra)
        except APIError as e:
            s.log(kind="api_error", status=e.status, body=e.body[:300])
            if e.status in (0, 429, 500, 502, 503, 504):
                s.pause(20)
                continue
            return False, messages
        msg = r["choices"][0]["message"]
        assistant = {"role": "assistant", "content": msg.get("content") or ""}
        if msg.get("tool_calls"):
            assistant["tool_calls"] = msg["tool_calls"]
        messages.append(assistant)
        calls = msg.get("tool_calls") or []
        s.log(kind="turn", label=label, turn=turn, model=model, tools=[c["function"]["name"] for c in calls],
              text=(msg.get("content") or "")[:2000], usage=u)
        print(f"[{label}] turn {turn}: {[c['function']['name'] for c in calls]}", flush=True)
        if not calls:
            messages.append({"role": "user", "content": "Continue with the tools."})
            continue
        for c in calls:
            if s.budget.past_deadline():
                s.budget.stop = "wall"
                raise BudgetExceeded("wall")
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
            t_tool = time.monotonic()
            result = fn() if fn else f"error: tool {name} is not available in this phase"
            s.log(kind="tool", label=label, name=name,
                  args={k: (v if len(str(v)) <= 4000 else str(v)[:4000] + " [truncated]") for k, v in args.items()},
                  result=result[:4000], ms=int((time.monotonic() - t_tool) * 1000), version=s.version)
            print(f"   {name} -> {result[:150]!r}", flush=True)
            messages.append({"role": "tool", "tool_call_id": c["id"], "content": result})
        if done():
            return True, messages
    return done(), messages


def spec_text(s):
    return "\n\n".join(f"=== {p} ===\n{s.read_file(p)}" for p in s.task.readable[:-1])


def orchestrate(s, a):
    system = task_brief(s.task, s.mode) + WORKFLOW
    spec = spec_text(s)
    impl = s.mode == "implement"
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
    user0 = (f"{spec}\n\n=== candidate/Solution.lean (current, {'placeholder' if impl else 'buggy'}) ===\n{s._source()}\n\n"
             f"Phase 1 of 2: {'implement' if impl else 'fix'} {defs} so it meets the requirements. Keep every required theorem in the file "
             "(use `sorry` proofs for now). Write the file with write_solution, then call run_tests until it reports PASS.")
    ok0 = tests_ok["v"] or dialog(s, a.model, a.effort, system, user0, {"write_solution", "run_tests", "read_file"},
                                  a.phase0_turns, lambda: tests_ok["v"], "implement")[0]
    s.log(kind="phase", phase="implement", ok=ok0)
    if ok0:
        structured(s, a, system, spec)
    if not s.accepted:
        whole_file(s, a, impl)


def whole_file(s, a, impl):
    """Phase 3: spend the rest of the budget on whole-file repair with the protocol of the
    compile-and-retry baseline. It starts from the best compiling version, with helper
    theorems that nothing uses removed, and the run's result remains the best version
    (finish), so a rewrite that loses proofs cannot replace them."""
    import baseline
    s.log(kind="phase", phase="whole-file")
    if s.best and s.best[2] != s._source():
        s._save(s.best[2], f"restore best version {s.best[1]} ({s.best[0]} proved)")
    compact(s)
    baseline.run(s, argparse.Namespace(model=a.model, effort=a.effort, max_turns=200),
                 state="current, partly implemented" if impl else "current, partly repaired", track_best=True)


def progress(s):
    """(required theorems proved, helper theorems with a complete proof of their own)."""
    st = s.check_status()
    helpers = [m.group(1).split(".")[-1] for m in s.DECL.finditer(s._source())
               if re.search(r"\b(?:theorem|lemma)\s", m.group(0))]
    return (sum(v == "PROVED" for v in st.values()),
            sum(1 for n in helpers if n not in s.theorems and own_sorry_free(s, n)))


def structured(s, a, system, spec):
    """Phase 1: one short direct dialog per obligation, in the task's listed order, which
    settles the easy ones. Phase 2: rounds that first design one proof architecture for
    everything still open (shared invariants, helper lemmas, and the required theorems
    derived from them, checked by Lean before it is kept), then resolve every open
    declaration, decomposing hard ones with the planner (A2); repeated while a round
    makes progress."""
    status = s.check_status()
    for t in s.theorems:
        if status.get(t) == "PROVED" or own_sorry_free(s, t):
            continue
        prove_target(s, a, system, spec, t, a.pass1_turns, "pass1")
        status = s.check_status()
    pending = [t for t, v in s.check_status().items() if v != "PROVED"]
    for rnd in range(a.rounds):
        if not pending:
            break
        before = progress(s)
        s.tried = set()
        if a.architect != "none":
            architect(s, a, spec, pending, rnd)
        for t in pending:
            resolve(s, a, system, spec, t, 0)
        prune(s)
        pending = [t for t, v in s.check_status().items() if v != "PROVED"]
        after = progress(s)
        s.log(kind="round", round=rnd, before=before, after=after, pending=pending)
        if after <= before:
            break
    s.check()


DECL_TEXT = (r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
             r"(?:theorem|lemma|def|abbrev|instance|structure|inductive)\s+{name}(?=[\s:({{\[]).*?(?=^{boundary})")


def decl_text(s, name, src=None):
    m = re.search(DECL_TEXT.format(name=re.escape(name), boundary=s.boundary),
                  s._source() if src is None else src, re.S | re.M)
    return m.group(0) if m else ""


def own_sorry_free(s, name):
    text = decl_text(s, name)
    return bool(text) and "sorry" not in text


def pending_deps(s, name):
    """Helper declarations still proved by `sorry` that `name`'s proof uses, directly or
    through helpers whose own proofs are complete, in file order."""
    names = [m.group(1).split(".")[-1] for m in s.DECL.finditer(s._source())]
    names = [n for n in dict.fromkeys(names) if n not in s.theorems]
    out, seen, todo = [], {name}, [name]
    while todo:
        body = decl_text(s, todo.pop())
        for n in names:
            if n in seen or not re.search(rf"(?<![\w.]){re.escape(n)}(?![\w?!'])", body):
                continue
            seen.add(n)
            if own_sorry_free(s, n):
                todo.append(n)
            else:
                out.append(n)
    return [n for n in names if n in out]


def resolve(s, a, system, spec, name, depth, plan_text=""):
    """Make `name` sorry-free: try directly, then decompose with the planner, then resolve
    the open helpers its proof uses. `depth` is the dependency nesting (labels only); the
    planner nesting is bounded by --max-depth through each declaration's plan level:
    required theorems 0, architecture helpers 1, a plan's lemmas one more than the
    declaration they were planned for. Each declaration is attempted once per round. When
    an earlier direct dialog on `name` failed and a planner is available, the
    decomposition comes first."""
    if name in s.tried:
        return own_sorry_free(s, name) and not pending_deps(s, name)
    s.tried.add(name)
    level = s.level.get(name, 0)
    can_plan = a.planner != "none" and level < a.max_depth
    if not own_sorry_free(s, name) and not (can_plan and name in s.notes):
        prove_target(s, a, system, spec, name, a.obligation_turns, f"d{depth}", plan_text)
    if not own_sorry_free(s, name) and can_plan:
        lemmas, text = plan(s, a, spec, name, s.plan_count)
        for l in lemmas:
            s.level[l] = level + 1
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


def compact(s):
    """Remove helper theorems that nothing else in the file mentions, proved or not, so that
    whole-file rewrites stay short. Declarations with attributes are kept (simp lemmas can
    be used without being named). Kept only if the file still compiles and proves as many
    required theorems."""
    before = s._source()
    want = s.best_score()
    src, removed, changed = before, [], True
    while changed:
        changed = False
        lines = src.split("\n")
        for m in list(s.DECL.finditer(src)):
            n = m.group(1).split(".")[-1]
            if n in s.theorems or not re.search(r"\b(?:theorem|lemma)\s", m.group(0)) or "@[" in m.group(0):
                continue
            line = src[:m.start()].count("\n")
            if line > 0 and lines[line - 1].lstrip().startswith("@["):
                continue
            text = decl_text(s, n, src)
            if text and not re.search(rf"(?<![\w.]){re.escape(n)}(?![\w?!'])", src.replace(text, "")):
                src, _ = s._replace_in(src, n, "")
                removed.append(n)
                changed = True
                break
    if not removed:
        return
    s._save(src, f"compact: removed {len(removed)} unused helper theorems")
    st = s.check_status()
    if "ERROR" in st.values() or sum(v == "PROVED" for v in st.values()) < want:
        s._save(before, "revert compact")
        return
    s.log(kind="compact", removed=removed)


STRUCTURE_GUIDANCE = """How to structure proofs of requirements like these:
- A requirement that quantifies over every sequence of operations or events (a fold over a list) is proved through an invariant: one predicate on states that holds at the start, is preserved by every single step, and implies the requirement. Prove preservation with one lemma per operation or event constructor, then the statement for every list by induction on the list (generalizing the starting state, or with an induction lemma the spec provides), then derive the requirement in a few lines.
- The invariant is usually stronger than the requirement. Add what a single step needs: equalities between the implementation's state and the quantities the specification computes, bounds that are preserved, lengths, index ranges and well-formedness of every record. Several requirements can share one invariant.
- For an upper bound on a quantity that only accumulates, prove a potential inequality instead: the accumulated amount plus everything still owed is at most the starting amount plus everything added since; each step then only moves value from owed to accumulated or adds new value.
- When a requirement starts from a state reached by an earlier sequence, state the invariant for every reachable state and apply it at the intermediate state; a fold over `l₁ ++ l₂` is a fold over `l₂` starting from the result of `l₁`.
- A requirement about a single call follows from a lemma that computes that call's result: unfold the definition once and case on its branches."""


# Planner calls are priced far above the prover's, and every attempt is reserved at its worst
# case (max_tokens of output) until it settles; a failed attempt keeps that charge. Observed
# planner completions stay below 15,000 tokens, so the cap and the retries are kept small.
PLANNER_MAX_TOKENS = 20000
PLANNER_ATTEMPTS = 2

PLANNER_SYSTEM = """You are a Lean 4 proof architect (Lean v4.35.0 core library only, no Mathlib).
Given a specification, a candidate implementation, and a required theorem that a prover failed to prove,
you design a chain of helper lemmas that makes the proof routine. Each lemma must be TRUE, stated in
Lean 4 syntax that elaborates against the given file, and small enough to prove by induction or simp/omega.
Prefer general lemmas over specific ones. Avoid Mathlib names (no Finset, no linarith, no BigOperators)."""

ARCHITECT_SYSTEM = """You are a Lean 4 proof architect (Lean v4.35.0 core library only, no Mathlib).
Given a specification, a candidate implementation and the required theorems that are not yet proved,
you design how they are proved together: shared definitions such as invariants, helper lemmas that are
TRUE and each small enough for one focused proof, and the derivation of each required theorem from them.
Everything you write must elaborate against the given file. Avoid Mathlib names (no Finset, no linarith,
no BigOperators)."""


def notes_text(s, name, limit=1600):
    notes = s.notes.get(name) or []
    return "\n".join(f"- {n}" for n in notes)[-limit:]


def remember(s, name, messages):
    """Keep the end of a dialog that did not prove `name`: the model's last words and the
    last tool result, for the next attempt at the same declaration and for the architect."""
    said = next((m["content"] for m in reversed(messages) if m["role"] == "assistant" and m.get("content")), "")
    got = next((m["content"] for m in reversed(messages) if m["role"] == "tool"), "")
    note = said.strip()[:600]
    if got:
        note += ("\n  Last tool result: " if note else "Last tool result: ") + got.strip()[-1000:]
    if note:
        s.notes[name] = (s.notes.get(name, []) + [note])[-2:]


def outline(s, keep=()):
    """The candidate with the proofs of proved theorems replaced by a marker, so prompts stay
    short; definitions, the declarations in `keep` and anything that still uses sorry are
    shown in full. The full file stays available through read_file."""
    src = s._source()
    pat = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(?:theorem|lemma)\s+([^\s:({\[]+).*?"
                     rf"(?=^{s.boundary})", re.S | re.M)
    pieces, pos = [], 0
    for m in pat.finditer(src):
        name, text = m.group(1).split(".")[-1], m.group(0)
        head = re.match(r"(.*?):=\s*by\b", text, re.S)
        if name in keep or "sorry" in text or not head:
            continue
        pieces += [src[pos:m.start()], head.group(1).rstrip() + " := by\n  -- proved; proof omitted here\n\n"]
        pos = m.end()
    return "".join(pieces) + src[pos:]


def split_decls(s, code):
    """Top-level declarations of a code block as (name, text), comments removed."""
    code = re.sub(r"/-.*?-/", "", code, flags=re.S)
    lines = code.strip("\n").split("\n")
    starts = [i for i, l in enumerate(lines) if s.DECL.match(l)]
    out = []
    for k, i in enumerate(starts):
        a = i
        while a > 0 and lines[a - 1].startswith("@["):
            a -= 1
        b = starts[k + 1] if k + 1 < len(starts) else len(lines)
        while b - 1 > a and (lines[b - 1].startswith("@[") or not lines[b - 1].strip()):
            b -= 1
        text = "\n".join(lines[a:b]).strip("\n")
        if text.strip() not in ("", s.end) and not text.startswith(("namespace", "end ")):
            out.append((s.DECL.match(lines[i]).group(1).split(".")[-1], text.replace(f"\n{s.end}", "")))
    return out


def install_architecture(s, code, status):
    """Install a proof architecture into the current source. New definitions and helper
    lemmas are appended in the given order (an existing helper that still uses sorry is
    replaced; a proved one is kept); a required theorem that is not PROVED takes the given
    proof under its locked statement. Returns (source, helpers left as sorry, required
    theorems given a proof)."""
    src = s._source()
    helpers, derived, append = [], [], []
    for name, text in split_decls(s, code):
        if name in s.theorems:
            if status.get(name) == "PROVED" or "sorry" in text:
                continue
            head = re.match(r"(.*?):=", decl_text(s, name, src), re.S)
            body = re.match(r".*?(:=.*)$", text, re.S)
            if head and body:
                src, _ = s._replace_in(src, name, head.group(1).rstrip() + " " + body.group(1))
                derived.append(name)
            continue
        cur = decl_text(s, name, src)
        if cur and "sorry" not in cur:
            continue
        if cur:
            src, _ = s._replace_in(src, name, "")
        append.append(text)
        if "sorry" in text and re.search(r"\b(?:theorem|lemma)\s", text.split("\n")[0] + " "):
            helpers.append(name)
    for text in append:
        lines = src.split("\n")
        ends = [i for i, l in enumerate(lines) if l.startswith(s.end)]
        e = ends[-1] if ends else len(lines)
        src = "\n".join(lines[:e] + text.split("\n") + [""] + lines[e:])
    return src, helpers, derived


def stuck_text(s, limit=6):
    """Helper theorems in the file that still use sorry, with notes from failed attempts."""
    out = []
    for m in s.DECL.finditer(s._source()):
        n = m.group(1).split(".")[-1]
        if n in s.theorems or own_sorry_free(s, n) or not re.search(r"\b(?:theorem|lemma)\s", m.group(0)):
            continue
        stmt = re.split(r":=\s*(?:by\b|sorry)", decl_text(s, n), maxsplit=1)[0].strip()
        out.append(f"`{stmt}`" + (f"\n  Attempts so far:\n{notes_text(s, n, 900)}" if n in s.notes else ""))
    return "\n".join(out[:limit])


def statement(s, t):
    m = re.search(rf"theorem\s+{re.escape(t)}\s*:[^\n]*", s.read_file(f"{s.task.spec_dir}/Challenge.lean"))
    return m.group(0).replace(" := sorry", "").strip() if m else t


def architect(s, a, spec, pending, rnd):
    """Ask for one proof architecture covering every pending required theorem and install
    it. It is kept only if the whole file compiles with it: the required theorems it
    derives then follow from its helper lemmas, which become targets of their own."""
    if a.architect == "auto":
        model = a.planner if a.planner != "none" else a.model
    else:
        model = a.architect
    status = s.check_status()
    defs = ", ".join(f"`{d}`" for d in s.task.definitions)
    req_notes = "\n".join(f"Earlier attempts at {t}:\n{notes_text(s, t, 900)}" for t in pending if t in s.notes)
    stuck = stuck_text(s)
    user = (f"{spec}\n\n=== candidate/Solution.lean (current; proofs of proved theorems omitted) ===\n{outline(s)}\n\n"
            f"Requirement status: {', '.join(f'{k}={v}' for k, v in status.items())}\n\n"
            "Required theorems not yet proved:\n" + "\n".join(f"- `{statement(s, t)}`" for t in pending) + "\n\n"
            + (f"{req_notes}\n\n" if req_notes else "")
            + (f"Helper lemmas in the file that are still unproved (restate or replace them if they are false or too hard):\n{stuck}\n\n" if stuck else "")
            + f"Design the proof of these required theorems together.\n{STRUCTURE_GUIDANCE}\n\n"
            "Reply with (1) a short plan in prose: the shared facts or invariant and how each required theorem follows, "
            "then (2) exactly one ```lean code block, inserted inside "
            f"`namespace {s.ns}` after the current helpers, containing in dependency order: new definitions you need, with "
            "complete bodies; helper lemmas, each `theorem <name> ... := by sorry`, each small enough for one focused proof "
            "(one operation or one case where possible); and every required theorem above that follows from them, with "
            "exactly its statement and a complete proof that uses the helpers and contains no sorry. New names start with "
            f"`arch{rnd}_` and contain no `?` or `!`. You may use every declaration already in the file without restating "
            f"it. Do not change {defs}.")
    messages = [{"role": "system", "content": ARCHITECT_SYSTEM}, {"role": "user", "content": user}]
    extra = {} if a.planner_effort == "default" else {"reasoning_effort": a.planner_effort}
    for tries in range(3):
        try:
            limits = {} if model == a.model else {"max_tokens": PLANNER_MAX_TOKENS, "attempts": PLANNER_ATTEMPTS}
            r, _ = s.call(model, messages, f"arch:{s.task.id}:{rnd}:{tries}", timeout=900, **limits, **extra)
        except APIError as e:
            s.log(kind="api_error", status=e.status, body=e.body[:300])
            if model != a.model:   # the planner is failing: the prover designs this round instead
                s.log(kind="architect_fallback", round=rnd, model=a.model)
                model = a.model
            else:
                s.pause(20)
            continue
        text = r["choices"][0]["message"].get("content") or ""
        messages.append({"role": "assistant", "content": text})
        m = re.search(r"```lean\s*\n(.*?)```", text, re.S)
        if not m:
            messages.append({"role": "user", "content": "Your reply had no ```lean code block. Reply again in the required format."})
            continue
        before = s._source()
        new, helpers, derived = install_architecture(s, m.group(1), status)
        if new == before:
            messages.append({"role": "user", "content": "Nothing in the code block was new: every declaration in it already exists "
                             "and is proved. Reply with helper lemmas and derivations for the unproved required theorems."})
            continue
        s._save(new, f"architect {rnd}")
        out = s.compile(8000)
        if "error:" in out["output_tail"]:
            s._save(before, f"revert architect {rnd}")
            messages.append({"role": "user", "content": "The file does not compile with your code, so nothing was kept. Fix it and "
                             "reply with the complete corrected code block. Compiler output:\n" + s._clean(out["output_tail"])[-4000:]})
            continue
        if not derived and tries < 2:
            s._save(before, f"revert architect {rnd}")
            messages.append({"role": "user", "content": "Your code compiles but derives none of the unproved required theorems, so "
                             "nothing was kept. Include each required theorem with exactly its statement and a complete proof "
                             "from your helper lemmas."})
            continue
        prose = text[: m.start()].strip()[-3000:]
        s.targets.update(helpers)
        for h in helpers:
            s.level[h] = 1
        for h in helpers:
            s.plan_for[h] = prose
        (s.out / f"arch_{rnd}.md").write_text(text)
        s.log(kind="architect", round=rnd, attempt=tries, model=model, helpers=helpers, derived=derived,
              prose=prose[:3000], code=m.group(1)[:8000])
        print(f"[architect {rnd}] derived {derived}, helpers {helpers}", flush=True)
        return helpers, derived
    s.log(kind="architect", round=rnd, model=model, helpers=[], derived=[], failed=True)
    return [], []


def plan(s, a, spec, t, attempt):
    """Ask the planner model for helper lemma statements; install them as sorry targets."""
    stmt = re.search(rf"theorem\s+{re.escape(t)}\s*:[^\n]*",
                     s.read_file(f"{s.task.spec_dir}/Challenge.lean") + s._source())
    tried = notes_text(s, t)
    user = (f"{spec}\n\n=== candidate/Solution.lean (current; proofs of proved theorems omitted) ===\n{outline(s, {t})}\n\n"
            f"The prover could not prove `{stmt.group(0).replace(' := sorry', '') if stmt else t}`.\n"
            + (f"Its last attempts ended like this:\n{tried}\n" if tried else "")
            + f"\n{STRUCTURE_GUIDANCE}\n\n"
            "Reply with (1) a short proof plan in prose, then (2) exactly one ```lean code block containing 2 to 6 "
            "helper lemmas, each written as `theorem <unique_name> ... := by sorry`, in dependency order, inside no "
            f"namespace (the code is inserted inside `namespace {s.ns}`). Use names prefixed with `plan"
            f"{attempt}_` and no `?` or `!` in names.")
    extra = {} if a.planner_effort == "default" else {"reasoning_effort": a.planner_effort}
    for tries in range(3):
        try:
            r, _ = s.call(a.planner, [{"role": "system", "content": PLANNER_SYSTEM}, {"role": "user", "content": user}],
                          f"plan:{s.task.id}:{t}:{attempt}", timeout=900, max_tokens=PLANNER_MAX_TOKENS,
                          attempts=PLANNER_ATTEMPTS, **extra)
        except APIError as e:
            s.log(kind="api_error", status=e.status, body=e.body[:300])
            return [], ""   # no plan this time; the target keeps its direct attempts
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
        for n in names:
            s.plan_for[n] = prose
        (s.out / f"plan_{t}_{attempt}.md").write_text(text)
        s.log(kind="plan", theorem=t, attempt=attempt, lemmas=names, model=a.planner, prose=prose[:3000], code=code[:6000])
        print(f"[plan {t}] {names}", flush=True)
        return names, prose
    return [], ""


def prove_target(s, a, system, spec, t, budget, label, plan_text=""):
    src = s._source()
    m = re.search(rf"theorem\s+{re.escape(t)}\b[^\n]*(?:\n(?!theorem|lemma|def|end )[^\n]*)*", src)
    stmt = (m.group(0).split(":= by")[0].split(":= sorry")[0] if m else t).strip()
    status = s.check_status()
    defs = ", ".join(f"`{d}`" for d in s.task.definitions)
    plan_text = plan_text or s.plan_for.get(t, "")
    tried = notes_text(s, t)
    user = (f"{spec}\n\n=== candidate/Solution.lean (current; proofs of proved theorems omitted, read_file shows the "
            f"full file) ===\n{outline(s, {t})}\n\n"
            f"Current requirement status: {', '.join(f'{k}={v}' for k, v in status.items())}\n\n"
            + (f"Proof plan from the architect:\n{plan_text}\n\n" if plan_text else "")
            + (f"Earlier attempts at this target ended like this (the file may have changed since):\n{tried}\n\n" if tried else "")
            + f"Your task now: prove `{stmt}`. Do not change {defs} or anything already proved. "
            "Develop the proof with try_snippet; a clean snippet that proves "
            f"`{t}` replaces its sorry automatically. You may use the other helper lemmas in the file even if "
            "they are still sorry; they are proved separately.")
    def own_proof_done():
        """The target's own proof is sorry-free and the file compiles (dependencies may be pending)."""
        m2 = re.search(rf"^(?:private\s+)?theorem\s+{re.escape(t)}\b.*?(?=^{s.boundary})", s._source(), re.S | re.M)
        return bool(m2) and "sorry" not in m2.group(0) and s.check_status([t]).get(t) != "ERROR"
    ok, messages = dialog(s, a.model, a.effort, system, user, {"try_snippet", "replace_declaration", "check", "read_file"},
                          budget, own_proof_done, f"{label}:{t}")
    if not ok:
        remember(s, t, messages)
    s.log(kind="obligation", label=label, theorem=t, ok=ok)
    return ok


def finish(s, out, arm, extra, select="newest"):
    """Write summary.json and the final candidate; final judging is done by the evaluator.
    A final file that does not compile is replaced by the newest version that did. With
    select="best" (the harness), the result is instead the compiling version that proves
    the most required theorems, the newest one on ties; the statuses compared were all
    computed during the run. This selection among already produced versions happens after
    the deadline."""
    judge.DEADLINE = None
    if "error:" in s.compile(2000)["output_tail"] and s.last_good is not None:
        s._save(s.last_good, "restore last compiling version")
    status = s.check_status()
    if select == "best" and s.best and s.best[0] > sum(v == "PROVED" for v in status.values()):
        s._save(s.best[2], f"restore best version {s.best[1]} ({s.best[0]} proved)")
        status = s.check_status()
    shutil.copy(s.ws / "candidate/Solution.lean", out / "final.lean")
    writes = [e for e in s.events if e.get("kind") == "write"]
    snapshot = {"sha256": taskmod.sha256(out / "final.lean"), "version": s.version,
                "selected": writes[-1]["why"] if writes else "start candidate",
                "written_at_s": round(writes[-1]["t"] - s.events[0]["t"], 1) if writes else 0.0}
    summary = {"task": s.task.id, "arm": arm, "model": s.model, **extra, "final_snapshot": snapshot,
               "accepted_in_session": s.accepted,
               "versions": s.version, "budget": s.budget.summary(), "final_status": status}
    (out / "summary.json").write_text(json.dumps(summary, indent=2))
    shutil.rmtree(s.ws, ignore_errors=True)
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", help="task id or directory (default: flagship)")
    ap.add_argument("--model", default="muse-spark-1.3-contributor")
    ap.add_argument("--mode", default="repair", choices=["repair", "implement", "orchestrated", "free"],
                    help="repair (default): start from the task's buggy candidate with its issue report; "
                         "implement: start from a stub generated from the locked challenge and implement "
                         "the definitions from the spec. 'orchestrated' and 'free' are kept for "
                         "compatibility and mean --mode repair with that --loop")
    ap.add_argument("--loop", default="orchestrated", choices=["orchestrated", "free"])
    ap.add_argument("--max-turns", type=int, default=40, help="free mode only")
    ap.add_argument("--phase0-turns", type=int, default=12)
    ap.add_argument("--pass1-turns", type=int, default=8, help="turns of the first direct dialog per obligation")
    ap.add_argument("--obligation-turns", type=int, default=12)
    ap.add_argument("--start", help="starting candidate (default: the task's candidate/Solution.lean)")
    ap.add_argument("--effort", default="medium", choices=["low", "medium", "high", "default"])
    ap.add_argument("--planner", default="muse-wonder-1.0", help="planner model, or 'none' (arm A1)")
    ap.add_argument("--planner-effort", default="high", choices=["low", "medium", "high", "default"])
    ap.add_argument("--architect", default="auto",
                    help="model that designs the joint proof architecture at the start of each phase 2 round: "
                         "'auto' (the planner, or the prover model when --planner none), a model id, or 'none'")
    ap.add_argument("--select", default="best", choices=["best", "newest"],
                    help="final candidate: the compiling version proving the most required theorems, or the newest")
    ap.add_argument("--max-depth", type=int, default=2)
    ap.add_argument("--rounds", type=int, default=3, help="phase 2 rounds while they make progress")
    ap.add_argument("--budget-usd", type=float, help="cap at standard-tier list prices")
    ap.add_argument("--budget-wall", type=float, help="wall-clock cap in seconds")
    ap.add_argument("--out", help="run directory (default: runs/repair-<time>-<task>-<arm>)")
    a = ap.parse_args()
    if a.mode in ("orchestrated", "free"):
        a.loop, a.mode = a.mode, "repair"
    if a.mode == "implement" and a.start:
        ap.error("--start cannot be combined with --mode implement (the start is generated)")
    task = taskmod.load(a.task)
    arm = "A1" if a.planner == "none" else "A2"
    kind = "implement" if a.mode == "implement" else "repair"
    out = pathlib.Path(a.out) if a.out else \
        ROOT / "runs" / f"{kind}-{time.strftime('%Y%m%d-%H%M%S')}-{task.id}-{arm}"
    out.mkdir(parents=True, exist_ok=True)
    start = a.start or task.start
    if a.mode == "implement":
        start = out / "start.lean"
        start.write_text(stub_candidate(task))
    s = Session(task, a.model, start, out, Budget(a.budget_usd, a.budget_wall), mode=a.mode)
    s.log(kind="start", arm=arm, **vars(a))
    try:
        if a.loop == "orchestrated":
            orchestrate(s, a)
        else:
            dialog(s, a.model, a.effort, task_brief(task, a.mode) + WORKFLOW,
                   "Begin. The current candidate is candidate/Solution.lean.",
                   {t["function"]["name"] for t in tools_for(task)}, a.max_turns, lambda: s.accepted, "free")
    except BudgetExceeded as e:
        s.log(kind="budget_stop", reason=str(e))
        print(f"budget exhausted: {e}", flush=True)
    summary = finish(s, out, arm, {"mode": a.loop, "task_mode": a.mode, "effort": a.effort, "planner": a.planner,
                                   "architect": a.architect}, select=a.select)
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
