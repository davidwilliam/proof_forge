"""The harness's proof tools for the ProofForge MCP server's `full` profile, on the agent's workspace.

Each tool calls the module the repair agent uses (agents/leanserver.py, agents/portfolio.py,
agents/refute.py, agents/ledger.py, harness/fin_lib.py) through a session object that behaves as
agents/repair.py's Session for those modules, with three differences:

  * the candidate is the agent's file (`candidate/Solution.lean` of the workspace), read afresh on
    every call and never written: a tool reports Lean's answer and the agent edits the file;
  * Lean runs in a shadow copy of the workspace (outside it, made once per server, the candidate
    copied in before each tool), so that probe files, a statement under test and the persistent
    Lean server never touch the agent's workspace or its build directory;
  * nothing is banked: the tactic portfolio returns the closing proof text, the refutation probe
    returns the counterexample, the ledger re-check returns the declarations that compile.

No model is called and no dollars are spent. Lean runs through judge.in_container (the pinned
image, no network, the host's container slots).
"""
import hashlib, json, os, pathlib, re, shutil, subprocess, sys, tempfile, threading, time

ROOT = pathlib.Path(__file__).resolve().parents[2]
for p in (ROOT / "agents", ROOT / "harness"):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))
import fin_lib, judge  # noqa: E402
import budget as budgetmod  # noqa: E402
import repair, leanserver, portfolio, refute, ledger  # noqa: E402

PRIOR_DIR = ".proofforge/prior-attempts"   # where prior_attempts puts files for the agent to read
PROBE_NAME = "pf_refute_statement"
LSP_IDLE_S = float(os.environ.get("PF_LSP_IDLE", "300"))   # a persistent Lean server idle this long is stopped
RESULT_CHARS = 12000


class ReadOnly(RuntimeError):
    pass


class WorkspaceSession(repair.Session):
    """repair.Session for the harness modules, on a shadow copy of the agent's workspace."""
    goal_tool = True
    topdown = False

    def __init__(self, ws, task):
        self.task = task
        self.ns, self.theorems = task.ns, task.theorems
        self.end = f"end {task.ns}"
        self.agent_ws = pathlib.Path(ws).resolve()
        self.ws = None                       # the shadow, made on first use (shadow())
        self.out = None
        self.budget = budgetmod.Budget()     # no caps here: the runner stops Muse Code, and with it this server
        self.library = (self.agent_ws / fin_lib.VENDOR).is_dir()
        self._lib_index = None
        self.version = 0
        self.targets, self.events, self.compiled = set(), [], {}
        self.refuted, self.notes, self.extra_tools = {}, {}, set()
        self.skeletons, self.prior_notes, self.resume_goals = [], {}, []
        self.portfolio_seen = set()
        self.refute_samples = refute.SAMPLES
        self.source_override = None
        self.saved = None
        self.boundary = (r"(?:@\[|/--|private |protected |noncomputable |theorem |lemma |def |instance |abbrev "
                         rf"|structure |inductive |open |{re.escape(self.end)})")

    @property
    def lib_index(self):
        if self.library and self._lib_index is None:
            self._lib_index = fin_lib.Index.load()
        return self._lib_index

    # The agent's file: read, never written.
    def _source(self):
        if self.source_override is not None:
            return self.source_override
        return (self.agent_ws / "candidate/Solution.lean").read_text()

    def _save(self, text, why):
        raise ReadOnly("the ProofForge tools never change candidate/Solution.lean")

    def log(self, **kw):
        kw["t"] = round(time.time(), 3)
        self.events.append(kw)
        del self.events[:-200]

    # Shadow workspace
    def shadow(self, candidate_text=None):
        """The shadow copy, with the agent's candidate directory (or `candidate_text` as
        candidate/Solution.lean) copied in. Locked files and the vendored library are copied once."""
        if self.ws is None:
            d = pathlib.Path(tempfile.mkdtemp(prefix="pf-mcp-shadow-"))
            for item in self.agent_ws.iterdir():
                if item.name in (".git", ".proofforge", "candidate") or item.suffix == ".lean":
                    continue
                if item.is_dir():
                    shutil.copytree(item, d / item.name, symlinks=True)
                else:
                    shutil.copy2(item, d / item.name)
            self.ws = d
        cand = self.ws / "candidate"
        shutil.rmtree(cand, ignore_errors=True)
        shutil.copytree(self.agent_ws / "candidate", cand, symlinks=False)
        if candidate_text is not None:
            (cand / "Solution.lean").write_text(candidate_text)
        return self.ws

    def close(self):
        leanserver.close(self)
        self.__dict__.pop("lean_server", None)
        if self.ws is not None:
            shutil.rmtree(self.ws, ignore_errors=True)
            self.ws = None


class CarrySession(WorkspaceSession):
    """The session ledger.carry re-checks prior declarations in: `_save` keeps the installed text
    instead of writing the agent's file; every text it keeps is one Lean just compiled without
    errors (ledger.carry keeps a set only after lean_messages finds no error in exactly that text)."""

    def _save(self, text, why):
        self.saved = None if why.startswith("revert") else text

    def compile(self, tail=9000):
        return {"output_tail": "", "exit_code": 0, "elapsed_ms": 0}


def short(name):
    return (name or "").split(".")[-1].strip()


def theorem_text(s, name, src=None):
    text = repair.decl_text(s, short(name), src)
    if text and re.match(rf"^{repair.DECL_PREFIX}(?:theorem|lemma)\s", text):
        return text.rstrip()
    return None


# ---------------------------------------------------------------------------------------------
# goal_at and check_snippet_fast: the persistent Lean session

def goal_at(s, name, line=None):
    s.shadow()
    out = leanserver.goal_at(s, name, line)
    if "(not inside a tactic proof)" in out:
        out += ("\n\nA term-mode `:= sorry` has no proof state: write the proof as `:= by` followed by tactics (or "
                "`:= by sorry`) to see the goal.")
    return out


def library_modules(s, code, src):
    """The ProofForgeFin modules a snippet needs that the candidate does not import (directly or
    through a library module it imports): those declaring a name the snippet uses, fully qualified
    or under a namespace the snippet or the candidate opens, and, for a namespace the snippet opens
    that no such module provides, the module of that name (or the first one declaring in it)."""
    if not s.library or s.lib_index is None:
        return []
    if getattr(s, "_lib_names", None) is None:
        s._lib_names = {e["name"]: e["module"] for e in s.lib_index.entries if e.get("module")}
    names = s._lib_names
    have = set(fin_lib.closure([m for m in fin_lib.imports_of(src) if fin_lib.IMPORT_RE.match(m)]))
    text = fin_lib.strip_comments(code)
    opened = re.findall(r"\bopen\s+(.+?)(?:\s+in\b|$)", text, re.M)
    spaces = [ns for line in opened + re.findall(r"^open\s+(.+?)(?:\s+in\b|$)", fin_lib.strip_comments(src), re.M)
              for ns in line.split() if ns.startswith(fin_lib.LIBRARY)]
    want = []
    for tok in dict.fromkeys(re.findall(r"[A-Za-z_][\w'.!?]*", text)):
        for name in [tok] + [f"{ns}.{tok}" for ns in spaces]:
            mod = names.get(name)
            if mod and mod != name:
                if mod not in have and mod not in want:
                    want.append(mod)
                break
    for ns in dict.fromkeys(ns for line in opened for ns in line.split() if ns.startswith(fin_lib.LIBRARY)):
        mods = have | set(want)
        if any(n.startswith(ns + ".") and m in mods for n, m in names.items()):
            continue
        mod = ns if names.get(ns) == ns else next((m for n, m in names.items() if n.startswith(ns + ".")), None)
        if mod and mod not in want:
            want.append(mod)
    return want


def check_snippet_fast(s, code):
    """One incremental elaboration of the snippet after the candidate on the persistent server.
    Library modules the snippet needs and the candidate does not import (library_modules) are
    imported for the check, and the result says so."""
    s.shadow()
    src = s._source()
    code, hoist, refusal = s._snippet_imports(code or "", src)
    if refusal:
        return refusal
    auto = [m for m in library_modules(s, code, src) if m not in hoist]
    hoist = hoist + auto
    note = ("" if not auto else "\nImported for this check: " + ", ".join(f"`import {m}`" for m in auto)
            + "; candidate/Solution.lean needs the same import before it uses these names.")
    code = s._snippet_opens(code)
    scratch, offset = s.scratch_text(code, hoist)
    r = leanserver.fast_snippet(s, scratch, offset, code)
    if r is None:
        return "error: the persistent Lean session is not available right now; use try_snippet"
    if r[0] is False:
        msgs = [m for m in r[1] if m]
        if msgs == [judge.TIMEOUT_MARK]:
            return "the snippet was stopped at the time limit"
        return "\n".join(msgs)[-6000:] + f"\n({r[2]} ms on the persistent session; the candidate file is unchanged)" + note
    return (f"clean: Lean's persistent session finds no errors and no warnings in the snippet ({r[1]} ms). "
            "Nothing was written; try_snippet or lean_build confirms with a full compile." + note)


# ---------------------------------------------------------------------------------------------
# try_tactics: the tactic portfolio on one open goal, banking nothing

def try_tactics(s, name):
    s.shadow()
    src = s._source()
    nm = short(name)
    if not repair.decl_text(s, nm, src):
        return f"error: no declaration `{name}` in candidate/Solution.lean"
    g = portfolio.goal_of(s, nm, src)
    if g is None:
        return (f"error: `{nm}` is not a theorem of candidate/Solution.lean proved by `sorry`; state it with "
                "`:= by sorry` first")
    results, info = portfolio.run_portfolio(s, [g], src=src)
    res = results.get(nm, {})
    closing, lines = [], []
    for key, _, _ in portfolio.PORTFOLIO:
        r = res.get(key)
        if r is None:
            continue
        if r["ok"]:
            text = portfolio.bank_text(g, key, r)
            if not portfolio.forbidden(text):
                closing.append((key, text))
                lines.append(f"  {key}: closes it" + (f" ({r['ms']} ms)" if r["ms"] else ""))
                continue
        why = "heartbeat limit" if r["limit"] else (r["error"] or "not closed").split("\n")[0][:160]
        lines.append(f"  {key}: {why}")
    s.last_portfolio = {"goal": nm, "tried": sorted(res), "closed_by": closing[0][0] if closing else None,
                        "ms": info["ms"], "stopped": info["stopped"]}
    head = f"Tactic portfolio on `{nm}` ({info['attempts']} attempts, {info['ms'] / 1000:.1f} s of Lean"
    head += ", stopped at its time allowance and retried without exact?/try?)" if info.get("retried") else ")"
    if not closing:
        return head + ": no tactic closes it.\n" + "\n".join(lines)
    key, text = closing[0]
    return (head + f": CLOSED by `{key}`. A renamed copy of the statement compiles with this proof, with no "
            "error and no sorryAx. Replace the declaration with:\n```lean\n" + text + "\n```\n"
            "The candidate file is unchanged.\n" + "\n".join(lines))


# ---------------------------------------------------------------------------------------------
# refute_statement: a proposed statement on concrete values

def statement_decl(statement, name=PROBE_NAME):
    """A theorem declaration with `sorry` from a statement given as `theorem n binders : P`,
    `binders : P`, `: P` or a bare proposition (any `:= proof` is dropped)."""
    text = (statement or "").strip()
    if not text:
        raise ValueError("give a statement")
    head, _ = ledger.split_proof(text)
    text = (head if head is not None else text).strip()
    m = re.match(r"^(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+[^\s:({\[]+\s*", text)
    if m:
        text = text[m.end():]
    if text.startswith(":"):
        text = text[1:].strip()
        return f"theorem {name} : {text} := by\n  sorry"
    if text[:1] in "({[⦃":
        return f"theorem {name} {text} := by\n  sorry"
    return f"theorem {name} : {text} := by\n  sorry"


def refute_statement(s, statement=None, name=None, samples=None):
    src = s._source()
    if bool(statement) == bool(name):
        raise ValueError("give either `statement` (a proposed helper) or `name` (a theorem in candidate/Solution.lean)")
    if name:
        nm = short(name)
        if theorem_text(s, nm, src) is None:
            return f"error: no theorem `{nm}` in candidate/Solution.lean"
        text, label = src, f"`{nm}`"
    else:
        decl = statement_decl(statement)
        body = src.rsplit(s.end, 1)
        if len(body) != 2:
            return f"error: candidate/Solution.lean has no `{s.end}`"
        text = body[0].rstrip("\n") + "\n\n" + decl + f"\n\n{s.end}" + body[1]
        nm, label = PROBE_NAME, "the statement"
    s.shadow(text)
    s.source_override = text
    try:
        res, info = refute.run_probe(s, [nm], samples=samples)
    finally:
        s.source_override = None
    r = res.get(nm, {})
    st = r.get("status")
    s.last_refute = {"name": short(name) if name else None, "status": st or "error"}
    if st == "false":
        return (f"FALSE: {label} does not hold at {r.get('counterexample')} (instance {r.get('instance')} of "
                f"{r.get('tried')} tried). Lean's kernel accepted the refutation, a proof of the negation at this "
                "instance. Do not try to prove it; fix the statement (a missing hypothesis, a bound off by one, "
                "rounding in the other direction).")
    if st == "survived":
        return (f"no counterexample: {label} held on all {r.get('tried')} instances Lean decided "
                f"({r.get('undecided')} undecided). This is evidence, not a proof.")
    if st == "unconfirmed":
        return (f"possibly false: {label} evaluated to false at {r.get('counterexample')}, but the kernel did not "
                f"accept the refutation ({r.get('tried')} tried). Check this instance by hand.")
    if st in ("unsupported", "missing", "error"):
        return f"not sampled: {r.get('reason') or st} (statements need decidable propositions over sampleable types)."
    err = info.get("error") or ""
    if "error:" in err or not res:
        b = judge.in_container(s.ws, "lake build Solution 2>&1 | tail -c 6000", timeout=600)
        out = s._clean(b["output_tail"])
        if "error:" in out:
            return ("not sampled: the candidate" + (" with the statement added" if statement else "")
                    + " does not compile. Lean:\n" + out[-3000:].replace(PROBE_NAME, "<statement>"))
    return "not sampled: the probe gave no result" + (f" ({err[-600:]})" if err else "")


# ---------------------------------------------------------------------------------------------
# search_library with a goal

def search_library(s, index, query, limit=10, goal=None):
    """The library's ranking; with `goal` (a statement, or the name of a declaration in the
    candidate) the goal-aware ranking (conclusion match and usage prior) of harness/fin_lib.py."""
    g = None
    if goal:
        g = goal
        if re.fullmatch(r"[\w.'!?]+", goal.strip()):
            text = repair.decl_text(s, short(goal))
            if text:
                g = ledger.statement(text.rstrip())
    hits = index.search(query or "", limit=limit, goal=g)
    if not hits:
        return "no library declaration matches; try other words or a declaration name"
    return fin_lib.render(hits)


# ---------------------------------------------------------------------------------------------
# prior_attempts: the attempt ledger of earlier runs on this task and spec

class PriorAttempts:
    def __init__(self, paths, task):
        self.paths = [p for p in paths if p]
        self.task = task
        self.loaded = None
        self.cache = {}

    def load(self):
        if self.loaded is None:
            self.loaded = ledger.load_many(self.paths, self.task)
        return self.loaded

    def report(self, s):
        priors, record = self.load()
        src = s._source()
        key = hashlib.sha256(src.encode()).hexdigest()
        if key in self.cache:
            return self.cache[key]
        lines = ["Prior attempts on this task (same task id and locked spec hash; anything else is refused):"]
        for r in record:
            nm = pathlib.Path(r["run_dir"]).name
            led = next((x for x in priors if x.get("run_dir") == r["run_dir"]), None)
            if r["used"] and led:
                fin = led.get("final", {}).get("proved_required") or []
                best = (led.get("best_candidate") or {}).get("proved_required") or []
                lines.append(f"- run {nm}: used; {len(led.get('proved', []))} declarations proved in some compiling "
                             f"version; final file proved {len(fin)} of {len(self.task.theorems)} required theorems"
                             + (f", best compiling version {len(best)}" if len(best) > len(fin) else ""))
            else:
                lines.append(f"- run {nm}: refused ({r['refused']})")
        if not priors:
            text = "\n".join(lines) + "\nNo usable prior attempt."
            self.cache[key] = text
            return text
        # Proved declarations, re-checked by Lean against the current candidate.
        cs = CarrySession(s.agent_ws, self.task)
        cs.ws = s.shadow()
        carried, dropped = ledger.carry(cs, priors)
        d = s.agent_ws / PRIOR_DIR
        d.mkdir(parents=True, exist_ok=True)
        lines.append("")
        if carried:
            rec = {r["name"]: r for led in priors for r in reversed(led.get("proved", []))}
            (d / "Solution-with-carried.lean").write_text(cs.saved)
            lines.append(f"{len(carried)} declarations proved in prior attempts compile with the current "
                         "candidate/Solution.lean (Lean re-checked them just now, no sorry): "
                         + ", ".join(f"`{n}`" for n in carried) + ".")
            lines.append(f"{PRIOR_DIR}/Solution-with-carried.lean is the current file with all of them installed in "
                         "dependency order; it compiles. Copy it over candidate/Solution.lean to take them all, or "
                         "paste the ones you need:")
            body = "\n\n".join(rec[n]["text"].rstrip() for n in carried if n in rec)
            lines.append("```lean\n" + (body if len(body) <= 8000 else body[:8000] + "\n-- [... more in the file above]")
                         + "\n```")
        else:
            lines.append("No prior proved declaration compiles with the current candidate/Solution.lean"
                         + (" (the current file does not compile, so nothing could be re-checked against it)"
                            if not self._compiles(cs, src) else "") + ".")
        if dropped:
            lines.append("Not carried: " + "; ".join(f"`{x['name']}` ({x['reason'][:100]})" for x in dropped[:12])
                         + (f"; {len(dropped) - 12} more" if len(dropped) > 12 else ""))
        for led in priors:
            best = led.get("best_candidate") or {}
            if best.get("text") and best.get("version") != "final":
                nm = pathlib.Path(led["run_dir"]).name
                (d / f"best-{nm}.lean").write_text(best["text"])
                lines.append(f"The best compiling version of run {nm} ({len(best.get('proved_required') or [])} required "
                             f"theorems proved) is in {PRIOR_DIR}/best-{nm}.lean.")
        # Failure notes, and the goals they left open that are still open now.
        goals = ledger.resume_goals(s, priors)
        lines.append("")
        lines.append("What the prior attempts left open and how they failed:\n" + ledger.summary_text(priors, limit=6000))
        if goals:
            lines.append("Still open in the current file: " + ", ".join(f"`{g}`" for g in goals) + ". Do not repeat an "
                         "approach that failed; try a different decomposition, lemma or tactic.")
        text = "\n".join(lines)
        text = text if len(text) <= RESULT_CHARS else text[:RESULT_CHARS] + "\n[... truncated]"
        self.cache[key] = text
        return text

    @staticmethod
    def _compiles(cs, src):
        msgs = ledger.lean_messages(cs, src, name="CarryBase")
        return msgs is not None and not any(sev == "error" for _, sev, _ in msgs)


# ---------------------------------------------------------------------------------------------
# Idle shutdown of the persistent Lean server

class IdleCloser:
    """Stops the session's persistent Lean server after LSP_IDLE_S without a call that used it, so
    that an idle run does not hold a Lean container's memory."""

    def __init__(self, lock, session_fn, idle=LSP_IDLE_S):
        self.lock, self.session_fn, self.idle = lock, session_fn, idle
        self.last = None
        self.thread = None

    def touch(self):
        self.last = time.monotonic()
        if self.thread is None:
            self.thread = threading.Thread(target=self.loop, daemon=True)
            self.thread.start()

    def loop(self):
        while True:
            time.sleep(min(10.0, max(0.5, self.idle / 4)))
            if self.last is None or time.monotonic() - self.last < self.idle:
                continue
            if not self.lock.acquire(blocking=False):
                continue
            try:
                s = self.session_fn()
                srv = s and s.__dict__.get("lean_server")
                if srv is not None and srv.alive() and time.monotonic() - self.last >= self.idle:
                    srv.close()
            finally:
                self.lock.release()
