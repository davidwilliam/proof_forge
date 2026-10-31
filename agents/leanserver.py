"""Persistent Lean session for the repair agent: Lean's own language server (`lean --server`, the
toolchain's LSP server, nothing vendored) in the pinned image, one per repair session.

The server holds one document, `PFSession.lean`, in memory (nothing is written to the
workspace). Its text is either the current candidate or the scratch file of a snippet (the
candidate followed by the snippet, as Session._scratch builds it). Every change is sent as one
incremental edit from the first character that differs, so Lean re-elaborates only the commands
from that point on and reuses the elaboration of everything before it: a snippet after an
unchanged candidate costs the snippet alone, where `lake env lean Scratch.lean` elaborates the
whole candidate again.

Two uses (`--goal-tool on`, the default for A1 and A2; A0 never has it):
  * `goal_at` (a model tool): the proof state (hypotheses and goals) in one declaration of the
    candidate, at each `sorry`, at each error, or before and after a given line, from
    `$/lean/plainGoal`;
  * the fast single-step check of try_snippet: a snippet with an error or a `sorry` is answered
    from the server, with the proof state at each `sorry` of the snippet appended; a snippet the
    server finds clean is compiled as before (`lake env lean`) and only that compile banks it.

Isolation and limits are those of every other Lean run: the same container command as
judge.in_container (no network, 4 GB, 512 processes; directly inside the image with
PF_IN_IMAGE=1), one of the host's container slots held while the server elaborates, every wait
cut at the run's deadline (judge.deadline()), so the time counts against the wall cap. A server
that stops answering is killed and restarted on the next use; a server that cannot start leaves
the session on the compile path.
"""
import json, os, queue, re, signal, subprocess, threading, time

import judge  # noqa: E402  (agents/repair.py puts harness/ on sys.path)

DOC = "PFSession.lean"
START_SECONDS = 120     # the server's `initialize` (after `lake build <spec>`, normally a no-op)
SYNC_SECONDS = 300      # one elaboration, as Session._scratch's compile
GOAL_SECONDS = 60
GOAL_CHARS = 2500       # one rendered proof state in a tool result
RESULT_CHARS = 6000


class ServerError(Exception):
    """The server could not be started or stopped answering; the caller falls back."""


class ServerTimeout(ServerError):
    """An elaboration did not finish within its time limit or the run's deadline."""


def utf16_col(line_text):
    return len(line_text.encode("utf-16-le")) // 2


def position(text, offset):
    """LSP position (0-based line, UTF-16 column) of a character offset."""
    line = text.count("\n", 0, offset)
    start = text.rfind("\n", 0, offset) + 1
    return {"line": line, "character": utf16_col(text[start:offset])}


def codepoint_col(line_text, col16):
    """Character column of a UTF-16 column in one line."""
    n = 0
    for i, ch in enumerate(line_text):
        if n >= col16:
            return i
        n += 2 if ord(ch) > 0xFFFF else 1
    return len(line_text)


class LeanServer:
    def __init__(self, ws, lib):
        self.ws, self.lib = ws, lib
        self.proc = None
        self.name = None
        self.text = None
        self.version = 0
        self.next_id = 0
        self.q = queue.Queue()
        self.diags = []
        self.diags_version = None
        self.stats = {"starts": 0, "start_ms": 0, "syncs": 0, "sync_ms": 0, "full_syncs": 0, "goal_requests": 0,
                      "timeouts": 0, "failures": 0}

    # Process and protocol

    def uri(self):
        return f"file:///work/{DOC}" if not judge.IN_IMAGE else f"file://{self.ws}/{DOC}"

    @staticmethod
    def _limit(seconds):
        d = judge.deadline()
        if d is not None:
            seconds = min(seconds, d - time.monotonic())
        if seconds <= 0:
            raise ServerTimeout("the run's deadline has passed")
        return seconds

    def start(self):
        t0 = time.monotonic()
        threads = os.environ.get("LEAN_NUM_THREADS")
        script = ((f"export LEAN_NUM_THREADS={int(threads)}; " if threads and threads.isdigit() else "")
                  + f"lake build {self.lib} >/dev/null 2>&1; exec lake env lean --server")
        self.name = f"pf-lsp-{os.getpid()}-{time.monotonic_ns()}"
        argv = judge.container_argv(self.ws, script, self.name, interactive=True)
        self.proc = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                     start_new_session=True)
        self.q = queue.Queue()
        threading.Thread(target=self._reader, args=(self.proc, self.q), daemon=True).start()
        self.text, self.version, self.diags, self.diags_version = None, 0, [], None
        try:
            with judge.container_slot() as slot:
                if slot is None:
                    raise ServerTimeout("the run's deadline has passed")
                self.request("initialize", {"processId": None, "rootUri": "file:///work" if not judge.IN_IMAGE
                                            else f"file://{self.ws}", "capabilities": {}},
                             self._limit(START_SECONDS))
            self.notify("initialized", {})
        except ServerError:
            self.close()
            raise
        self.stats["starts"] += 1
        self.stats["start_ms"] += int((time.monotonic() - t0) * 1000)

    @staticmethod
    def _reader(proc, q):
        f = proc.stdout
        try:
            while True:
                headers = {}
                while True:
                    line = f.readline()
                    if not line:
                        q.put(None)
                        return
                    line = line.decode(errors="replace").strip()
                    if not line:
                        break
                    k, _, v = line.partition(":")
                    headers[k.lower()] = v.strip()
                n = int(headers.get("content-length", "0"))
                q.put(json.loads(f.read(n)) if n else {})
        except (OSError, ValueError):
            q.put(None)

    def _write(self, msg):
        b = json.dumps(msg).encode()
        try:
            self.proc.stdin.write(f"Content-Length: {len(b)}\r\n\r\n".encode() + b)
            self.proc.stdin.flush()
        except (OSError, AttributeError) as e:
            raise ServerError(f"the Lean server is not running: {e}")

    def notify(self, method, params):
        self._write({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method, params, timeout):
        self.next_id += 1
        rid = self.next_id
        self._write({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        end = time.monotonic() + timeout
        while True:
            left = end - time.monotonic()
            if left <= 0:
                self.stats["timeouts"] += 1
                self.close()
                raise ServerTimeout(f"{method}: no answer within {timeout:.0f} s")
            try:
                m = self.q.get(timeout=min(left, 5))
            except queue.Empty:
                if self.proc.poll() is not None:
                    self.close()
                    raise ServerError("the Lean server exited")
                continue
            if m is None:
                self.close()
                raise ServerError("the Lean server exited")
            if "method" in m:
                if "id" in m:   # a request from the server (refresh hints and the like): answer null
                    self._write({"jsonrpc": "2.0", "id": m["id"], "result": None})
                elif m["method"] == "textDocument/publishDiagnostics" and m["params"].get("uri") == self.uri():
                    self.diags = m["params"].get("diagnostics") or []
                    self.diags_version = m["params"].get("version")
                continue
            if m.get("id") == rid:
                if "error" in m:
                    raise ServerError(f"{method}: {m['error'].get('message', m['error'])}")
                return m.get("result")

    def close(self):
        p, self.proc = self.proc, None
        self.text = None
        if p is None:
            return
        if not judge.IN_IMAGE and self.name:
            subprocess.run(["docker", "kill", self.name], capture_output=True)
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        try:
            p.wait(timeout=10)
        except subprocess.TimeoutExpired:
            pass

    def alive(self):
        return self.proc is not None and self.proc.poll() is None

    # Document

    def sync(self, text, timeout=SYNC_SECONDS):
        """Make the document `text` and wait until Lean has elaborated it. Returns the diagnostics
        (LSP dicts). Only the part from the first differing character is re-elaborated."""
        if not self.alive():
            self.start()
        t0 = time.monotonic()
        with judge.container_slot() as slot:
            if slot is None:
                raise ServerTimeout("the run's deadline has passed")
            if self.text is None:
                self.version = 1
                self.notify("textDocument/didOpen", {"textDocument": {"uri": self.uri(), "languageId": "lean4",
                                                                      "version": 1, "text": text}})
                self.stats["full_syncs"] += 1
            elif text != self.text:
                old = self.text
                p = 0
                n = min(len(old), len(text))
                while p < n and old[p] == text[p]:
                    p += 1
                self.version += 1
                self.notify("textDocument/didChange", {
                    "textDocument": {"uri": self.uri(), "version": self.version},
                    "contentChanges": [{"range": {"start": position(old, p), "end": position(old, len(old))},
                                        "text": text[p:]}]})
            self.text = text
            self.request("textDocument/waitForDiagnostics", {"uri": self.uri(), "version": self.version},
                         self._limit(timeout))
        self.stats["syncs"] += 1
        self.stats["sync_ms"] += int((time.monotonic() - t0) * 1000)
        return list(self.diags)

    def goals(self, line, character, timeout=GOAL_SECONDS):
        """The goals at a position of the current document (each a rendered hypotheses-and-goal
        block), or None when the position is not inside a tactic proof."""
        self.stats["goal_requests"] += 1
        r = self.request("$/lean/plainGoal", {"textDocument": {"uri": self.uri()},
                                              "position": {"line": line, "character": character}},
                         self._limit(timeout))
        return None if r is None else list(r.get("goals") or [])

    def term_goal(self, line, character, timeout=GOAL_SECONDS):
        r = self.request("$/lean/plainTermGoal", {"textDocument": {"uri": self.uri()},
                                                  "position": {"line": line, "character": character}},
                         self._limit(timeout))
        return None if r is None else r.get("goal")


# Session integration (agents/repair.py)

def enabled(s):
    return bool(getattr(s, "goal_tool", False))


def server(s):
    """The session's server, created on first use (started on its first elaboration)."""
    srv = s.__dict__.get("lean_server")
    if srv is None:
        srv = s.lean_server = LeanServer(s.ws, s.task.lib)
    return srv


def close(s):
    srv = s.__dict__.get("lean_server")
    if srv is not None:
        srv.close()


def summary(s, a=None):
    """The `goal_tool` record of summary.json."""
    on = enabled(s) if a is None else getattr(a, "goal_tool", "on") != "off"
    srv = s.__dict__.get("lean_server")
    rec = {"enabled": on}
    if srv is not None:
        rec.update(srv.stats)
    rec.update(s.__dict__.get("goal_stats", {}))
    return rec


def _count(s, key, n=1):
    st = s.__dict__.setdefault("goal_stats", {})
    st[key] = st.get(key, 0) + n


def _render(goals, limit=GOAL_CHARS):
    if goals is None:
        return "(not inside a tactic proof)"
    if not goals:
        return "no goals (this branch is closed here)"
    out = []
    for i, g in enumerate(goals):
        g = g if len(g) <= limit else g[:limit] + "\n... [state truncated]"
        out.append((f"goal {i + 1} of {len(goals)}:\n" if len(goals) > 1 else "") + g)
    return "\n".join(out)


def _messages(diags, text, first_line, label, last_line=None):
    """Diagnostics located in lines [first_line, last_line] of the document, as compiler-style
    lines `label:L:C: error: ...` with L counted from 1 at first_line. Returns (lines, errors,
    blocking warnings, linter warnings)."""
    lines = text.split("\n")
    out, errors, warnings, linters = [], 0, 0, 0
    for d in sorted(diags, key=lambda d: (d["range"]["start"]["line"], d["range"]["start"]["character"])):
        ln = d["range"]["start"]["line"]
        if ln < first_line or (last_line is not None and ln > last_line):
            continue
        sev = {1: "error", 2: "warning"}.get(d.get("severity"))
        if sev is None:
            continue
        msg = d.get("message", "")
        col = codepoint_col(lines[ln] if ln < len(lines) else "", d["range"]["start"]["character"])
        out.append(f"{label}:{ln - first_line + 1}:{col}: {sev}: {msg}")
        if sev == "error":
            errors += 1
        elif re.search(r"\blinter\.\w+", msg):
            linters += 1
        else:
            warnings += 1
    return out, errors, warnings, linters


def fast_snippet(s, scratch, offset, code):
    """try_snippet's single-step check on the server. `scratch` is the document Session._scratch
    builds, `offset` the number of lines before the snippet. Returns (False, messages, ms) for a
    snippet with an error or a non-linter warning (`sorry`), with the proof state at each `sorry`
    of the snippet; ("clean", ms) when the server finds it clean (the caller then compiles it, as
    the compile decides what is banked); None when the server is unavailable."""
    if not enabled(s):
        return None
    srv = server(s)
    t0 = time.monotonic()
    try:
        diags = srv.sync(scratch)
    except ServerTimeout:
        ms = int((time.monotonic() - t0) * 1000)
        _count(s, "fast_timeouts")
        return False, [judge.TIMEOUT_MARK], ms
    except ServerError as e:
        _count(s, "fast_unavailable")
        s.log(kind="lean_server", event="unavailable", error=str(e)[:300])
        return None
    msgs, errors, warnings, linters = _messages(diags, scratch, offset, "snippet")
    ms = int((time.monotonic() - t0) * 1000)
    blocking = errors or warnings or (linters and not getattr(s, "topdown", False))
    if not blocking:
        _count(s, "fast_clean")
        return "clean", ms
    _count(s, "fast_rejected")
    states = sorry_states(srv, scratch, offset, code, "snippet line")
    if states:
        msgs.append("Proof state at each `sorry` of the snippet:\n" + states)
    return False, msgs, ms


def sorry_states(srv, text, first_line, part, where, limit=6):
    """The goals at each `sorry` of `part`, which starts at line `first_line` of the document."""
    out = []
    plines = part.split("\n")
    for k, l in enumerate(plines):
        for m in re.finditer(r"(?<![\w.'])sorry(?![\w'])", re.sub(r"--.*$", "", l)):
            if len(out) >= limit:
                break
            try:
                g = srv.goals(first_line + k, utf16_col(l[:m.start()]))
            except ServerError:
                return "\n\n".join(out)
            out.append(f"{where} {k + 1}: {l.strip()[:120]}\n{_render(g)}")
    return "\n\n".join(out)


def goal_at(s, name, line=None):
    """The `goal_at` tool: the proof state in declaration `name` of candidate/Solution.lean, at
    every `sorry` of it (or, with none, at every error in it), or before and after line `line` of
    the declaration (counted from 1 at its first line). Errors Lean reports in the declaration
    are listed too."""
    import repair
    if not enabled(s):
        return "error: goal_at is not available in this run"
    short = (name or "").split(".")[-1].strip()
    src = s._source()
    text = repair.decl_text(s, short, src)
    if not text:
        return f"error: no declaration `{name}` in candidate/Solution.lean"
    text = text.rstrip()
    start = src.find(text)
    first = src.count("\n", 0, start)
    dlines = text.split("\n")
    t0 = time.monotonic()
    srv = server(s)
    try:
        diags = srv.sync(src)
    except ServerError as e:
        s.log(kind="goal_at", name=short, line=line, ok=False, error=str(e)[:300])
        return f"error: Lean did not finish elaborating the file ({e}); use try_snippet instead"
    msgs, errors, _, _ = _messages(diags, src, first, short, first + len(dlines) - 1)
    parts = []
    try:
        if line not in (None, ""):
            k = max(1, min(len(dlines), int(line))) - 1
            l = dlines[k]
            ind = len(l) - len(l.lstrip())
            before = srv.goals(first + k, utf16_col(l[:ind]))
            after = srv.goals(first + k, utf16_col(l.rstrip()))
            parts.append(f"line {k + 1} of `{short}`: {l.strip()[:160]}\nbefore this line:\n{_render(before)}\n"
                         f"after this line:\n{_render(after)}")
        else:
            states = sorry_states(srv, src, first, text, f"`{short}` line")
            if states:
                parts.append(states)
            else:
                for d in [d for d in diags if d.get("severity") == 1
                          and first <= d["range"]["start"]["line"] < first + len(dlines)][:4]:
                    p = d["range"]["start"]
                    g = srv.goals(p["line"], p["character"])
                    parts.append(f"at the error on line {p['line'] - first + 1} of `{short}`:\n{_render(g)}")
            if not parts:
                parts.append(f"`{short}` has no `sorry` and no error; give `line` to see the state at a line of it.")
    except (ServerError, ValueError) as e:
        parts.append(f"(proof state not available: {e})")
    out = "\n\n".join(parts)
    if msgs:
        out += "\n\nLean messages in this declaration:\n" + "\n".join(m[:800] for m in msgs[:8])
    ms = int((time.monotonic() - t0) * 1000)
    _count(s, "goal_at_calls")
    _count(s, "goal_at_ms", ms)
    s.log(kind="goal_at", name=short, line=line, ok=True, ms=ms, errors=errors, chars=len(out))
    return out[:RESULT_CHARS]


GOAL_TOOL = {"type": "function", "function": {
    "name": "goal_at",
    "description": "Show the exact proof state (hypotheses and goals) inside one declaration of candidate/Solution.lean, "
                   "without compiling the whole file: at every `sorry` of it (or, if it has none, at every error), or "
                   "before and after one line of it. A declaration with `have h : P := by sorry` steps shows each "
                   "remaining goal. try_snippet also returns the state at each `sorry` of a snippet.",
    "parameters": {"type": "object", "properties": {
        "name": {"type": "string", "description": "the declaration"},
        "line": {"type": "integer", "minimum": 1, "description": "a line of the declaration, counted from 1 at its "
                                                                "first line (optional)"}},
        "required": ["name"]}}}
