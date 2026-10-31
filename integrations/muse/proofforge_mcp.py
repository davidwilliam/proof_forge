#!/usr/bin/env python3
"""ProofForge MCP server (stdio, JSON-RPC 2.0, one JSON message per line; stdlib only).

Muse Code starts it from `mcp_servers` with the transport `stdio`. Two profiles:

  --profile lean        `lean_build` only: Lean 4.35 in the pinned judge image on the workspace
                        (the Lean project the agent edits), returning Lean's own output. This is
                        the whole toolset of the Muse-Code-alone arm, whose shell sandbox cannot
                        reach Docker.
  --profile proofforge  `lean_build` plus the ProofForge tools:
      list_tasks        the benchmark and real-world tasks
      show_task         a task's issue report, README, definitions under repair, the locked
                        requirements (id, theorem, statement, plain-language text) and the rules
      try_snippet       compile Lean code appended to the candidate (inside its namespace)
                        without changing the file; errors and unsolved goals in the snippet
      check_candidate   the official pipeline (`bin/proofforge check`): per-requirement
                        VERIFIED / REFUTED / UNRESOLVED, witnesses, kernel-checked
                        counterexamples, proof-check reasons, the Lean errors and sorry status
                        of the candidate, and the Passport (written under .proofforge/)
      verify_passport   `bin/proofforge verify` of a Passport against a candidate
      search_library    retrieval over the ProofForgeFin declaration index

`--blind` (measured runs) leaves the task README out of `show_task`: the READMEs of the
real-world tasks describe the known fixes and earlier repairs.

The workspace (`--workspace`, default the current directory) is the agent's copy of the task's
Lean project; candidate paths are resolved inside it and may not leave it. The task comes from
`--task` or the workspace's `.proofforge/task.json`. The checks read the harness and the locked
task files from this repository checkout; nothing the agent writes reaches them except the
candidate file, which the judge copies into a fresh project of locked files.

`--log FILE` appends one JSON line per tool call (name, arguments abridged, duration, result
abridged) for the run record.
"""
import argparse, json, os, pathlib, re, shutil, signal, subprocess, sys, time, traceback

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "harness"))
import fin_lib, judge, task as taskmod  # noqa: E402

PROTOCOL_VERSIONS = ["2025-06-18", "2025-03-26", "2024-11-05"]
SERVER_INFO = {"name": "proofforge", "version": "1.0.0"}
OUT_LIMIT = 12000


def clean_lean(text):
    """Lean output without Lake's progress and trace lines."""
    keep = [l for l in text.splitlines()
            if not l.startswith("trace:") and not re.match(r"^[✔✖⚠] \[\d+/\d+\]", l)
            and "linter" not in l and "Hint:" not in l and "deprecated" not in l]
    return "\n".join(keep)


def tail(text, n=OUT_LIMIT):
    return text if len(text) <= n else "[... earlier output omitted ...]\n" + text[-n:]


def kill_containers(pid):
    """Stop the judge containers a process started (judge.in_container names them pf-<pid>-...)."""
    if judge.IN_IMAGE:
        return
    r = subprocess.run(["docker", "ps", "-q", "--filter", f"name=^pf-{pid}-"], capture_output=True, text=True)
    ids = r.stdout.split()
    if ids:
        subprocess.run(["docker", "kill"] + ids, capture_output=True)


def scrub(text):
    """Tool output without this machine's paths: the repository and the home directory."""
    return text.replace(str(ROOT), "<proofforge>").replace(str(pathlib.Path.home()), "~")


def all_tasks():
    out = taskmod.all_tasks()
    out += [taskmod.Task(d) for d in sorted(taskmod.REALWORLD.glob("*")) if (d / "task.json").exists()]
    return [t for t in out if "hidden" not in t.split]


def requirement_rows(t):
    import passport
    rows = []
    for rid, th in t.requirements:
        stmt = passport.statement(t, th)
        rows.append({"id": rid, "theorem": f"{t.ns}.{th}", "statement": stmt, "text": passport.docstring(t, stmt)})
    return rows


class Server:
    def __init__(self, workspace, task_id=None, profile="proofforge", log=None, lean_timeout=900, blind=False):
        self.ws = pathlib.Path(workspace).resolve()
        self.profile = profile
        self.blind = blind
        self.log_path = pathlib.Path(log) if log else None
        self.lean_timeout = lean_timeout
        meta = self.ws / ".proofforge" / "task.json"
        if not task_id and meta.is_file():
            task_id = json.loads(meta.read_text()).get("task")
        self.task_id = task_id
        self.checks = 0
        self._index = None
        self.children = {}

    def run_cli(self, args, timeout=3600):
        """`bin/proofforge ...` as a child process that cleanup() can stop."""
        p = subprocess.Popen([sys.executable, str(ROOT / "bin/proofforge")] + args, cwd=str(ROOT), text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
        self.children[p.pid] = p
        try:
            out, _ = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            self.stop_process(p)
            out = "the check was stopped at its time limit"
        finally:
            self.children.pop(p.pid, None)
        return p.returncode, out

    @staticmethod
    def stop_process(p):
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        kill_containers(p.pid)

    def cleanup(self):
        """Stop running checks and every Lean container this server or its checks started."""
        for p in list(self.children.values()):
            self.stop_process(p)
        kill_containers(os.getpid())

    # -- helpers -------------------------------------------------------------------------------
    def task(self, task_id=None):
        tid = task_id or self.task_id
        if not tid:
            raise ValueError("no task given and the workspace names none")
        if "/" in tid or tid.startswith("."):
            raise ValueError(f"unknown task {tid!r}")
        t = taskmod.load(tid)
        if "hidden" in t.split:
            raise ValueError(f"unknown task {tid!r}")
        return t

    def path(self, rel, default="candidate/Solution.lean"):
        p = (self.ws / (rel or default)).resolve()
        if p != self.ws and self.ws not in p.parents:
            raise ValueError(f"{rel!r} is outside the workspace")
        return p

    def lean(self, script, timeout=None):
        """`script` in the pinned image on the workspace; with pipefail, so Lean's exit code survives `| tail`."""
        return judge.in_container(self.ws, "set -o pipefail; " + script, timeout=timeout or self.lean_timeout)

    # -- tools ---------------------------------------------------------------------------------
    def lean_build(self, file=None):
        """Lean's own output for the candidate module, or for one .lean file of the workspace."""
        if file:
            p = self.path(file)
            if p.suffix != ".lean" or not p.is_file():
                raise ValueError(f"{file!r} is not a .lean file in the workspace")
            rel = p.relative_to(self.ws)
            lib = self.task().lib if self.task_id else None
            pre = f"lake build {lib} >/dev/null 2>&1; " if lib else ""
            r = self.lean(f"{pre}lake env lean {rel} 2>&1 | tail -c 60000")
            what = f"lake env lean {rel}"
        else:
            r = self.lean("lake build Solution 2>&1 | tail -c 60000")
            what = "lake build Solution"
        out = clean_lean(r["output_tail"])
        return f"$ {what}\nexit code {r['exit_code']} ({r['elapsed_ms']} ms)\n" + (tail(out) or "(no output)")

    def list_tasks(self, split=None):
        rows = []
        for t in all_tasks():
            if split and t.split != split:
                continue
            rows.append(f"{t.id:<28} {t.family:<14} {t.split:<9} {len(t.requirements)} requirements")
        return "\n".join(rows) or "no tasks"

    def show_task(self, task=None):
        t = self.task(task)
        readme = t.root / "README.md"
        lp = t.root / t.spec_dir / "Lemmas.lean"
        doc = {
            "id": t.id, "family": t.family, "split": t.split,
            "issue_report": t.issue,
            "definitions_under_repair": [f"{t.ns}.{d}" for d in t.definitions],
            "namespace": t.ns,
            "candidate": "candidate/Solution.lean",
            "locked_files": [p for p in t.readable if p != "candidate/Solution.lean"],
            "requirements": requirement_rows(t),
            "rules": {
                "edit_only": "candidate/Solution.lean (and optionally candidate/Lib/**); spec/, app/ and the Lake files are locked and checked byte for byte",
                "allowed_imports": [f"{t.lib}.Spec"] + ([f"{t.lib}.Lemmas"] if lp.exists() else []) + ["Init.*", "Std.*", "ProofForgeFin.*"],
                "forbidden": "sorry, axiom, opaque, implemented_by, extern, unsafe, @[export], macro, elab, syntax, "
                             "initialize, #eval, run_cmd, native_decide, set_option, @[csimp], simprocs and other "
                             "elaboration-time code",
                "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
                "statements": "every required theorem must have exactly the locked statement in Challenge.lean",
            },
        }
        if self.profile == "proofforge":
            doc["library"] = ("ProofForgeFin is vendored in this workspace: `import ProofForgeFin` or one module; "
                              "search_library finds its theorems and tactics.") if (self.ws / fin_lib.VENDOR).exists() else None
        text = json.dumps(doc, indent=2, ensure_ascii=False)
        if readme.is_file() and not self.blind:
            text += "\n\n=== README.md ===\n" + tail(readme.read_text(), 16000)
        return text

    def try_snippet(self, code, candidate=None):
        """Compile `code` appended inside the namespace after the candidate; the file is unchanged."""
        t = self.task()
        src = self.path(candidate).read_text()
        end = f"end {t.ns}"
        decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                          r"(?:theorem|lemma|def|instance|abbrev)\s+([^\s:({\[]+)", re.M)
        # A declaration the snippet redefines is dropped from the context, so it can be re-proved.
        for m in decl.finditer(code):
            name = re.escape(m.group(1).split(".")[-1])
            src = re.sub(rf"(?ms)^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma|def|instance|abbrev)\s+{name}\b.*?(?=^(?:@\[|/--|private |protected |theorem |lemma |def |instance |abbrev |{re.escape(end)})|\Z)", "", src)
        body = src.rsplit(end, 1)[0] if end in src else src
        offset = body.count("\n") + 1
        d = self.ws / ".proofforge"
        d.mkdir(exist_ok=True)
        (d / "Snippet.lean").write_text(body + "\n" + code + f"\n\n{end}\n")
        r = self.lean(f"lake build {t.lib} >/dev/null 2>&1; lake env lean .proofforge/Snippet.lean 2>&1 | tail -c 20000", timeout=600)
        msgs, cur = [], None
        for l in clean_lean(r["output_tail"]).splitlines():
            m = re.match(r"^\.proofforge/Snippet\.lean:(\d+):(\d+): (error|warning)", l)
            if m:
                ln = int(m.group(1)) - offset
                cur = ln >= 0
                if cur:
                    l = re.sub(r"^\.proofforge/Snippet\.lean:\d+", f"snippet:{ln}", l)
                elif m.group(3) == "error" and not msgs:
                    msgs.append("(the candidate file itself has errors; the snippet was compiled after them)")
            if cur:
                msgs.append(l)
        if r["exit_code"] == 124:
            return "the snippet was stopped at the time limit"
        if not any(re.search(r": (error|warning)", x) for x in msgs):
            return "snippet compiles with no errors or warnings (the candidate file is unchanged)"
        return tail("\n".join(msgs), 8000)

    def theorem_status(self, t):
        """Per required theorem: PROVED, SORRY or MISSING (`#print axioms` on the built candidate)."""
        d = self.ws / ".proofforge"
        d.mkdir(exist_ok=True)
        (d / "Status.lean").write_text("import Solution\n" + "".join(f"#print axioms {t.ns}.{th}\n" for th in t.theorems))
        r = self.lean("lake env lean .proofforge/Status.lean 2>&1", timeout=300)
        blocks = re.split(rf"(?='{re.escape(t.ns)}\.)", r["output_tail"])
        out = {}
        for th in t.theorems:
            blk = next((b for b in blocks if b.startswith(f"'{t.ns}.{th}'")), "")
            out[th] = "MISSING" if not blk else "SORRY" if "sorryAx" in blk else "PROVED"
        return out

    def check_candidate(self, candidate=None, counterexample=True, cases=2000):
        """The official check: `bin/proofforge check` from the repository, plus the candidate's
        Lean errors and sorry status from the workspace build when the proof check rejects."""
        t = self.task()
        cand = self.path(candidate)
        if not cand.is_file():
            raise ValueError(f"no candidate file {candidate!r}")
        self.checks += 1
        d = self.ws / ".proofforge"
        d.mkdir(exist_ok=True)
        out = d / f"passport-{self.checks:03d}.json"
        snap = d / f"checked-{self.checks:03d}.lean"
        shutil.copy(cand, snap)
        args = ["check", "--task", t.id, "--candidate", str(snap), "--out", str(out),
                "--cases", str(int(cases))] + ([] if counterexample else ["--no-counterexample"])
        t0 = time.monotonic()
        _, text = self.run_cli(args)
        if not out.is_file():
            return "the check did not complete:\n" + tail(text, 4000)
        p = json.loads(out.read_text())
        res = {"status": p["status"], "passport": str(out.relative_to(self.ws)),
               "passport_sha256": p["passport_sha256"], "checked_file": str(snap.relative_to(self.ws)),
               "seconds": round(time.monotonic() - t0, 1),
               "proof_check": p["proof_check"],
               "executable": {"status": p["executable"]["status"],
                              "cases": p["checks"]["property_tests"]["cases"],
                              "violations": p["checks"]["property_tests"]["violations"]},
               "kernels": p["checks"]["comparator_kernels"],
               "requirements": [{"id": q["id"], "theorem": q["theorem"], "status": q["status"],
                                 "axioms": q.get("axioms_used"),
                                 **({"witness": q["witness"]} if q.get("witness") else {})}
                                for q in p["requirements"]]}
        if p.get("counterexamples"):
            res["counterexamples"] = [{k: c.get(k) for k in ("requirement", "theorem", "statement", "kernel_checked",
                                                               "kernels", "axioms", "reason", "lean_source")}
                                      for c in p["counterexamples"]]
        if p.get("library", {}).get("vendored"):
            res["library"] = {k: p["library"].get(k) for k in ("source_tree_sha256", "imported", "modules")}
        if not p["proof_check"]["accepted"]:
            b = self.lean("lake build Solution 2>&1 | tail -c 60000")
            text = clean_lean(b["output_tail"])
            if "error:" in text:
                res["lean_errors"] = tail(text, 8000)
            else:
                res["theorem_status"] = self.theorem_status(t)
        return json.dumps(res, indent=2, ensure_ascii=False)

    def verify_passport(self, passport, candidate=None):
        pp, cand = self.path(passport), self.path(candidate)
        code, text = self.run_cli(["verify", str(pp), "--candidate", str(cand)])
        return f"exit code {code}\n" + tail(text, 8000)

    def search_library(self, query, limit=10):
        if self._index is None:
            self._index = fin_lib.Index.load()
        limit = max(1, min(25, int(limit or 10)))
        hits = self._index.search(query or "", limit=limit)
        return fin_lib.render(hits) if hits else "no library declaration matches; try other words or a declaration name"

    # -- MCP -----------------------------------------------------------------------------------
    def tools(self):
        cand = {"type": "string", "description": "candidate file, relative to the workspace (default candidate/Solution.lean)"}
        lean = [{"name": "lean_build",
                 "description": "Run Lean 4.35 (the pinned toolchain, in its container) on this workspace and return Lean's output. "
                                "Without `file`: `lake build Solution` (the candidate module candidate/Solution.lean). With `file`: "
                                "`lake env lean <file>` for any .lean file in the workspace, for example a scratch file that imports "
                                "Solution and runs `#print axioms`.",
                 "inputSchema": {"type": "object", "properties": {"file": {"type": "string"}}}}]
        if self.profile == "lean":
            return lean
        return lean + [
            {"name": "list_tasks", "description": "List ProofForge tasks: id, family, split, number of locked requirements.",
             "inputSchema": {"type": "object", "properties": {"split": {"type": "string", "description": "dev, val, test or realworld"}}}},
            {"name": "show_task", "description": "A task's issue report, README, definitions under repair, locked requirements "
                                                 "(id, theorem, exact statement, plain-language text) and the judge's rules. "
                                                 "Default: this workspace's task.",
             "inputSchema": {"type": "object", "properties": {"task": {"type": "string"}}}},
            {"name": "try_snippet", "description": "Compile Lean code appended inside the task namespace after the current candidate, "
                                                   "without changing the file. Returns the errors, warnings and unsolved goals located "
                                                   "in the snippet (lines numbered from the snippet's start). A declaration the snippet "
                                                   "redefines replaces the file's version for this compile.",
             "inputSchema": {"type": "object", "properties": {"code": {"type": "string"}, "candidate": cand}, "required": ["code"]}},
            {"name": "check_candidate", "description": "Run the official ProofForge check (bin/proofforge check) on the candidate: tree "
                                                       "check, implementation scan, Comparator with six kernels, leanchecker, axiom audit, "
                                                       "and property tests of the executable built from the same source. Returns each "
                                                       "requirement as VERIFIED, REFUTED (with the concrete input that violates it, and a "
                                                       "counterexample checked by the kernel) or UNRESOLVED, the proof-check reasons, the "
                                                       "candidate's Lean errors or sorry status, and the Passport file and hash. Takes minutes.",
             "inputSchema": {"type": "object", "properties": {"candidate": cand,
                                                              "counterexample": {"type": "boolean", "description": "kernel-check a refutation of each refuted requirement (default true)"},
                                                              "cases": {"type": "integer", "minimum": 100, "maximum": 2000, "description": "property cases (default 2000, the Passport setting)"}}}},
            {"name": "verify_passport", "description": "Reproduce a Passport (bin/proofforge verify): re-run the pipeline on the candidate "
                                                       "and compare every recorded hash and status.",
             "inputSchema": {"type": "object", "properties": {"passport": {"type": "string"}, "candidate": cand}, "required": ["passport"]}},
            {"name": "search_library", "description": "Search the ProofForgeFin library (theorems, definitions, tactics, simp sets, modules "
                                                      "about rounding, fixed point, shares, ledgers, sequences of operations) by keywords, "
                                                      "names or a statement. Returns signature, module to import and doc string.",
             "inputSchema": {"type": "object", "properties": {"query": {"type": "string"},
                                                              "limit": {"type": "integer", "minimum": 1, "maximum": 25}}, "required": ["query"]}},
        ]

    def call(self, name, args):
        allowed = {t["name"] for t in self.tools()}
        if name not in allowed:
            raise ValueError(f"unknown tool {name!r}")
        fn = getattr(self, name)
        return fn(**{k: v for k, v in (args or {}).items() if v is not None})

    def handle(self, msg):
        """One JSON-RPC message; returns the response object, or None for a notification."""
        mid, method, params = msg.get("id"), msg.get("method"), msg.get("params") or {}
        if mid is None:
            return None
        try:
            if method == "initialize":
                want = params.get("protocolVersion")
                result = {"protocolVersion": want if want in PROTOCOL_VERSIONS else PROTOCOL_VERSIONS[0],
                          "capabilities": {"tools": {"listChanged": False}}, "serverInfo": SERVER_INFO,
                          "instructions": "ProofForge: locked Lean specifications, the official judge and Passports."}
            elif method == "ping":
                result = {}
            elif method == "tools/list":
                result = {"tools": self.tools()}
            elif method == "tools/call":
                name, args = params.get("name"), params.get("arguments") or {}
                t0 = time.monotonic()
                try:
                    text, err = self.call(name, args), False
                except Exception as e:   # a tool error goes back to the model, not to the protocol
                    text, err = f"error: {e}", True
                    if not isinstance(e, (ValueError, TypeError)):
                        text += "\n" + traceback.format_exc(limit=2)
                text = scrub(text)
                self.record(name, args, text, err, time.monotonic() - t0)
                result = {"content": [{"type": "text", "text": text}], "isError": err}
            else:
                return {"jsonrpc": "2.0", "id": mid, "error": {"code": -32601, "message": f"method not found: {method}"}}
            return {"jsonrpc": "2.0", "id": mid, "result": result}
        except Exception as e:
            return {"jsonrpc": "2.0", "id": mid, "error": {"code": -32603, "message": str(e)}}

    def record(self, name, args, text, err, seconds):
        if not self.log_path:
            return
        rec = {"t": round(time.time(), 3), "tool": name, "seconds": round(seconds, 1), "error": err,
               "args": {k: (v if len(str(v)) <= 2000 else str(v)[:2000] + " [truncated]") for k, v in (args or {}).items()},
               "result": text[:4000]}
        with self.log_path.open("a") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")


def serve(server, inp=sys.stdin, out=sys.stdout):
    for line in inp:
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except ValueError:
            resp = {"jsonrpc": "2.0", "id": None, "error": {"code": -32700, "message": "parse error"}}
        else:
            batch = msg if isinstance(msg, list) else [msg]
            resps = [r for r in (server.handle(m) for m in batch if isinstance(m, dict)) if r is not None]
            resp = resps if isinstance(msg, list) else (resps[0] if resps else None)
        if resp:
            out.write(json.dumps(resp, ensure_ascii=False) + "\n")
            out.flush()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--workspace", default=".")
    ap.add_argument("--task")
    ap.add_argument("--profile", choices=["lean", "proofforge"], default="proofforge")
    ap.add_argument("--log")
    ap.add_argument("--blind", action="store_true",
                    help="measured runs: show_task omits the task README, which describes the known fixes")
    a = ap.parse_args(argv)
    server = Server(a.workspace, a.task, a.profile, a.log, blind=a.blind)

    def stop(signum, frame):
        server.cleanup()
        sys.exit(128 + signum)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGHUP, stop)
    try:
        serve(server)
    finally:
        server.cleanup()


if __name__ == "__main__":
    main()
