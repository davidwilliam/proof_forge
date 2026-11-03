"""Tactic portfolio: a fixed list of Lean tactics tried on open goals before the model spends a
turn on them.

An open goal is a theorem of the candidate whose proof is `sorry`: a required theorem, a skeleton
helper, a planner lemma or a goal left open by a resumed attempt. For a batch of goals, one Lean
file is compiled: the current candidate with the goals removed (so that no tactic can use a goal
to prove itself), then, for every goal and every tactic of the portfolio, a copy of the goal's
statement under a fresh name proved by that tactic, each under its own heartbeat limit, then
`#print axioms` of every copy. A copy closes its goal when Lean reports no error for it and its
axioms do not include `sorryAx` (so it uses no open declaration either). The first tactic in
portfolio order that closes a goal is banked through Session.bank, the banking path of
try_snippet: the goal's own statement with the tactic as its proof, kept only if the whole
candidate still compiles. Besides fixed tactics (grind, omega, simp_all, decide, simp_all then
omega, the library's generalize_divs then omega and machine_norm then grind where the candidate
imports them, exact?, try?), two entries unfold the definitions the goal's own statement names
(found in the locked spec files and the candidate, never chosen per task) before grind. `exact?` and `try?` are banked as the proof they report (their
"Try this" suggestion), never as the search itself.

No model is called and no dollars are spent. Every Lean run goes through judge.in_container, so
it stops at the run's deadline and its time counts against the wall cap like any other Lean run.
The per-tactic limit is Lean's heartbeat counter (`maxHeartbeats`, deterministic); the batch as a
whole is also stopped after a wall allowance of `seconds` per attempt. `exact?` and `try?` do not
stop at the heartbeat limit (measured: one ran 516 s), so a stopped batch is compiled once more
without them.
"""
import hashlib, json, re, time

import judge, fin_lib  # noqa: E402  (agents/repair.py puts harness/ on sys.path)
from ledger import declarations, has_sorry, split_proof  # noqa: E402

# (key, tactic text, library tactic it needs or None), in the order a closing tactic is chosen.
# `{unfold}` and `{defs}` stand for the definitions the goal's own statement names (goal_of): an
# entry with one of them is tried only on a goal whose statement names such a definition. A tactic
# of several lines is written without indentation; proof_body() indents every line of it, in the
# batch file and in the text banked, so that the proof banked is the proof Lean checked.
PORTFOLIO = [
    ("grind", "grind", None),
    ("omega", "omega", None),
    ("simp_all", "simp_all", None),
    ("decide", "decide", None),
    ("simp_all_omega", "simp_all <;> omega", None),
    ("generalize_divs_omega", "generalize_divs <;> omega", "generalize_divs"),
    ("machine_norm_grind", "machine_norm <;> grind", "machine_norm"),
    ("unfold_grind", "unfold {unfold} at *\nintros\ngrind", None),
    ("grind_defs", "intros\ngrind [{defs}]", None),
    ("exact?", "exact?", None),
    ("try?", "try?", None),
]
SEARCH = {"exact?", "try?"}          # tactics banked as the proof they suggest
PREFIX = "pfport_"                   # names of the copies in the batch file (never banked)
HEARTBEATS = 50000                   # per-tactic limit, in Lean's `maxHeartbeats` units (default 200000)
SECONDS = 5                          # per-attempt wall allowance of a batch
BASE_SECONDS = 60                    # elaborating the candidate before the attempts
MAX_BATCH_SECONDS = 600
PROFILE_MS = 10                      # attempts faster than this report no time


HEAD = re.compile(r"^((?:open\s[^\n]*?\bin\s+)?)(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*"
                  r"(?:theorem|lemma)\s+([^\s:({\[]+)(.*)$", re.S)


DEF = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:private|protected|noncomputable)\s+)*)(def|abbrev)\s+([^\s:({\[]+)", re.M)


def definitions(s, src):
    """{name: reducible} for the definitions of the locked spec files and of the candidate."""
    texts = [src] + [p.read_text() for p in sorted((s.task.root / s.task.spec_dir).glob("*.lean"))
                     if p.name != "Challenge.lean"]
    out = {}
    for text in texts:
        for m in DEF.finditer(text):
            out.setdefault(m.group(3).split(".")[-1], m.group(2) == "abbrev")
    return out


def goal_of(s, name, src=None):
    """The open goal `name` of the candidate: its statement (as written, attributes included), the
    pieces a renamed copy is built from, and the definitions its statement names (`unfold`: all of
    them, `defs`: the ones that are not reducible), or None when `name` is not a theorem proved by
    `sorry`."""
    import repair
    src = s._source() if src is None else src
    text = repair.decl_text(s, name, src)
    if not text or not re.search(r"\bsorry\b", text):
        return None
    head, _ = split_proof(text.rstrip())
    m = HEAD.match(head or "")
    if not m:
        return None
    defs = definitions(s, src)
    named = sorted({t for t in re.findall(r"[A-Za-z_][\w'.]*", m.group(3)) if t.split(".")[-1] in defs})
    return {"name": name, "head": head, "open_in": m.group(1), "rest": m.group(3),
            "unfold": named, "defs": [d for d in named if not defs[d.split(".")[-1]]]}


def tactic_for(tac, goal):
    """The tactic text of a portfolio entry for one goal, or None when the entry needs definitions
    the goal's statement does not name."""
    for key in ("unfold", "defs"):
        if "{" + key + "}" in tac:
            names = goal.get(key) or []
            if not names:
                return None
            tac = tac.replace("{" + key + "}", (" " if key == "unfold" else ", ").join(names))
    return tac


def proof_body(tac):
    """The lines of a tactic proof after `:= by`: every line of `tac` indented by two spaces (blank
    lines kept empty). The batch file and the banked text use it alike."""
    return "\n".join("  " + l if l.strip() else l for l in tac.split("\n"))


def available(s, src):
    """Portfolio entries usable on the current candidate: the library tactics only when a module
    the candidate imports (transitively) defines them."""
    mods = set()
    if s.library and s.lib_index:
        imported = [m for m in fin_lib.imports_of(src) if fin_lib.IMPORT_RE.match(m)]
        mods = set(fin_lib.closure(imported)) if imported else set()
    tactic_mod = {e["name"]: e["module"] for e in (s.lib_index.entries if s.lib_index else []) if e["kind"] == "tactic"}
    return [p for p in PORTFOLIO if p[2] is None or tactic_mod.get(p[2]) in mods]


def suggestions(text):
    """The proofs a `Try this` / `Try these` message offers, in order."""
    m = re.search(r"Try (?:this|these):?\s*(.*)$", text, re.S)
    if not m:
        return []
    body = m.group(1)
    parts = re.split(r"(?m)^\s*\[apply\]\s*", body)
    out = []
    for p in parts:
        p = p.rstrip()
        if not p.strip():
            continue
        lines = p.split("\n")
        indent = min((len(l) - len(l.lstrip()) for l in lines[1:] if l.strip()), default=0)
        out.append("\n".join([lines[0].strip()] + [l[indent:] for l in lines[1:]]))
    return out


def batch_text(s, goals, entries, heartbeats, src=None):
    """The batch file and its attempts: the candidate without the goals, then one renamed copy of
    each goal per portfolio entry (the searching tactics first, so that no copy they could find
    exists yet), then `#print axioms` of every copy."""
    src = s._source() if src is None else src
    for g in goals:
        src, _ = s._replace_in(src, g["name"], "")
    body = src.rsplit(s.end, 1)[0] if s.end in src else src
    lines = body.rstrip("\n").split("\n") + ["", "set_option trace.profiler true",
                                             f"set_option trace.profiler.threshold {PROFILE_MS}", ""]
    attempts = []
    order = [e for e in entries if e[0] in SEARCH] + [e for e in entries if e[0] not in SEARCH]
    for key, tac0, _ in order:
        for gi, g in enumerate(goals):
            tac = tactic_for(tac0, g)
            if tac is None:
                continue
            name = f"{PREFIX}{gi}_{[e[0] for e in entries].index(key)}"
            chunk = "\n".join([f"set_option maxHeartbeats {int(heartbeats)} in",
                               f"{g['open_in']}theorem {name}{g['rest']} := by", proof_body(tac), ""]).split("\n")
            start = len(lines) + 1
            lines += chunk
            attempts.append({"goal": g["name"], "key": key, "tactic": tac, "copy": name,
                             "lines": (start, start + len(chunk) - 1)})
    lines += [f"#print axioms {a['copy']}" for a in attempts] + ["", s.end, ""]
    return "\n".join(lines), attempts


def parse(output, attempts, ns):
    """Per attempt: ok, elapsed ms (None below the profiler threshold), whether it stopped at its
    heartbeat limit, its first error and its suggestions."""
    res = {a["copy"]: {"errors": [], "sorry": False, "axioms": None, "ms": None, "limit": False, "suggest": []}
           for a in attempts}
    by_line = [(a["lines"], a["copy"]) for a in attempts]
    for raw in output.splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            m = json.loads(raw)
        except ValueError:
            continue
        data, sev = m.get("data") or "", m.get("severity")
        line = (m.get("pos") or {}).get("line", 0)
        ax = re.match(rf"'(?:{re.escape(ns)}\.)?({PREFIX}\d+_\d+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                      data)
        if ax and ax.group(1) in res:
            res[ax.group(1)]["axioms"] = sorted(x.strip() for x in (ax.group(3) or "").replace("\n", " ").split(",") if x.strip())
            continue
        tr = re.match(rf"\[Elab\.(?:async|command)\] \[([\d.]+)\][^\n]*?({PREFIX}\d+_\d+)", data)
        if tr and tr.group(2) in res and sev == "information":
            r = res[tr.group(2)]
            r["ms"] = max(r["ms"] or 0, int(float(tr.group(1)) * 1000))
            continue
        copy = next((c for (a, b), c in by_line if a <= line <= b), None)
        if copy is None:
            continue
        r = res[copy]
        if sev == "error":
            r["errors"].append(data)
            if "heartbeats" in data or "deterministic) timeout" in data:
                r["limit"] = True
        elif sev == "warning" and "sorry" in data:
            r["sorry"] = True
        elif re.search(r"Try (?:this|these)", data):
            r["suggest"] += suggestions(data)
    for r in res.values():
        r["ok"] = (not r["errors"] and not r["sorry"] and r["axioms"] is not None and "sorryAx" not in r["axioms"])
    return res


def run_batch(s, goals, entries=None, heartbeats=HEARTBEATS, seconds=SECONDS, src=None):
    """Compile one batch for `goals` (goal_of records). Returns (per-goal results, info): per goal,
    per portfolio key {ok, ms, limit, error, suggest}; info has the batch wall time, the number of
    attempts and whether the batch was stopped."""
    src = s._source() if src is None else src
    entries = available(s, src) if entries is None else entries
    text, attempts = batch_text(s, goals, entries, heartbeats, src)
    (s.ws / "Portfolio.lean").write_text(text)
    name = judge.output_name("portfolio", ".json")
    out = s.ws / name
    timeout = min(MAX_BATCH_SECONDS, BASE_SECONDS + seconds * len(attempts))
    t0 = time.monotonic()
    r = judge.in_container(s.ws, f"lake build {s.task.lib} >/dev/null 2>&1; "
                                 f"lake env lean --json Portfolio.lean > {name} 2>&1; tail -c 300 {name}",
                           timeout=timeout)
    ms = int((time.monotonic() - t0) * 1000)
    stopped = judge.TIMEOUT_MARK in r["output_tail"]
    output = out.read_text(errors="replace") if out.exists() else ""
    out.unlink(missing_ok=True)
    parsed = parse(output, attempts, s.ns)
    results = {g["name"]: {} for g in goals}
    for a in attempts:
        p = parsed[a["copy"]]
        ok = p["ok"] and not stopped
        sug = [x for x in p["suggest"] if PREFIX not in x]
        if a["key"] in SEARCH and ok and not sug:
            ok = False   # nothing bankable: the search found only a copy in the batch
        results[a["goal"]][a["key"]] = {"ok": ok, "ms": p["ms"], "limit": p["limit"],
                                        "error": (p["errors"][0][:300] if p["errors"] else None),
                                        "suggest": sug[:3]}
    return results, {"ms": ms, "attempts": len(attempts), "stopped": stopped, "timeout_s": timeout}


def run_portfolio(s, goals, heartbeats=HEARTBEATS, seconds=SECONDS, src=None):
    """run_batch, and when the wall allowance stopped it, one more batch without the searching
    tactics (the entries the heartbeat limit does not bound). Returns (results, info) with the
    time of both batches and `retried` when the second one ran."""
    src = s._source() if src is None else src
    results, info = run_batch(s, goals, heartbeats=heartbeats, seconds=seconds, src=src)
    if info["stopped"] and not s.budget.past_deadline():
        cheap = [e for e in available(s, src) if e[0] not in SEARCH]
        results, again = run_batch(s, goals, entries=cheap, heartbeats=heartbeats, seconds=seconds, src=src)
        info = {"ms": info["ms"] + again["ms"], "attempts": info["attempts"] + again["attempts"],
                "stopped": again["stopped"], "timeout_s": again["timeout_s"], "retried": True}
    return results, info


def bank_text(goal, key, res):
    """The text banked for a goal closed by `key`: its statement with the tactic (or, for a
    search, the first suggestion) as proof."""
    tac = res["suggest"][0] if key in SEARCH else tactic_for(dict((k, t) for k, t, _ in PORTFOLIO)[key], goal)
    return f"{goal['head']} := by\n{proof_body(tac)}"


def forbidden(code):
    return any(re.search(p, code) for p in judge.FORBIDDEN) or bool(judge.attribute_problems(code))


def context_key(s, src, goal):
    """A goal is retried only when its statement or the set of complete declarations changed."""
    done = sorted(n for n, _, text in declarations(src, s.ns) if not has_sorry(text))
    return hashlib.sha256((goal["name"] + "\0" + re.sub(r"\s+", " ", goal["head"]) + "\0" + " ".join(done)).encode()).hexdigest()


def settings(a):
    """(enabled, heartbeats, seconds) from the run's options; enabled by default."""
    return (getattr(a, "portfolio", "on") != "off", getattr(a, "portfolio_heartbeats", None) or HEARTBEATS,
            getattr(a, "portfolio_seconds", None) or SECONDS)


def close_goals(s, a, names, label=""):
    """Try the portfolio on the open goals among `names` (one batch for all of them) and bank the
    first closing proof of each. Returns {goal: portfolio key} for the goals banked."""
    on, heartbeats, seconds = settings(a)
    if not on or not names or s.budget.past_deadline():
        return {}
    src = s._source()
    seen = s.__dict__.setdefault("portfolio_seen", set())
    goals, keys = [], {}
    for n in dict.fromkeys(names):
        g = goal_of(s, n, src)
        if g is None:
            continue
        k = context_key(s, src, g)
        if k in seen:
            continue
        goals.append(g)
        keys[n] = k
    if not goals:
        return {}
    for k in keys.values():
        seen.add(k)
    results, info = run_portfolio(s, goals, heartbeats=heartbeats, seconds=seconds, src=src)
    closed = {}
    for g in goals:
        res = results.get(g["name"], {})
        for key, _, _ in PORTFOLIO:
            r = res.get(key)
            if not r or not r["ok"]:
                continue
            code = bank_text(g, key, r)
            if forbidden(code):
                continue
            if g["name"] not in s.theorems:
                s.targets.add(g["name"])
            import repair
            banked = s.bank(code)
            ok = g["name"] in banked and repair.own_sorry_free(s, g["name"])
            s.log(kind="portfolio_bank", name=g["name"], tactic=key, text=code[-600:], banked=ok, version=s.version)
            if ok:
                closed[g["name"]] = key
                break
    st = s.__dict__.setdefault("portfolio_stats", {"batches": 0, "goals": 0, "closed": 0, "ms": 0, "stopped": 0,
                                                   "closed_by": {}})
    st["batches"] += 1
    st["goals"] += len(goals)
    st["closed"] += len(closed)
    st["ms"] += info["ms"]
    st["stopped"] += bool(info["stopped"])
    for key in closed.values():
        st["closed_by"][key] = st["closed_by"].get(key, 0) + 1
    s.log(kind="portfolio", label=label, goals=[g["name"] for g in goals], closed=closed, ms=info["ms"],
          attempts=info["attempts"], stopped=info["stopped"], retried=info.get("retried", False), heartbeats=heartbeats,
          results={n: {k: [int(v["ok"]), v["ms"], int(v["limit"])] for k, v in r.items()} for n, r in results.items()})
    if closed:
        print(f"[portfolio] closed {closed}", flush=True)
    return closed


def summary(s):
    """Run totals of the portfolio for summary.json: batches, goals tried, goals closed (and by
    which entry), Lean milliseconds, batches stopped at their wall allowance."""
    return dict(s.__dict__.get("portfolio_stats") or {"batches": 0, "goals": 0, "closed": 0, "ms": 0, "stopped": 0,
                                                       "closed_by": {}})
