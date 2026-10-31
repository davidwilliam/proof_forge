#!/usr/bin/env python3
"""Attempt ledger: what a repair run established, so that a later attempt starts from it.

Every run of agents/repair.py (all loops) and agents/baseline.py writes `ledger.json` into its
run directory (repair.finish):

  proved         every declaration that some compiling version of the candidate held with no
                 `sorry` in it or in any candidate declaration it mentions: name, kind, full text,
                 the candidate declarations it depends on (by name, transitively), the task id and
                 the SHA-256 of the locked spec manifest it was proved against;
  skeletons      the proof skeletons accepted in the top-down loop (code, helpers, plan);
  open_goals     for each goal still open in the final candidate (a required theorem not proved, a
                 helper theorem proved by `sorry`): what was tried (snippets and the Lean messages
                 they got, portfolio tactics), the last unsolved goals Lean reported, the dialogs,
                 turns and list-price dollars spent on it;
  best_candidate the compiling version with the most required theorems proved, and the final one.

`repair.py --resume-from DIR[,DIR...]` and `baseline.py --resume-from ...` read ledgers back
(load_many). A ledger is used only when its task id and spec hash are the current task's. A run
directory written before ledgers existed is reconstructed from its events and candidate versions;
its spec hash is the current lock's only when git shows the lock unchanged since the run started.
Nothing in a ledger is trusted: the base candidate and every carried declaration are compiled
again by Lean in the new run (best_base, carry), inside its budget.

Usage: ledger.py RUN_DIR [--task T] [--out FILE]   writes (or prints) the ledger of a run directory
"""
import argparse, hashlib, json, pathlib, re, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "agents"))
sys.path.insert(0, str(ROOT / "harness"))
import budget  # noqa: E402
import task as taskmod  # noqa: E402

SCHEMA = 1
NAME = "ledger.json"
KIND = "proofforge-attempt-ledger"
DECL_KIND = re.compile(r"\b(theorem|lemma|def|instance|abbrev|structure|inductive)\s")
TOKEN = re.compile(r"[A-Za-z_Ͱ-Ͽ][\w'!?Ͱ-Ͽ]*")


def spec_sha256(task):
    return task.locked()["manifest_sha256"]


def _repair():
    import repair
    return repair


def _norm(text):
    return re.sub(r"\s+", " ", text or "").strip()


def has_sorry(text):
    return bool(re.search(r"(?<![\w.'])sorry(?![\w'])", re.sub(r"--[^\n]*", "", text or "")))


def split_proof(text):
    """(statement, proof) of a declaration's text, split at its first `:=` outside brackets;
    (None, None) when there is none (for example a definition by pattern matching)."""
    depth, i = 0, 0
    while i < len(text) - 1:
        ch = text[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            return text[:i].rstrip(), text[i + 2:]
        i += 1
    return None, None


def boundary(ns):
    end = f"end {ns}"
    return re.compile(r"^(?:@\[|/--|private |protected |noncomputable |theorem |lemma |def |instance |abbrev "
                      rf"|structure |inductive |open |{re.escape(end)})", re.M)


def declarations(src, ns):
    """Top-level declarations of a candidate in file order: [(short name, kind, text)], each text
    from its first line to the next declaration boundary (one pass)."""
    DECL = _repair().Session.DECL
    bounds = sorted({m.start() for m in boundary(ns).finditer(src)} | {len(src)})
    out = []
    for m in DECL.finditer(src):
        end = next((b for b in bounds if b > m.start()), len(src))
        text = src[m.start():end].rstrip()
        k = DECL_KIND.search(text.split("\n", 1)[0] + " ")
        out.append((m.group(1).split(".")[-1], k.group(1) if k else "def", text))
    return out


def statement(text):
    """A declaration's text up to its proof (definitions: the whole text, since the body matters)."""
    k = DECL_KIND.search(text.split("\n", 1)[0] + " ")
    if not k or k.group(1) not in ("theorem", "lemma"):
        return text.strip()
    head, _ = split_proof(text)
    return (head or text).strip()


def proved_in(src, ns):
    """Declarations of one compiling version with no `sorry` in them or in any candidate
    declaration they mention: {name: (kind, text, deps)} with deps transitive."""
    decls = declarations(src, ns)
    names = {n for n, _, _ in decls}
    text_of = {n: (k, t) for n, k, t in reversed(decls)}   # first occurrence wins
    direct = {}
    for n, (_, t) in text_of.items():
        toks = set()
        for tok in TOKEN.findall(t):
            toks.update(tok.split("."))
        direct[n] = (toks & names) - {n}
    memo = {}

    def closure(n, stack=()):
        if n in memo:
            return memo[n]
        if n in stack:
            return set(), True
        seen, dirty = set(), has_sorry(text_of[n][1])
        for d in direct[n]:
            sub, sd = closure(d, stack + (n,))
            seen |= {d} | sub
            dirty = dirty or sd
        memo[n] = (seen, dirty)
        return memo[n]
    out = {}
    for n, (k, t) in text_of.items():
        deps, dirty = closure(n)
        if not dirty:
            out[n] = (k, t, sorted(deps))
    return out


# Run records

def _events(run_dir):
    p = pathlib.Path(run_dir) / "events.jsonl"
    if not p.exists():
        return []
    out = []
    for l in p.read_text(errors="replace").splitlines():
        try:
            out.append(json.loads(l))
        except ValueError:
            pass
    return out


def goal_label(label):
    """The goal a dialog label is about (`pass1:req_x`, `d1:td0_h`, `resume:h`), or None."""
    if not label or ":" not in label:
        return None
    return label.split(":", 1)[1]


LEAN_MSG = re.compile(r"(unsolved goals|error:|could not prove|failed)", re.I)


def goal_notes(events):
    """Per goal, what the dialogs on it did: dialogs, turns, dollars, the snippets tried with the
    first lines Lean answered, the last unsolved goals Lean reported, the model's last words,
    planner decompositions and portfolio tactics tried."""
    notes = {}

    def rec(g):
        return notes.setdefault(g, {"dialogs": 0, "turns": 0, "usd_list": 0.0, "tried": [], "last_lean": "",
                                    "last_words": "", "plans": [], "portfolio": [], "refuted": False})
    for e in events:
        k = e.get("kind")
        g = goal_label(e.get("label"))
        if k == "turn" and g:
            r = rec(g)
            r["turns"] += 1
            r["dialogs"] += 1 if e.get("turn") == 0 else 0
            try:
                r["usd_list"] += budget.list_cost(e.get("model"), e.get("usage") or {})
            except KeyError:
                pass
            if (e.get("text") or "").strip():
                r["last_words"] = e["text"].strip()[:600]
        elif k == "tool" and g:
            r = rec(g)
            res = e.get("result") or ""
            if e.get("name") in ("try_snippet", "replace_declaration"):
                code = (e.get("args") or {}).get("code") or (e.get("args") or {}).get("text") or ""
                first = next((l for l in res.splitlines() if LEAN_MSG.search(l)), res.split("\n", 1)[0])
                r["tried"].append({"tool": e["name"], "code": code[:1200], "lean": first[:300]})
            if "unsolved goals" in res or "error" in res:
                r["last_lean"] = res[-1500:]
        elif k == "plan" and e.get("theorem"):
            r = rec(e["theorem"])
            r["plans"].append(e.get("lemmas") or [])
            r["usd_list"] += e.get("usd_list") or 0.0
        elif k == "portfolio":
            for gname, res in (e.get("results") or {}).items():
                if gname not in (e.get("closed") or {}):
                    rec(gname)["portfolio"] = sorted(res)
        elif k == "refute" and e.get("ok"):
            rec(e["name"])["refuted"] = True
    for r in notes.values():
        r["usd_list"] = round(r["usd_list"], 4)
        r["tried"] = r["tried"][-4:]
    return notes


def best_from_events(events, out_dir, task):
    """The version with the most required theorems proved among those whose status the run
    recorded (`check` in the repair loops, `audit` in A0); latest on a tie."""
    best = None
    for e in events:
        st = e.get("status")
        if e.get("kind") not in ("check", "audit") or not isinstance(st, dict) or e.get("errors"):
            continue
        n = sum(1 for v in st.values() if v == "PROVED")
        if best is None or n >= best[0]:
            best = (n, e.get("version"), sorted(t for t, v in st.items() if v == "PROVED"))
    if best is None or best[1] is None:
        return None
    f = pathlib.Path(out_dir) / f"candidate_v{best[1]:03d}.lean"
    if not f.exists():
        return None
    return {"version": best[1], "proved_required": best[2], "text": f.read_text()}


def _open_goals(task, final_text, final_status, notes, run_turns=None, run_usd=None, last_feedback=""):
    out = []
    for n, kind, text in declarations(final_text, task.ns):
        if kind not in ("theorem", "lemma") or n in task.theorems or not has_sorry(text):
            continue
        out.append(_goal(n, False, statement(text), notes.get(n)))
    for t in task.theorems:
        if (final_status or {}).get(t) == "PROVED":
            continue
        text = next((x for n, _, x in declarations(final_text, task.ns) if n == t), "")
        g = _goal(t, True, statement(text) if text else t, notes.get(t))
        if not notes.get(t) and run_turns is not None:
            g.update({"scope": "run", "turns": run_turns, "usd_list": run_usd, "last_lean": last_feedback[-1500:]})
        out.append(g)
    return out


def _goal(name, required, stmt, note):
    g = {"name": name, "required": required, "statement": stmt, "scope": "goal"}
    g.update(note or {"dialogs": 0, "turns": 0, "usd_list": 0.0, "tried": [], "last_lean": "", "last_words": "",
                      "plans": [], "portfolio": [], "refuted": False})
    return g


def build(task, run_dir, sources, events, final_text, final_status, arm, extra=None, reconstructed=False,
          spec=None, skeletons=None):
    """A ledger from a run's compiling sources, events and final candidate."""
    sha = spec or spec_sha256(task)
    proved, order = {}, []
    for src in sources:
        for n, (k, t, deps) in proved_in(src, task.ns).items():
            key = (n, _norm(statement(t)))
            if key not in proved:
                order.append(key)
            proved[key] = {"name": n, "kind": k, "text": t, "deps": deps, "statement": statement(t),
                           "required_definition": n in task.definitions, "required_theorem": n in task.theorems,
                           "task": task.id, "spec_sha256": sha}
    notes = goal_notes(events)
    turns = sum(1 for e in events if e.get("kind") in ("turn", "attempt"))
    audits = [e for e in events if e.get("kind") == "audit" and e.get("feedback")]
    s = extra or {}
    best = best_from_events(events, run_dir, task)
    final_proved = sorted(t for t, v in (final_status or {}).items() if v == "PROVED")
    if best is None or len(best["proved_required"]) <= len(final_proved):
        best = {"version": "final", "proved_required": final_proved, "text": final_text}
    return {
        "schema": SCHEMA, "kind": KIND, "task": task.id, "spec_sha256": sha,
        "run_dir": str(pathlib.Path(run_dir).resolve()), "arm": arm, "loop": s.get("mode"),
        "model": s.get("model"), "created": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "reconstructed": reconstructed,
        "final": {"text": final_text, "sha256": hashlib.sha256(final_text.encode()).hexdigest(),
                  "proved_required": final_proved},
        "best_candidate": best,
        "proved": [proved[k] for k in order],
        "skeletons": skeletons or [],
        "open_goals": _open_goals(task, final_text, final_status, notes,
                                  run_turns=turns, run_usd=(s.get("budget") or {}).get("usd_list"),
                                  last_feedback=(audits[-1]["feedback"] if audits else "")),
        "budget": s.get("budget"),
        "resumed_from": s.get("resumed_from") or [],
    }


def write(s, out, arm, summary):
    """The ledger of a live session (repair.finish)."""
    srcs = list(dict.fromkeys(src for _, src in sorted(s.compiled.values())))
    final = (out / "final.lean").read_text()
    if final not in srcs:
        srcs.append(final)
    led = build(s.task, out, srcs, s.events, final, summary.get("final_status"), arm, summary,
                skeletons=getattr(s, "skeletons", []))
    (out / NAME).write_text(json.dumps(led, indent=1))
    return led


def lock_unchanged_since(task, t):
    """True when git shows the task's spec lock last changed before time `t` (epoch seconds)."""
    lock = (task.root / "spec/locked.json").resolve()
    try:
        r = subprocess.run(["git", "log", "-1", "--format=%ct", "--", str(lock)], cwd=lock.parent,
                           capture_output=True, text=True, timeout=30)
        dirty = subprocess.run(["git", "status", "--porcelain", "--", str(lock)], cwd=lock.parent,
                               capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return False
    if r.returncode or not r.stdout.strip() or dirty.stdout.strip():
        return False
    return int(r.stdout.strip()) <= t


def reconstruct(run_dir, task):
    """A ledger for a run directory written before ledgers existed: compiling sources are the
    final candidate and the versions not undone by the next write (a revert), and the spec hash is
    the current lock's when git shows the lock unchanged since the run started (else None)."""
    d = pathlib.Path(run_dir)
    summ = json.loads((d / "summary.json").read_text())
    ev = _events(d)
    final = (d / "final.lean").read_text()
    writes = [e for e in ev if e.get("kind") == "write"]
    srcs = []
    if summ.get("arm") != "A0":
        for w, nxt in zip(writes, writes[1:] + [None]):
            if nxt is not None and str(nxt.get("why", "")).startswith("revert"):
                continue
            f = d / f"candidate_v{w['version']:03d}.lean"
            if f.exists():
                srcs.append(f.read_text())
    srcs.append(final)
    t0 = ev[0]["t"] if ev else (d / "summary.json").stat().st_mtime
    sha = spec_sha256(task) if summ.get("task") == task.id and lock_unchanged_since(task, t0) else None
    skels = []
    for e in ev:
        if e.get("kind") == "skeleton" and e.get("accepted"):
            f = d / f"skeleton_{e['round']}.lean"
            skels.append({"round": e["round"], "code": f.read_text() if f.exists() else e.get("code", ""),
                          "helpers": sorted(e.get("helpers") or {}), "derived": e.get("derived", [])})
    led = build(task, d, list(dict.fromkeys(srcs)), ev, final, summ.get("final_status"), summ.get("arm"), summ,
                reconstructed=True, spec=sha, skeletons=skels)
    led["task"] = summ.get("task")
    return led


def ledger_sha256(led):
    return hashlib.sha256(json.dumps(led, sort_keys=True).encode()).hexdigest()


def load(path, task):
    """(ledger, refusal reason or None) for a run directory or a ledger file."""
    p = pathlib.Path(path)
    try:
        if p.is_file():
            led = json.loads(p.read_text())
        elif (p / NAME).is_file():
            led = json.loads((p / NAME).read_text())
        elif (p / "summary.json").is_file() and (p / "final.lean").is_file():
            led = reconstruct(p, task)
        else:
            return None, "no ledger.json and no run record (summary.json, final.lean) to reconstruct one from"
    except (OSError, ValueError, KeyError) as e:
        return None, f"unreadable: {e}"
    if led.get("kind") != KIND:
        return led, "not an attempt ledger"
    if led.get("task") != task.id:
        return led, f"task {led.get('task')!r} is not {task.id!r}"
    if not led.get("spec_sha256"):
        return led, "spec hash unknown (the task's lock changed after the run started, or git cannot tell)"
    if led["spec_sha256"] != spec_sha256(task):
        return led, f"spec hash {led['spec_sha256'][:12]} is not the current lock's {spec_sha256(task)[:12]}"
    return led, None


def load_many(paths, task):
    """Ledgers usable for `task`, and a provenance record of every path given."""
    used, record = [], []
    for path in [x for x in paths if x]:
        led, why = load(path, task)
        rec = {"path": str(path), "run_dir": (led or {}).get("run_dir") or str(pathlib.Path(path).resolve()),
               "reconstructed": bool((led or {}).get("reconstructed")), "used": why is None, "refused": why}
        if led is not None:
            rec["ledger_sha256"] = ledger_sha256(led)
            rec["spec_sha256"] = led.get("spec_sha256")
        record.append(rec)
        if why is None:
            used.append(led)
    return used, record


# Resuming

def best_base(s, ledgers):
    """Compile each prior attempt's best and final candidate in the session and keep the one with
    the most required theorems PROVED (first on a tie); the candidate on disk becomes it. Returns
    its record, or None when no prior candidate compiles."""
    cands, seen = [], set()
    for led in ledgers:
        for which in ("best_candidate", "final"):
            c = led.get(which) or {}
            text = c.get("text")
            if text and text not in seen:
                seen.add(text)
                cands.append((led["run_dir"], which, text))
    best = None
    for run_dir, which, text in cands:
        s._save(text, f"resume: candidate of {pathlib.Path(run_dir).name} ({which})")
        st = s.check_status()
        n = sum(1 for v in st.values() if v == "PROVED")
        s.log(kind="resume_base", run_dir=run_dir, which=which, status=st, proved=n)
        if "ERROR" in st.values():
            continue
        if best is None or n > best["proved"]:
            best = {"run_dir": run_dir, "which": which, "proved": n, "text": text,
                    "proved_required": sorted(t for t, v in st.items() if v == "PROVED")}
    if best is not None:
        s._save(best["text"], f"resume: base from {pathlib.Path(best['run_dir']).name} ({best['which']})")
        s.compile()
    return best


def lean_messages(s, text, name="Carry"):
    """Lean's messages for `text` compiled as one file in the session workspace (JSON, every
    message, not a tail): [(line, severity, text)]; None when the run stopped at its time limit."""
    import judge
    (s.ws / f"{name}.lean").write_text(text)
    oname = judge.output_name(name.lower(), ".json")
    out = s.ws / oname
    r = judge.in_container(s.ws, f"lake build {s.task.lib} >/dev/null 2>&1; lake env lean --json {name}.lean > "
                                 f"{oname} 2>&1; tail -c 300 {oname}", timeout=600)
    text = out.read_text(errors="replace") if out.exists() else ""
    out.unlink(missing_ok=True)
    if judge.TIMEOUT_MARK in r["output_tail"]:
        return None
    msgs = []
    for raw in text.splitlines():
        try:
            m = json.loads(raw)
        except ValueError:
            if "error" in raw:
                msgs.append((0, "error", raw))
            continue
        msgs.append(((m.get("pos") or {}).get("line", 0), m.get("severity"), m.get("data") or ""))
    return msgs


def _spans(src, ns):
    """(name, first line, last line) of each declaration (1-based)."""
    out, pos = [], 0
    for n, _, text in declarations(src, ns):
        at = src.find(text, pos)
        if at < 0:
            continue
        a = src.count("\n", 0, at) + 1
        out.append((n, a, a + text.count("\n")))
        pos = at + len(text)
    return out


def _topo(items):
    """Records ordered so that each comes after the carried records it depends on."""
    by = {r["name"]: r for r in items}
    out, seen = [], set()

    def visit(r, stack=()):
        if r["name"] in seen or r["name"] in stack:
            return
        for d in r["deps"]:
            if d in by:
                visit(by[d], stack + (r["name"],))
        seen.add(r["name"])
        out.append(r)
    for r in items:
        visit(r)
    return out


def select(s, ledgers, src):
    """Declarations to carry into `src`: proved ones from the ledgers, the required definitions
    left to the base, de-duplicated by statement (a duplicate is kept only when a kept declaration
    mentions its name), without what the base already has complete. Returns (records, skipped)."""
    base = {n: (k, t) for n, k, t in declarations(src, s.ns)}
    base_complete = {_norm(statement(t)) for n, (k, t) in base.items() if not has_sorry(t)}
    pool, skipped = {}, []
    for led in ledgers:
        for r in led.get("proved", []):
            if r.get("task") != s.task.id or r.get("spec_sha256") != led.get("spec_sha256"):
                skipped.append({"name": r["name"], "reason": "task or spec hash differs"})
                continue
            if r["name"] in s.task.definitions:
                continue
            cur = base.get(r["name"])
            if cur is not None:
                if not has_sorry(cur[1]):
                    continue   # the base has it complete
                if _norm(statement(cur[1])) != _norm(r["statement"]):
                    skipped.append({"name": r["name"], "reason": "the base has an open declaration of this name "
                                                                  "with another statement"})
                    continue
            if r["name"] in s.theorems and cur is None:
                continue
            pool.setdefault(r["name"], r)   # first ledger given wins on a name
    # De-duplication by statement: drop records whose statement the base has complete, and among
    # records with one statement keep the first, unless a kept record mentions the others.
    keep, by_stmt = {}, {}
    for n, r in pool.items():
        st = _norm(r["statement"])
        if st in base_complete and n not in base:
            skipped.append({"name": n, "reason": "duplicate of a complete declaration of the base"})
            continue
        if st in by_stmt and r["kind"] in ("theorem", "lemma"):
            by_stmt[st].append(n)
            continue
        by_stmt.setdefault(st, []).append(n)
        keep[n] = r
    needed = set()
    for r in keep.values():
        needed |= set(r["deps"])
    for st, names in by_stmt.items():
        for n in names[1:]:
            if n in needed:
                keep[n] = pool[n]
            else:
                skipped.append({"name": n, "reason": f"same statement as {names[0]}"})
    # A record whose dependency is neither in the base nor carried cannot compile.
    changed = True
    while changed:
        changed = False
        for n, r in list(keep.items()):
            miss = [d for d in r["deps"] if d not in keep and d not in base]
            if miss:
                del keep[n]
                skipped.append({"name": n, "reason": f"depends on {', '.join(miss[:3])}, which is not carried"})
                changed = True
    return _topo(list(keep.values())), skipped


def install(s, src, records):
    """`src` with `records` installed. An open declaration of the base is replaced in place. New
    declarations go, in dependency order, before the first base declaration that is replaced or
    mentions one of them (so that it can use them), or before the namespace end when that point
    comes before a base declaration they depend on. The session keeps required theorems last."""
    names = {r["name"] for r in records}
    decls = declarations(src, s.ns)
    base_names = [n for n, _, _ in decls]
    replaced = {r["name"] for r in records if r["name"] in base_names}
    new = [r for r in records if r["name"] not in replaced]
    first = None
    for i, (n, _, text) in enumerate(decls):
        toks = {p for tok in TOKEN.findall(text) for p in tok.split(".")}
        if n in replaced or (toks & (names - replaced)):
            first = i
            break
    early, late = [], []
    for r in new:
        last_dep = max([base_names.index(d) for d in r["deps"] if d in base_names] or [-1])
        (early if first is not None and last_dep < first else late).append(r)
    # A record that depends on a late record is late too.
    moved = True
    while moved:
        moved = False
        late_names = {r["name"] for r in late}
        for r in list(early):
            if set(r["deps"]) & late_names:
                early.remove(r)
                late.append(r)
                moved = True
    late = [r for r in new if r in late]
    if early:
        lines = src.split("\n")
        at = src.count("\n", 0, src.find(decls[first][2])) if src.find(decls[first][2]) >= 0 else len(lines)
        while at > 0 and (lines[at - 1].startswith("@[") or lines[at - 1].rstrip().endswith("-/")):
            if lines[at - 1].rstrip().endswith("-/"):
                while at > 0 and not lines[at - 1].lstrip().startswith("/-"):
                    at -= 1
            at -= 1
        block = "\n\n".join(r["text"].rstrip() for r in early).split("\n") + [""]
        lines[at:at] = block
        src = "\n".join(lines)
    for r in [r for r in records if r["name"] in replaced] + late:
        src, _ = s._replace_in(src, r["name"], r["text"])
    return s._normalize(src)


def carry(s, ledgers, max_rounds=6):
    """Install the ledgers' proved declarations into the current candidate, checked by Lean: the
    whole set is compiled, every carried declaration with an error (or that a base declaration
    with a new error mentions) is dropped with the carried declarations that depend on it, and
    this repeats until the file compiles; that set is kept. Returns (carried names, dropped)."""
    base = s._source()
    records, dropped = select(s, ledgers, base)
    s.log(kind="resume_select", candidates=[r["name"] for r in records], skipped=dropped[:200])
    if not records:
        return [], dropped
    live = {r["name"]: r for r in records}
    for rnd in range(max_rounds):
        if s.budget.past_deadline():
            dropped += [{"name": n, "reason": "deadline reached while checking"} for n in live]
            live = {}
            break
        text = install(s, base, [r for r in records if r["name"] in live])
        msgs = lean_messages(s, text)
        if msgs is None:
            dropped += [{"name": n, "reason": "time limit reached while checking"} for n in live]
            live = {}
            break
        errs = [(l, d) for l, sev, d in msgs if sev == "error"]
        if not errs:
            break
        spans = _spans(text, s.ns)
        bad = set()
        for line, data in errs:
            owner = next((n for n, a, b in spans if a <= line <= b), None)
            if owner in live:
                bad.add(owner)
                dropped.append({"name": owner, "reason": "Lean error: " + data.split("\n")[0][:200]})
            elif owner is not None:
                # A base declaration broke: the carried declarations it mentions are the cause.
                btxt = next((t for n, _, t in declarations(text, s.ns) if n == owner), "")
                toks = {p for tok in TOKEN.findall(btxt) for p in tok.split(".")}
                cause = (toks & set(live)) - {owner}
                if owner in live:
                    cause.add(owner)
                for c in cause:
                    bad.add(c)
                    dropped.append({"name": c, "reason": f"breaks `{owner}` of the base: " + data.split("\n")[0][:150]})
                if not cause:
                    bad |= set(live)   # cannot attribute it: carry nothing
                    dropped += [{"name": n, "reason": "unattributed error: " + data.split("\n")[0][:150]} for n in live]
        if not bad:
            bad |= set(live)
            dropped += [{"name": n, "reason": "errors outside the declarations"} for n in live]
        for n in bad:
            live.pop(n, None)
        changed = True
        while changed:   # dependents of a dropped declaration go too
            changed = False
            for n, r in list(live.items()):
                if any(d in bad or (d not in live and d in {x["name"] for x in records}) for d in r["deps"]):
                    live.pop(n)
                    bad.add(n)
                    dropped.append({"name": n, "reason": "depends on a dropped declaration"})
                    changed = True
    else:
        dropped += [{"name": n, "reason": "no compiling set within the rounds"} for n in live]
        live = {}
    carried = [r["name"] for r in records if r["name"] in live]
    if carried:
        s._save(install(s, base, [r for r in records if r["name"] in live]), f"resume: carried {len(carried)} declarations")
        if "error:" in s.compile(2000)["output_tail"]:
            s._save(base, "revert resume carry")
            dropped += [{"name": n, "reason": "the carried file did not build"} for n in carried]
            carried = []
    s.log(kind="resume_carry", carried=carried, dropped=dropped[:300])
    return carried, dropped


def notes_by_goal(ledgers):
    """Failure notes of the prior attempts per goal: [(run name, note)]."""
    out = {}
    for led in ledgers:
        for g in led.get("open_goals", []):
            out.setdefault(g["name"], []).append((pathlib.Path(led["run_dir"]).name, g))
    return out


def render_note(run, g, limit=2400):
    """A prior attempt's failure on one goal, for a prompt."""
    scope = "the whole run (A0 works on the whole file)" if g.get("scope") == "run" else "this goal"
    lines = [f"Run {run}: {g.get('dialogs', 0)} dialog(s), {g.get('turns', 0)} turn(s), "
             f"${(g.get('usd_list') or 0):.2f} at list prices spent on {scope}, not proved."]
    if g.get("refuted"):
        lines.append("Lean accepted a proof that this statement is false.")
    if g.get("portfolio"):
        lines.append(f"Tactics that did not close it: {', '.join(g['portfolio'])}.")
    for p in g.get("plans") or []:
        lines.append(f"Planner decomposition tried: {', '.join(p)}.")
    for t in (g.get("tried") or [])[-2:]:
        lines.append(f"Tried ({t['tool']}):\n```lean\n{t['code'][:700]}\n```\nLean: {t['lean']}")
    if g.get("last_lean"):
        lines.append(f"Last Lean output:\n{g['last_lean'][-900:]}")
    if g.get("last_words"):
        lines.append(f"The model's last words: {g['last_words'][:400]}")
    text = "\n".join(lines)
    return text if len(text) <= limit else text[:limit - 3] + "..."


def prompt_notes(notes, name, limit=4000):
    """The text a prompt gets for goal `name` from prior attempts, or ''."""
    parts = [render_note(run, g) for run, g in notes.get(name, [])]
    if not parts:
        return ""
    text = ("Previous attempts at this goal failed as follows (the file may differ now). Do not repeat an approach "
            "that failed; try a different decomposition, lemma or tactic:\n" + "\n\n".join(parts))
    return text[-limit:]


def summary_text(ledgers, limit=6000):
    """The failure summary of prior attempts for a whole-file prompt (A0, the free loop): per run,
    the required theorems it left unproved, what the run spent, its last Lean feedback, and the
    notes of up to six goals it worked on one by one."""
    parts = []
    for led in ledgers:
        run = pathlib.Path(led["run_dir"]).name
        goals = led.get("open_goals", [])
        req = [g for g in goals if g.get("required")]
        b = led.get("budget") or {}
        parts.append(f"Run {run} ({led.get('arm')}, {led.get('loop') or 'whole file'}): {len(req)} required theorem(s) "
                     f"left unproved ({', '.join(g['name'] for g in req) or 'none'}) after "
                     f"${(b.get('usd_list') or 0):.2f} at list prices.")
        whole = next((g for g in goals if g.get("scope") == "run"), None)
        if whole and whole.get("last_lean"):
            parts.append(f"Its last Lean feedback:\n{whole['last_lean'][-900:]}")
        for g in [g for g in goals if g.get("scope") != "run" and (g.get("turns") or g.get("tried"))][:6]:
            parts.append(f"`{g['statement'][:300]}`\n" + render_note(run, g, 1200))
    text = "\n\n".join(parts)
    return text if len(text) <= limit else text[:limit - 3] + "..."


def resume_goals(s, ledgers):
    """Goals the prior attempts left open that are still open in the current candidate: helper
    theorems first (shared decompositions), then required theorems in listed order."""
    repair = _repair()
    names = []
    for led in ledgers:
        for g in led.get("open_goals", []):
            if g["name"] not in names:
                names.append(g["name"])
    src = s._source()
    open_now = [n for n in names if repair.decl_text(s, n, src) and not repair.own_sorry_free(s, n)]
    helpers = [n for n in open_now if n not in s.theorems]
    return helpers + [t for t in s.theorems if t in open_now]


def round_offset(ledgers):
    """1 + the highest skeleton round and planner index the prior attempts used, so that new
    helper names (`td<k>_`, `plan<k>_`) never collide with carried ones."""
    rnd, plan = -1, -1
    for led in ledgers:
        for r in led.get("proved", []) + led.get("open_goals", []):
            m = re.match(r"td(\d+)_", r["name"])
            if m:
                rnd = max(rnd, int(m.group(1)))
            m = re.match(r"plan(\d+)_", r["name"])
            if m:
                plan = max(plan, int(m.group(1)))
        for sk in led.get("skeletons", []):
            rnd = max(rnd, int(sk.get("round", 0)))
    return rnd + 1, plan + 1


def main():
    ap = argparse.ArgumentParser(description="Write the attempt ledger of a run directory.")
    ap.add_argument("run_dir")
    ap.add_argument("--task", help="task id (default: the one in summary.json)")
    ap.add_argument("--out", help="ledger file to write (default: print a summary only)")
    a = ap.parse_args()
    d = pathlib.Path(a.run_dir)
    tid = a.task or json.loads((d / "summary.json").read_text())["task"]
    task = taskmod.load(tid)
    led, why = load(d, task)
    if a.out and led is not None:
        pathlib.Path(a.out).write_text(json.dumps(led, indent=1))
    print(json.dumps({"run_dir": str(d), "task": tid, "usable": why is None, "refused": why,
                      "spec_sha256": (led or {}).get("spec_sha256"), "proved": len((led or {}).get("proved", [])),
                      "open_goals": [g["name"] for g in (led or {}).get("open_goals", [])],
                      "best_candidate": {k: v for k, v in ((led or {}).get("best_candidate") or {}).items() if k != "text"}},
                     indent=1))


if __name__ == "__main__":
    main()
