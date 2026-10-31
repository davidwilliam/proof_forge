#!/usr/bin/env python3
"""Failure mining: the goals that agent runs failed to prove, grouped by mathematical shape.

No model is called and no Lean runs here; this reads run directories (results/**/events.jsonl,
final.lean, candidate_v*.lean, summary.json, eval.json, passport.json).

  split      results/feedback-library-1/split.json: task families are either in the mining set or
             held out. `goals --set mining` reads only runs of mining-set tasks; the held-out goals
             are read only by the measurement (`goals --set held-out`).
  runs       a run directory is one with events.jsonl or final.lean. It is accepted when its
             Passport is VERIFIED, its eval.json has judge ACCEPT and binary PASS, or (with
             neither file) its summary.json says the candidate was accepted in the session;
             every other run is failed or partial.
  goals      for each failed or partial run, from the final candidate (final.lean, else the last
             candidate_vNNN.lean): every theorem whose proof still contains `sorry` (`required`
             when it is one of the task's required theorems, else `helper`); from the planner's
             events (`plan`, `decompose`, `architect`, `skeleton`): every lemma statement it
             proposed, `open` unless the final candidate proves it without `sorry`; from the tool
             results: the last `unsolved goals` text per theorem (the theorem is the one the
             snippet declares, or the one at the error's line in the candidate version checked).
  shapes     each goal's conclusion (the statement after its binders, or the goal after `⊢`) is
             tagged with the shape features `shape_tags` finds (sums after an update, floor and
             ceiling bounds, monotone accrual, run invariants, step-effect projections...); the
             clusters are the tag combinations, counted by run and by task family.
  proved     declarations failed runs proved (sorry-free in the final candidate) are harvested
             by `harness/harvest.py run --unverified`, not here.

Usage: mine.py runs [--results DIR] | goals --set mining|held-out [--results DIR] [--out F]
       | clusters GOALS.jsonl
"""
import argparse, collections, glob, json, os, pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import fin_lib, harvest, task as taskmod  # noqa: E402

ROOT = fin_lib.ROOT
SPLIT = ROOT / "results/feedback-library-1/split.json"
OUT = ROOT / "results/feedback-library-1"


def load_split(path=SPLIT):
    return json.loads(pathlib.Path(path).read_text())


def task_set(task_id, split):
    t = split["tasks"].get(task_id)
    return t["set"] if t else None


# ---------------------------------------------------------------------------------------------
# Runs

def events(run):
    f = pathlib.Path(run) / "events.jsonl"
    if not f.is_file():
        return []
    out = []
    for line in f.read_text(errors="replace").splitlines():
        try:
            out.append(json.loads(line))
        except ValueError:
            continue
    return out


def run_task(run, evs):
    s = pathlib.Path(run) / "summary.json"
    if s.is_file():
        try:
            t = json.loads(s.read_text()).get("task")
            if t:
                return t
        except ValueError:
            pass
    for e in evs:
        if e.get("kind") == "start" and e.get("task"):
            return e["task"]
    for name in ("eval.json", "passport.json"):
        f = pathlib.Path(run) / name
        if f.is_file():
            d = json.loads(f.read_text())
            t = d.get("task")
            return t["id"] if isinstance(t, dict) else t
    return None


def outcome(run):
    """'accepted' or 'failed', with the evidence that decided it."""
    run = pathlib.Path(run)
    pp, ev, sm = run / "passport.json", run / "eval.json", run / "summary.json"
    if pp.is_file():
        st = json.loads(pp.read_text()).get("status")
        return ("accepted" if st == "VERIFIED" else "failed"), f"passport {st}"
    if ev.is_file():
        e = json.loads(ev.read_text())
        ok = e.get("judge") == "ACCEPT" and e.get("binary") == "PASS"
        return ("accepted" if ok else "failed"), f"eval {e.get('judge')}/{e.get('binary')}"
    if sm.is_file():
        ok = bool(json.loads(sm.read_text()).get("accepted_in_session"))
        return ("accepted" if ok else "failed"), f"summary accepted_in_session={ok}"
    return "failed", "no verdict recorded"


def versions(run):
    out = {}
    for p in pathlib.Path(run).glob("candidate_v*.lean"):
        m = re.match(r"candidate_v(\d+)\.lean$", p.name)
        if m:
            out[int(m.group(1))] = p
    return out


def final_file(run):
    f = pathlib.Path(run) / "final.lean"
    if f.is_file():
        return f
    vs = versions(run)
    return vs[max(vs)] if vs else None


def runs(results):
    """Every run directory under `results` with its task, outcome and final candidate."""
    results = pathlib.Path(results)
    dirs = sorted({p.parent for p in results.rglob("events.jsonl")} | {p.parent for p in results.rglob("final.lean")})
    out = []
    for d in dirs:
        if "harvest-1" in d.parts or "feedback-library-1" in d.parts:
            continue
        evs = events(d)
        t = run_task(d, evs)
        if not t:
            continue
        oc, why = outcome(d)
        f = final_file(d)
        out.append({"run": str(d.relative_to(results)), "dir": str(d), "task": t, "outcome": oc, "evidence": why,
                    "final": str(f) if f else None})
    return out


# ---------------------------------------------------------------------------------------------
# Goals

def statement_conclusion(stmt):
    """The conclusion of a theorem statement: the text after the last top-level `:` that ends
    the binders (bracketed binders are skipped)."""
    s = stmt.strip()
    i, n = 0, len(s)
    while i < n:
        while i < n and s[i].isspace():
            i += 1
        if i < n and s[i] in "([{⦃⟨":
            i = harvest.matching(s, i) + 1
            continue
        break
    rest = s[i:]
    if rest.startswith(":"):
        return rest[1:].strip()
    m = re.match(r"[^:]*?:\s", rest)
    return rest[m.end():].strip() if m else rest.strip()


def goal_conclusion(goal):
    """The target of the first goal of an `unsolved goals` text."""
    m = re.search(r"⊢\s*(.*?)(?:\n\S[^\n]*:|\n\ncase|\Z)", goal, re.S)
    return re.sub(r"\s+", " ", m.group(1)).strip() if m else ""


def goal_hyps(goal):
    m = goal.split("⊢")[0] if "⊢" in goal else ""
    return [l.strip() for l in m.split("\n") if " : " in l]


def theorem_at(text, line):
    for name, _, _, first, last in harvest.theorem_spans(text):
        if first <= line <= last:
            return name
    return None


def snippet_theorem(code):
    m = re.search(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\s+(" + harvest.IDENT + ")", code or "", re.M)
    return m.group(1) if m else ("example" if re.search(r"^\s*example\b", code or "", re.M) else None)


GOAL_BLOCK = re.compile(r"(?:^|\n)([^\n]*?):(\d+):(\d+): error: unsolved goals\n(.*?)(?=\n[^\n]*:\d+:\d+: (?:error|warning|info)|\Z)", re.S)


def unsolved(evs, run):
    """{theorem: last unsolved-goal text} from the tool results of a run."""
    vs = versions(run)
    last = {}
    for e in evs:
        if e.get("kind") != "tool":
            continue
        res = e.get("result")
        if not isinstance(res, str) or "unsolved goals" not in res:
            continue
        args = e.get("args") if isinstance(e.get("args"), dict) else {}
        code = args.get("code") or args.get("content") or args.get("proof")
        for m in GOAL_BLOCK.finditer(res):
            where, line, goal = m.group(1), int(m.group(2)), m.group(4).strip()
            name = None
            if where.strip().startswith("snippet") and code:
                name = snippet_theorem(code)
            else:
                v = e.get("version")
                try:
                    v = int(v)
                except (TypeError, ValueError):
                    v = None
                if v in vs:
                    name = theorem_at(vs[v].read_text(errors="replace"), line)
            last[name or f"?{e.get('name')}"] = goal[:4000]
    return last


PLAN_KINDS = ("plan", "decompose", "architect", "skeleton")


def planner_lemmas(evs):
    """{name: statement} of every lemma a planner event proposed (the last statement per name)."""
    out = {}
    for e in evs:
        if e.get("kind") in PLAN_KINDS and isinstance(e.get("code"), str):
            try:
                p = harvest.parse(e["code"])
            except Exception:  # noqa: BLE001 - a planner reply this reader cannot parse
                continue
            for th in p["theorems"]:
                out[th["name"]] = th["statement"]
    return out


def goals_of(r):
    """Open goals of one failed run."""
    run = pathlib.Path(r["dir"])
    evs = events(run)
    try:
        t = taskmod.load(r["task"])
        required = set(t.theorems)
    except (FileNotFoundError, KeyError):
        required = set()
    out = []
    proved = set()
    if r["final"]:
        text = pathlib.Path(r["final"]).read_text(errors="replace")
        sites = harvest.sorry_sites(text)
        for name, a, b, first, _ in harvest.theorem_spans(text):
            short = name.split(".")[-1]
            if any(a <= s < b for s in sites):
                stmt = next((th["statement"] for th in harvest.parse(text)["theorems"] if th["name"] == name), "")
                out.append({"source": "final", "kind": "required" if short in required else "helper",
                            "name": name, "statement": stmt, "conclusion": statement_conclusion(stmt)})
            else:
                proved.add(short)
    for name, stmt in planner_lemmas(evs).items():
        if name.split(".")[-1] in proved or any(g["name"] == name for g in out):
            continue
        out.append({"source": "planner", "kind": "planner", "name": name, "statement": stmt,
                    "conclusion": statement_conclusion(stmt)})
    for name, goal in unsolved(evs, run).items():
        if name.split(".")[-1] in proved:
            continue
        out.append({"source": "unsolved", "kind": "goal", "name": name, "goal": goal,
                    "hyps": goal_hyps(goal), "conclusion": goal_conclusion(goal)})
    for g in out:
        g.update(run=r["run"], task=r["task"])
        g["tags"] = shape_tags(g)
    return out


# ---------------------------------------------------------------------------------------------
# Shapes

def shape_tags(g):
    """Shape features of a goal's conclusion (and hypotheses for goals): general patterns, not
    task names. A goal can have several."""
    c = g.get("conclusion") or ""
    full = c + " " + " ".join(g.get("hyps", [])) + " " + (g.get("statement") or "")
    tags = set()
    sumlike = re.search(r"\.sum\b|List\.sum|sumOver|foldl|foldr|\bsum\w*\b|total\w*", c)
    update = re.search(r"Function\.update|\bset\b|\.set\b|modify|\bif\s+\S+\s*=\s*\S+\s+then|fun\s+\w+\s*=>\s*if", c)
    if sumlike and update:
        tags.add("sum-after-update")
    elif sumlike:
        tags.add("sum")
    if re.search(r"(?<![/])/(?![/])|\bdiv\w*\b|mulDiv|ceilDiv|divUp|divDown|mulDown|mulUp|scale\w*", c):
        if re.search(r"≤|<|≥|>", c):
            tags.add("division-bound")
        else:
            tags.add("division-eq")
    if re.search(r"%", c):
        tags.add("mod")
    if re.search(r"\brun\b|\bruns?\w*\b|foldl\s*\(?\s*fun|List\.foldl|steps?\b.*\bops\b|exec\w*|\bapplyAll|\bprocess\w*", full) and \
            re.search(r"\bInv\w*|inv\w*|∀\s*\w+\s*∈|Reachable|reachable", full):
        tags.add("run-invariant")
    elif re.search(r"\brun\b|List\.foldl|foldl|exec\w*", c):
        tags.add("run")
    if re.search(r"index|Index|accru\w*|acc\b|cum\w*|emitted|accrued|growth|rate", c) and re.search(r"≤|<", c):
        tags.add("monotone-accrual")
    if re.search(r"\(\s*\w+\s+\w+\s+\w+\s*\)\.(snd|2|fst|1)\.|\.snd\.\w+|\.2\.\w+", c):
        tags.add("step-projection")
    if re.search(r"\bwith\b|\{\s*\w+\s+with", c):
        tags.add("record-update")
    if re.search(r"\bmatch\b|Outcome\.|\.ok\b|\.rejected\b|Except\.|some\s|none\b|Option\.", c):
        tags.add("result-case")
    if re.search(r"\.length\b|List\.length", c):
        tags.add("length")
    if re.search(r"∈|List\.Mem|\bmem\b|Nodup|nodup|\.contains|\.find\?|filter", c):
        tags.add("membership")
    if re.search(r"∀", c):
        tags.add("forall")
    if re.search(r"∃", c):
        tags.add("exists")
    if re.search(r"\bmin\b|\bmax\b|Nat\.min|Nat\.max", c):
        tags.add("min-max")
    if re.search(r"(?<![≤<≥>])\s-\s|\bsub\b|Nat\.sub", c):
        tags.add("truncated-sub")
    if re.search(r"\*", c) and re.search(r"≤|<", c) and "division-bound" not in tags:
        tags.add("product-bound")
    if not tags:
        if re.search(r"≤|<|≥|>", c):
            tags.add("order")
        elif re.search(r"=", c):
            tags.add("equation")
        else:
            tags.add("other")
    return sorted(tags)


def family(task_id, split):
    t = split["tasks"].get(task_id)
    return t["family"] if t else "?"


_RESTATED = {}


def restated_names(task_id):
    """The definitions of a task's specification whose text equals a library definition's (the
    restatements `lib_defs` replaces): {name: library name}."""
    if task_id not in _RESTATED:
        lib_defs, _ = harvest.library_tables()
        out = {}
        try:
            t = taskmod.load(task_id)
            for f in sorted((t.root / "spec").rglob("*.lean")):
                if f.name == "Challenge.lean":
                    continue
                for n, d in harvest.parse(f.read_text())["defs"].items():
                    full = lib_defs.get(harvest.norm_def(d["text"]))
                    if d["kw"] in ("def", "abbrev") and full:
                        out[n] = full
        except FileNotFoundError:
            pass
        _RESTATED[task_id] = out
    return _RESTATED[task_id]


def clusters(goals, split, examples=6):
    """Shape tags with the goals, runs and families that have them and example conclusions; a
    goal that mentions a definition its task restates from the library is also counted under
    `restated-library-definition`."""
    by = collections.defaultdict(list)
    for g in goals:
        text = (g.get("statement") or "") + " " + (g.get("goal") or g.get("conclusion") or "")
        names = restated_names(g["task"])
        hit = sorted(n for n in names if re.search(rf"(?<![\w.']){re.escape(n)}(?![\w'])", text))
        if hit:
            by["restated-library-definition"].append(g)
            g.setdefault("restated", hit)
        for tg in g["tags"]:
            by[tg].append(g)
    out = []
    for tg, gs in sorted(by.items(), key=lambda x: -len(x[1])):
        ex, seen = [], set()
        for g in gs:
            c = re.sub(r"\s+", " ", g.get("conclusion") or "")[:200]
            if c and c not in seen and len(ex) < examples:
                seen.add(c)
                ex.append({"task_family": family(g["task"], split), "source": g["source"], "conclusion": c})
        out.append({"shape": tg, "goals": len(gs), "runs": len({g["run"] for g in gs}),
                    "families": sorted({family(g["task"], split) for g in gs}),
                    "by_source": dict(collections.Counter(g["source"] for g in gs)), "examples": ex})
    return out


def collect_goals(results, which, split):
    rs = [r for r in runs(results) if task_set(r["task"], split) == which]
    failed = [r for r in rs if r["outcome"] == "failed"]
    goals = []
    for r in failed:
        goals += goals_of(r)
    return rs, failed, goals



# ---------------------------------------------------------------------------------------------
# Closing recorded open goals with a library, without model calls

# The fixed battery of harness/harvest.py (default tactics, the library tactics, `exact?`) with
# `grind` added before `exact?`.
TACTICS = harvest.SITE_TACTICS + ["grind"]
# With the new library, the same battery and then the library tactic `lib_defs` (restated
# definitions replaced by the library's) followed by the closing tactics and `exact?`.
NEW_TACTICS = ["(lib_defs <;> simp_all)", "(lib_defs <;> grind)", "(lib_defs <;> exact?)"]


def goal_statement(goal):
    """A theorem statement ` (h : T) ... : target` from an `unsolved goals` text, or None when
    the text cannot be read back (inaccessible names, elided proofs, several goals)."""
    if not goal or "✝" in goal or "⋯" in goal or "sorry" in goal or "⊢" not in goal:
        return None
    first = re.split(r"\n\s*\ncase |\ncase ", "\n" + goal)[1 if goal.startswith("case ") else 0]
    lines = [l for l in first.split("\n") if l.strip() and not l.startswith("case ")]
    hyps, target, in_target = [], [], False
    for l in lines:
        if l.startswith("⊢"):
            in_target = True
            target.append(l[1:].strip())
        elif in_target:
            if not l.startswith(" "):
                return None   # a second goal
            target.append(l.strip())
        elif l.startswith(" ") and hyps:
            hyps[-1] += " " + l.strip()
        elif " : " in l:
            hyps.append(l.strip())
        else:
            return None
    binders = []
    for h in hyps:
        names, _, ty = h.partition(" : ")
        if not re.fullmatch(r"[^\s:()]+(?:\s+[^\s:()]+)*", names.strip()):
            return None
        binders.append(f"({names.strip()} : {ty.strip()})")
    tgt = " ".join(target).strip()
    return (" " + " ".join(binders) if binders else "") + f" :\n    {tgt}" if tgt else None


def extras_of(goals):
    """[(label, statement)] of the planner lemmas and unsolved goals of a run, one per statement."""
    out, seen = [], set()
    for g in goals:
        if g["source"] == "planner":
            stmt = g["statement"]
        elif g["source"] == "unsolved":
            stmt = goal_statement(g.get("goal"))
        else:
            continue
        if not stmt or stmt in seen:
            continue
        seen.add(stmt)
        out.append((g["source"], g["name"], stmt))
    return out


def augment(text, extras):
    """The candidate with each extra statement appended as a theorem proved by `sorry`, before
    a final `end` of the candidate's namespace; returns (text, first line of the extras, [(line
    range, extra)])."""
    lines = text.rstrip("\n").split("\n")
    cut = len(lines)
    while cut and not lines[cut - 1].strip():
        cut -= 1
    tail = []
    if cut and re.match(r"end\b", lines[cut - 1]):
        tail = lines[cut - 1:]
        lines = lines[:cut - 1]
    start = len(lines) + 1
    ranges = []
    for i, (src, name, stmt) in enumerate(extras):
        a = len(lines) + 1
        lines += f"theorem pfm_{'plan' if src == 'planner' else 'goal'}_{i}{stmt} := by\n  sorry\n".split("\n")
        ranges.append(((a, len(lines)), (src, name, f"pfm_{'plan' if src == 'planner' else 'goal'}_{i}")))
    return "\n".join(lines + tail) + "\n", start, ranges


def with_import(text, mod="ProofForgeFin"):
    if re.search(rf"^import {re.escape(mod)}\s*$", text, re.M):
        return text
    return harvest.add_import(text, mod)


def measure_open(results, which, base, new=None, log=print, only=None, include_extras=True):
    """Open goals of the failed runs of one set closed by the battery, with the library at
    `base` and (if given) at `new`. Every obligation is a `sorry` or a failing theorem of the
    final candidate, or a planner lemma or unsolved goal of the run that elaborates in the
    candidate's context."""
    import shutil
    split = load_split()
    harvest.SITE_TACTICS[:] = TACTICS
    rs, failed, goals = collect_goals(results, which, split)
    by_run = collections.defaultdict(list)
    for g in goals:
        by_run[g["run"]].append(g)
    cands = []
    for i, r in enumerate(failed):
        if not r["final"]:
            continue
        c = {"id": f"{'m' if which == 'mining' else 'h'}{i:03d}", "task": r["task"], "run": r["run"],
             "file": r["final"], "evidence": r["evidence"]}
        if only is None or c["id"] in only:
            cands.append(c)
    parent = harvest.WORK / f"open-{which}"
    shutil.rmtree(parent, ignore_errors=True)
    parent.mkdir(parents=True)
    with harvest.limited():
        base_pkg = fin_lib.ensure_built(base) / fin_lib.VENDOR
        new_pkg = fin_lib.ensure_built(new) / fin_lib.VENDOR if new else None
    for c in cands:
        d = harvest.measure_project(parent, c)
        text0 = pathlib.Path(c["file"]).read_text(errors="replace")
        extras = extras_of(by_run[c["run"]]) if include_extras else []
        text1, start, ranges = augment(text0, extras)
        c.update(extras_start=start, extras=[{"range": list(rg), "source": x[0], "name": x[1], "theorem": x[2]}
                                             for rg, x in ranges])
        (d / "candidate/Solution.lean").write_text(text1)
        harvest.link_tree(base_pkg, d / fin_lib.VENDOR)
        fin_lib.add_require(d)
    log(f"{which}: {len(cands)} failed runs with a final candidate")
    harvest.compile_all(parent, cands, lambda c: (
        f"lake build {taskmod.load(c['task']).lib} > build.log 2>&1; "
        "lake env lean -DmaxErrors=1000000 --json candidate/Solution.lean > judged.jsonl 2> judged.err"), 3600, log)
    ready = []
    for c in cands:
        d = parent / c["id"]
        if not (d / ".done").is_file():
            c["skipped"] = "the candidate did not compile within the time limit"
            continue
        text1 = (d / "candidate/Solution.lean").read_text()
        msgs = harvest.read_messages(d / "judged.jsonl")
        keep, dropped = [], []
        for x in c["extras"]:
            a, b = x["range"]
            errs = [m for m in msgs if m["severity"] == "error" and a <= m["pos"]["line"] <= b]
            (dropped if errs else keep).append(x)
            if errs:
                x["not_elaborated"] = errs[0]["data"][:200]
        lines = text1.split("\n")
        drop_lines = {ln for x in dropped for ln in range(x["range"][0], x["range"][1] + 1)}
        text2 = "\n".join(l for i, l in enumerate(lines, 1) if i not in drop_lines)
        orig = [m for m in msgs if m["pos"]["line"] < c["extras_start"]]
        failing, outside = harvest.failing_theorems(text2, orig)
        if outside:
            c["skipped"] = f"errors outside every theorem: {outside[0][:160]}"
            continue
        failing = [f for f in failing if not f[0].startswith("pfm_")]
        obs = harvest.battery_text(text2, failing)[1]
        for o in obs:
            th = o.get("theorem") or ""
            o["origin"] = ("planner" if th.startswith("pfm_plan_") else "unsolved" if th.startswith("pfm_goal_")
                           else "final")
            if o["origin"] != "final":
                x = next(x for x in keep if x["theorem"] == th)
                o["source_name"] = x["name"]
        c["obligations"] = obs
        if not obs:
            continue
        c["groups"] = harvest.batches([o["k"] for o in obs], harvest.GROUP)
        for j, ks in enumerate(c["groups"]):
            for name, tactics in (("Battery", TACTICS), ("NewBattery", TACTICS + NEW_TACTICS)):
                if name == "NewBattery" and not new_pkg:
                    continue
                harvest.SITE_TACTICS[:] = tactics
                t, _ = harvest.battery_text(text2, failing, set(ks))
                (d / f"{name}{j}.lean").write_text(t.replace("import ProofForgeFin\n", "", 1)
                                                   if t.count("import ProofForgeFin\n") > 1 else t)
            harvest.SITE_TACTICS[:] = TACTICS
        if new_pkg:
            harvest.link_tree(new_pkg, d / ".pfnew")
        (d / ".done").unlink()
        ready.append(c)
    log(f"{len(ready)} candidates with open obligations, {sum(len(c['obligations']) for c in ready)} obligations")

    def runs_of(c, tag):
        b = "NewBattery" if tag == "new" else "Battery"
        return "; ".join(f"{harvest.LEAN_BATTERY.replace('candidate/Solution.lean', f'{b}{j}.lean')} > {tag}{j}.jsonl "
                         f"2> {tag}{j}.err; echo $? > {tag}{j}.rc" for j in range(len(c["groups"])))
    tags = ["base"] + (["new"] if new_pkg else [])
    harvest.compile_all(parent, ready, lambda c: (
        runs_of(c, "base") + (f"; rm -rf {fin_lib.VENDOR} && mv .pfnew {fin_lib.VENDOR} && {runs_of(c, 'new')}"
                              if new_pkg else "")), 4 * 3600, log, chunk=4)
    for c in ready:
        d = parent / c["id"]
        for j, ks in enumerate(c["groups"]):
            group = [o for o in c["obligations"] if o["k"] in ks]
            for tag in tags:
                btext = (d / f"{'NewBattery' if tag == 'new' else 'Battery'}{j}.lean").read_text()
                ms = harvest.read_messages(d / f"{tag}{j}.jsonl")
                res = harvest.read_sites(ms, group)
                rc = d / f"{tag}{j}.rc"
                for o in group:
                    k = o["k"]
                    line = next((i + 1 for i, l in enumerate(btext.split("\n")) if f'"PFH_CLOSED_{k}"' in l), o["line"])
                    o[tag] = res[k]
                    o[f"{tag}_exit"] = int(rc.read_text().strip()) if rc.is_file() and rc.read_text().strip() else None
                    if res[k] == "closed":
                        o[f"{tag}_by"] = (harvest.try_this(ms, line) or ["a battery tactic"])[0]
        c["finished"] = (d / ".done").is_file()
        c.pop("groups")
    return cands


def sorry_goals(parent, cands, log=print):
    """The goal at every `sorry` of each prepared candidate (parent/<id>, as `measure_open` left
    it): each `sorry` is replaced by `trace_state` before it, the candidate compiled with the
    vendored library; returns {candidate id: [{"line", "theorem", "goal"}]}."""
    ready = []
    for c in cands:
        d = parent / c["id"]
        f = d / "candidate/Solution.lean"
        if not f.is_file():
            continue
        text = f.read_text()
        sites = harvest.sorry_sites(text)
        out = text
        for pos in sorted(sites, reverse=True):
            kind = harvest.site_kind(text, pos)
            rep = "(trace_state; sorry)" if kind == "tactic" else "(by trace_state; sorry)"
            out = out[:pos] + rep + out[pos + len("sorry"):]
        (d / "Goals.lean").write_text(out)
        c["_sites"] = [(pos, text.count("\n", 0, pos) + 1) for pos in sites]
        ready.append(c)
    harvest.compile_all(parent, ready, lambda c: (
        "lake env lean -DmaxErrors=1000000 --json Goals.lean > goals.jsonl 2> goals.err"), 3600, log)
    res = {}
    for c in ready:
        d = parent / c["id"]
        text = (d / "Goals.lean").read_text()
        spans = harvest.theorem_spans(text)
        msgs = harvest.read_messages(d / "goals.jsonl")
        out = []
        for m in msgs:
            if m["severity"] == "information" and ("⊢" in m["data"]):
                line = m["pos"]["line"]
                th = next((sp[0] for sp in spans if sp[3] <= line < sp[4]), None)
                out.append({"line": line, "theorem": th, "goal": m["data"][:6000]})
        res[c["id"]] = out
        c.pop("_sites", None)
    return res


def measure_reprove(results, which, base, new, log=print, min_chars=100, only=None):
    """Proofs of accepted runs re-proved by the battery: every theorem of an accepted run's final
    candidate other than the required ones, with a proof of at least `min_chars` characters
    other than whitespace, one per distinct statement of a task; its proof is replaced by the
    battery (the other theorems keep theirs), with the library at `base` and at `new` (the new
    battery adds `lib_defs`). Returns the candidates with per-theorem results and sizes."""
    import shutil
    split = load_split()
    rs = [r for r in runs(results) if task_set(r["task"], split) == which and r["outcome"] == "accepted" and r["final"]]
    seen, cands = set(), []
    for i, r in enumerate(rs):
        try:
            req = set(taskmod.load(r["task"]).theorems)
        except FileNotFoundError:
            continue
        text = pathlib.Path(r["final"]).read_text(errors="replace")
        if harvest.sorry_sites(text):
            continue
        parsed = {t["name"]: t for t in harvest.parse(text)["theorems"]}
        pick = []
        for sp in harvest.theorem_spans(text):
            th = parsed.get(sp[0])
            if not th or sp[0].split(".")[-1] in req:
                continue
            key = (r["task"], re.sub(r"\s+", " ", th["statement"]).strip())
            if key in seen or harvest.size(th["proof"])["chars"] < min_chars:
                continue
            seen.add(key)
            pick.append({"theorem": sp[0], "proof_chars": harvest.size(th["proof"])["chars"],
                         "proof_lines": harvest.size(th["proof"])["lines"]})
        if pick:
            c = {"id": f"{'v' if which == 'held-out' else 'w'}{i:03d}", "task": r["task"], "run": r["run"],
                 "file": r["final"], "theorems": pick}
            if only is None or c["id"] in only:
                cands.append(c)
    parent = harvest.WORK / f"reprove-{which}"
    shutil.rmtree(parent, ignore_errors=True)
    parent.mkdir(parents=True)
    with harvest.limited():
        base_pkg = fin_lib.ensure_built(base) / fin_lib.VENDOR
        new_pkg = fin_lib.ensure_built(new) / fin_lib.VENDOR
    log(f"{which}: {len(cands)} accepted candidates, {sum(len(c['theorems']) for c in cands)} proofs to re-prove")
    for c in cands:
        d = harvest.measure_project(parent, c)
        text = pathlib.Path(c["file"]).read_text(errors="replace")
        names = {t["theorem"] for t in c["theorems"]}
        failing = [sp for sp in harvest.theorem_spans(text) if sp[0] in names]
        obs = harvest.battery_text(text, failing)[1]
        by_name = {t["theorem"]: t for t in c["theorems"]}
        for o in obs:
            o.update(by_name.get(o["theorem"], {}))
        c["obligations"] = [o for o in obs if o["kind"] == "failing theorem"]
        c["groups"] = harvest.batches([o["k"] for o in c["obligations"]], harvest.GROUP)
        for j, ks in enumerate(c["groups"]):
            for name, tactics in (("Battery", TACTICS), ("NewBattery", TACTICS + NEW_TACTICS)):
                harvest.SITE_TACTICS[:] = tactics
                t, _ = harvest.battery_text(text, failing, set(ks))
                (d / f"{name}{j}.lean").write_text(t.replace("import ProofForgeFin\n", "", 1)
                                                   if t.count("import ProofForgeFin\n") > 1 else t)
            harvest.SITE_TACTICS[:] = TACTICS
        harvest.link_tree(base_pkg, d / fin_lib.VENDOR)
        fin_lib.add_require(d)
        harvest.link_tree(new_pkg, d / ".pfnew")

    def runs_of(c, tag):
        b = "NewBattery" if tag == "new" else "Battery"
        return "; ".join(f"{harvest.LEAN_BATTERY.replace('candidate/Solution.lean', f'{b}{j}.lean')} > {tag}{j}.jsonl "
                         f"2> {tag}{j}.err; echo $? > {tag}{j}.rc" for j in range(len(c["groups"])))
    harvest.compile_all(parent, cands, lambda c: (
        f"lake build {taskmod.load(c['task']).lib} > build.log 2>&1; {runs_of(c, 'base')}; "
        f"rm -rf {fin_lib.VENDOR} && mv .pfnew {fin_lib.VENDOR} && {runs_of(c, 'new')}"), 4 * 3600, log, chunk=4)
    for c in cands:
        d = parent / c["id"]
        for j, ks in enumerate(c["groups"]):
            group = [o for o in c["obligations"] if o["k"] in ks]
            for tag in ("base", "new"):
                btext = (d / f"{'NewBattery' if tag == 'new' else 'Battery'}{j}.lean").read_text()
                ms = harvest.read_messages(d / f"{tag}{j}.jsonl")
                res = harvest.read_sites(ms, group)
                for o in group:
                    k = o["k"]
                    line = next((i + 1 for i, l in enumerate(btext.split("\n")) if f'"PFH_CLOSED_{k}"' in l), o["line"])
                    o[tag] = res[k]
                    if res[k] == "closed":
                        o[f"{tag}_by"] = (harvest.try_this(ms, line) or ["a battery tactic"])[0]
        c["finished"] = (d / ".done").is_file()
        c.pop("groups")
    return cands


def summarize_reprove(cands):
    obs = [o for c in cands for o in c.get("obligations", [])]

    def repl_chars(o, tag):
        by = o.get(f"{tag}_by") or ""
        return len(re.sub(r"\s", "", "exact " + by)) if by and by != "a battery tactic" else 12
    only_new = [o for o in obs if o.get("new") == "closed" and o.get("base") != "closed"]
    both = [o for o in obs if o.get("new") == "closed" and o.get("base") == "closed"]
    return {"candidates": len(cands), "proofs": len(obs),
            "closed_base": sum(o.get("base") == "closed" for o in obs),
            "closed_new": sum(o.get("new") == "closed" for o in obs),
            "closed_only_new": len(only_new), "closed_only_base": sum(o.get("base") == "closed" and o.get("new") != "closed" for o in obs),
            "not_reached": sum("not reached" in (o.get("base"), o.get("new")) for o in obs),
            "only_new_proof_chars": sum(o["proof_chars"] for o in only_new),
            "only_new_replacement_chars": sum(repl_chars(o, "new") for o in only_new),
            "both_proof_chars": sum(o["proof_chars"] for o in both),
            "both_base_replacement_chars": sum(repl_chars(o, "base") for o in both),
            "both_new_replacement_chars": sum(repl_chars(o, "new") for o in both)}


def summarize_open(cands, tags=("base", "new")):
    obs = [(c, o) for c in cands for o in c.get("obligations", [])]
    out = {"candidates": len(cands), "skipped": sum("skipped" in c for c in cands),
           "extras_not_elaborated": sum(1 for c in cands for x in c.get("extras", []) if "not_elaborated" in x),
           "obligations": len(obs), "by_origin": dict(collections.Counter(o["origin"] for _, o in obs))}
    for t in tags:
        out[f"closed_{t}"] = sum(o.get(t) == "closed" for _, o in obs)
    if "new" in tags:
        out["closed_only_new"] = sum(o.get("new") == "closed" and o.get("base") != "closed" for _, o in obs)
        out["closed_only_base"] = sum(o.get("base") == "closed" and o.get("new") != "closed" for _, o in obs)
    out["not_reached"] = sum(any(o.get(t) == "not reached" for t in tags) for _, o in obs)
    return out


NEW_MODULES = ["ProofForgeFin.Sums.Eqns", "ProofForgeFin.Sums.Index", "ProofForgeFin.Sums.Update",
               "ProofForgeFin.Sums.Floor", "ProofForgeFin.Accrual", "ProofForgeFin.Tactic.LibDefs"]


def lemma_list(root=None):
    """The theorems and tactics this work adds, by module, with their statements and doc strings
    (read from the sources)."""
    out = []
    for m in NEW_MODULES:
        text = fin_lib.module_file(m, root).read_text()
        ns = re.search(r"^namespace (\S+)", text, re.M)
        for th in re.finditer(r"(/--((?:(?!-/).)*)-/\s*\n)?theorem (\S+)(.*?)(?=:=|\n  \|)", text, re.S):
            out.append({"module": m, "kind": "theorem", "name": f"{ns.group(1)}.{th.group(3)}" if ns else th.group(3),
                        "statement": re.sub(r"\s+", " ", th.group(4)).strip(),
                        "doc": re.sub(r"\s+", " ", th.group(2) or "").strip()})
        for syn in re.finditer(r'^syntax \(name := \w+\) "([^"]+)"', text, re.M):
            out.append({"module": m, "kind": "tactic", "name": syn.group(1)})
    return out

if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    a1 = sub.add_parser("runs")
    a1.add_argument("--results", default=str(ROOT / "results"))
    a2 = sub.add_parser("goals")
    a2.add_argument("--set", required=True, choices=["mining", "held-out"])
    a2.add_argument("--results", default=str(ROOT / "results"))
    a2.add_argument("--out")
    a3 = sub.add_parser("clusters")
    a3.add_argument("goals")
    a4 = sub.add_parser("open")
    a4.add_argument("--set", required=True, choices=["mining", "held-out"])
    a4.add_argument("--results", default=str(ROOT / "results"))
    a4.add_argument("--base", required=True, help="library sources before (a lib/ directory)")
    a4.add_argument("--new", help="library sources after")
    a4.add_argument("--only", nargs="*")
    a4.add_argument("--out", required=True)
    sub.add_parser("lemmas")
    sub.add_parser("kernels", help="six kernels, leanchecker and the axiom audit on the whole library and the "
                                   "demonstrations; writes results/feedback-library-1/kernels-full.json")
    a5 = sub.add_parser("reprove")
    a5.add_argument("--set", required=True, choices=["mining", "held-out"])
    a5.add_argument("--results", default=str(ROOT / "results"))
    a5.add_argument("--base", required=True)
    a5.add_argument("--new", required=True)
    a5.add_argument("--min-chars", type=int, default=100)
    a5.add_argument("--only", nargs="*")
    a5.add_argument("--out", required=True)
    a = ap.parse_args()
    split = load_split()
    if a.cmd == "runs":
        rs = runs(a.results)
        c = collections.Counter((task_set(r["task"], split), r["outcome"]) for r in rs)
        print(json.dumps({f"{k[0]}/{k[1]}": v for k, v in sorted(c.items(), key=str)}, indent=1))
    elif a.cmd == "goals":
        rs, failed, goals = collect_goals(a.results, a.set, split)
        out = pathlib.Path(a.out or OUT / f"goals-{a.set}.jsonl")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text("".join(json.dumps(g, ensure_ascii=False) + "\n" for g in goals))
        print(json.dumps({"set": a.set, "runs": len(rs), "failed_runs": len(failed), "goals": len(goals),
                          "by_source": dict(collections.Counter(g["source"] for g in goals)),
                          "by_kind": dict(collections.Counter(g["kind"] for g in goals))}, indent=1))
    elif a.cmd == "clusters":
        goals = [json.loads(l) for l in pathlib.Path(a.goals).read_text().splitlines() if l.strip()]
        print(json.dumps(clusters(goals, split), indent=1))
    elif a.cmd == "open":
        cands = measure_open(a.results, a.set, a.base, a.new, only=a.only)
        tags = ("base", "new") if a.new else ("base",)
        rec = {"set": a.set, "base_sha256": fin_lib.tree_sha256(a.base),
               "new_sha256": fin_lib.tree_sha256(a.new) if a.new else None, "battery": TACTICS + ["exact?"],
               "new_battery": TACTICS + NEW_TACTICS + ["exact?"] if a.new else None,
               "summary": summarize_open(cands, tags), "candidates": cands}
        pathlib.Path(a.out).write_text(json.dumps(rec, indent=1, ensure_ascii=False) + "\n")
        print(json.dumps(rec["summary"], indent=1))
    elif a.cmd == "kernels":
        harvest.OUT = OUT
        sys.exit(0 if harvest.kernels(full=True)["passed"] else 1)
    elif a.cmd == "lemmas":
        ls = lemma_list()
        (OUT / "lemmas.json").write_text(json.dumps({"modules": NEW_MODULES, "count": collections.Counter(
            x["kind"] for x in ls), "declarations": ls}, indent=1, ensure_ascii=False) + "\n")
        print(collections.Counter(x["module"] for x in ls))
    elif a.cmd == "reprove":
        cands = measure_reprove(a.results, a.set, a.base, a.new, min_chars=a.min_chars, only=a.only)
        rec = {"set": a.set, "base_sha256": fin_lib.tree_sha256(a.base), "new_sha256": fin_lib.tree_sha256(a.new),
               "battery": TACTICS + ["exact?"], "new_battery": TACTICS + NEW_TACTICS + ["exact?"],
               "min_chars": a.min_chars, "summary": summarize_reprove(cands), "candidates": cands}
        pathlib.Path(a.out).write_text(json.dumps(rec, indent=1, ensure_ascii=False) + "\n")
        print(json.dumps(rec["summary"], indent=1))
