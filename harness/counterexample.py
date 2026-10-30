#!/usr/bin/env python3
"""Counterexample stage: turn a failing property case into a refutation checked by the kernel.

The binary check (binary_check.py) reports that the rebuilt executable violated requirement R on
a concrete input. This stage turns that report into a Lean theorem

    theorem <ns>.cex_<req_theorem> : ¬ (<locked statement of R>)

about the candidate's own definitions, and checks it in a fresh container with the judge's
kernel checks: `lake comparator --paranoid` (Lean's default and paranoid kernels, lean4lean,
nanoda, con-leche, con-ron) against a challenge generated from the locked challenge, then
`leanchecker`, then `#print axioms`. A REFUTED requirement then carries a disproof checked by
the kernel, not only a failing test of the executable.

Trust. The statement is never written by an adapter. It is the locked challenge's statement of
R, negated, and the comparator challenge for it is the locked `Challenge.lean` itself with the
negated theorem appended (holes unchanged), so Comparator checks that the theorem proves exactly
`¬ R` about the solution's definition of each hole. Everything an adapter supplies (the Lean
terms for the concrete input, proof hints, helper declarations) only has to make the proof go
through; a wrong term makes the check fail, it cannot make a false refutation pass. The executable
and its JSON wrapper are not trusted here at all: the kernel evaluates the candidate's definitions
on the instance, so a refutation holds even where the wrapper misreports.

Adapters. How a JSON case becomes Lean terms depends on the task's types, so each task may
provide an optional adapter, a Python file with

    def instance(task, requirement, case, out, origin=None) -> dict | None

(`origin` is passed only for a witness found on a follow-up case: the round-1 case and output
it was derived from), looked up as `<task dir>/counterexample.py`, then
`counterexamples/<task id>.py`, then `counterexamples/<base id>.py` (the task id without its
`-bN` variant suffix; variants share a specification). The registry directory keeps existing task directories, whose files are frozen by
validation receipts and the test freeze, unchanged. `instance` returns None when it cannot handle
the case, or a dict with:

  args      Lean terms for the leading arguments of the requirement, in binder order. `_` lets
            unification find a binder; `?` is a hypothesis the stage discharges with
            `decide`, `Option.some_get` (for `f x = some y` with `y` left as `_`), `rfl` or one
            of the `hints`.
  hints     proof terms tried for `?` hypotheses that are not decidable (for example a lemma
            that a parameter is well behaved).
  observe   Lean functions applied to both sides when the instantiated conclusion is an
            equation whose type has no decidable equality (a state with function fields); the
            stage refutes the equation of the values of one of them, tried in turn.
  preamble  Lean declarations placed before the theorem (instances, helper lemmas).
  imports   further modules of the task's specification library to import.
  proof     a complete tactic proof, used instead of the default one.
  note      one sentence describing the instance.

The default proof instantiates the requirement and decides the rest by kernel evaluation:

    intro h
    have hx := h <args>
    revert hx
    first | decide | decide +kernel

with fallbacks that unfold the specification's propositions, refute one part of a conjunction,
or refute the equation of one observed value (`congrArg <observe_i> hx`).

Usage: counterexample.py <candidate.lean | workspace> --task T [--cases N] [--seed S] [--json out]
(runs the binary check, then this stage on each refuted requirement).
"""
import argparse, hashlib, importlib.util, json, pathlib, re, shutil, sys, threading

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import judge, task as taskmod  # noqa: E402

ROOT = taskmod.ROOT
REGISTRY = ROOT / "counterexamples"
PERMITTED = ["Classical.choice", "Quot.sound", "propext"]
# Adapter text is not trusted; this is defense in depth (Comparator's axiom check is the
# authority). `set_option` is allowed: the stage itself raises recursion and heartbeat limits.
FORBIDDEN = [p for p in judge.FORBIDDEN if p != r"\bset_option\b"]
OPTIONS = "set_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\n"
_LOCK = threading.Lock()
_ADAPTERS = {}


def sha256_text(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def base_id(task_id: str) -> str:
    parts = task_id.rsplit("-", 1)
    return parts[0] if len(parts) == 2 and parts[1][:1] == "b" and parts[1][1:].isdigit() else task_id


def adapter_path(task):
    local = task.root / "counterexample.py"
    if local.is_file():
        return local
    for name in (task.id, base_id(task.id)):
        p = REGISTRY / f"{name}.py"
        if p.is_file():
            return p
    return None


def adapter(task):
    path = adapter_path(task)
    if path is None:
        return None, None
    with _LOCK:
        if path not in _ADAPTERS:
            spec = importlib.util.spec_from_file_location(f"cex_adapter_{abs(hash(str(path)))}", path)
            mod = importlib.util.module_from_spec(spec)
            flag, sys.dont_write_bytecode = sys.dont_write_bytecode, True
            try:
                spec.loader.exec_module(mod)
            finally:
                sys.dont_write_bytecode = flag
            _ADAPTERS[path] = mod
    return _ADAPTERS[path], path


# Lean term renderers for adapters.

def nat(x) -> str:
    if not isinstance(x, int) or isinstance(x, bool) or x < 0:
        raise ValueError(f"not a natural number: {x!r}")
    return str(x)


def int_(x) -> str:
    if not isinstance(x, int) or isinstance(x, bool):
        raise ValueError(f"not an integer: {x!r}")
    return f"({x} : Int)" if x >= 0 else f"(-{-x} : Int)"


def boolean(x) -> str:
    if not isinstance(x, bool):
        raise ValueError(f"not a Bool: {x!r}")
    return "true" if x else "false"


def lst(items, ty=None) -> str:
    body = "[" + ", ".join(items) + "]"
    return f"({body} : List {ty})" if ty else body


def table(values, default, ty=None) -> str:
    """A function `Nat → α` that maps i to values[i] and every other index to `default`."""
    return f"(fun i => {lst(values, ty)}.getD i {default})"


def struct(fields: dict, ty=None) -> str:
    body = "{ " + ", ".join(f"{k} := {v}" for k, v in fields.items()) + " }"
    return f"({body} : {ty})" if ty else body


def string(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


# Generation.

def challenge_text(task):
    return (task.root / task.spec_dir / "Challenge.lean").read_text()


def locked_statement(task, theorem):
    m = re.search(rf"^theorem\s+{re.escape(theorem)}\s*:\s*(.*?)\s*:= sorry$", challenge_text(task), re.M)
    return m.group(1) if m else None


def negation(stmt):
    return f"¬ ({stmt})"


def cex_name(theorem):
    return f"cex_{theorem}"


def challenge_source(task, theorem, stmt):
    """The locked challenge, unchanged, with the negated requirement appended."""
    return (challenge_text(task).rstrip("\n") + "\n\n/-! Appended by harness/counterexample.py: the negation of the "
            f"locked requirement `{theorem}`. -/\nnamespace {task.ns}\n\n"
            f"theorem {cex_name(theorem)} : {negation(stmt)} := sorry\n\nend {task.ns}\n")


def imports_of(text):
    return re.findall(r"^import\s+(\S+)", text, re.M)


def _scan(text):
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)
    code = re.sub(r"--[^\n]*", "", code)
    return [m.group(0) for pat in FORBIDDEN for m in re.finditer(pat, code)]


def _comment(s):
    return s.replace("-/", "- /").replace("/-", "/ -")


def prop_defs(task):
    """Names of the specification's `Prop`-valued definitions. A definition without a
    `Decidable` instance blocks `decide`; unfolding it exposes a decidable body."""
    names = []
    for f in sorted((task.root / task.spec_dir).glob("*.lean")):
        if f.name == "Challenge.lean":
            continue
        code = re.sub(r"/-.*?-/", "", f.read_text(), flags=re.S)
        for m in re.finditer(r"^(?:def|abbrev)\s+([\w.]+)", code, re.M):
            head = re.split(r":=|\n\s*\|", code[m.end():], maxsplit=1)[0]
            if re.search(r"(:|→)\s*Prop\s*$", head) and m.group(1) not in names:
                names.append(m.group(1))
    return names


def discharger(hints, unfold):
    alts = ["decide", "exact (Option.some_get (by decide)).symm", "rfl"] + [f"exact ({h})" for h in hints]
    if unfold:
        alts.append(f"(simp -failIfUnchanged only [{unfold}] <;> decide)")
    return "(by first | " + " | ".join(alts) + ")"


def observing(eq, fns):
    """Tactic alternatives refuting the equation `eq` through one of the observations `fns`. One
    observation per alternative keeps each `Decidable` instance small."""
    return "first\n" + "\n".join(
        f"  | (have hy := congrArg ({f}) ({eq}); revert hy; first | decide | decide +kernel)" for f in fns)


def default_proof(inst, props=()):
    hints = inst.get("hints") or []
    unfold = ", ".join(props)
    args = " ".join(discharger(hints, unfold) if a == "?" else (a if a == "_" else f"({a})")
                    for a in inst.get("args") or [])
    app = f"h {args}".rstrip()
    obs = inst.get("observe")
    if obs:
        obs = [obs] if isinstance(obs, str) else list(obs)
        return "\n".join("  " + l for l in ["intro h", f"have hx := {app}"] + observing("hx", obs).splitlines())
    lines = ["intro h", f"have hx := {app}"]
    # Decide the instantiated statement, unfolding the specification's propositions when one
    # has no Decidable instance; when it is a conjunction with a part that is not decidable (for
    # example a frame condition over every account), refute one decidable part.
    lines += ["first",
              "  | (revert hx; decide)",
              "  | (revert hx; decide +kernel)"]
    if unfold:
        lines += [f"  | (simp -failIfUnchanged only [{unfold}] at hx <;> (revert hx; decide))"]
    lines += ["  | (repeat (first | exact absurd hx (by decide) | exact absurd hx.1 (by decide) "
              "| replace hx := hx.2); done)"]
    return "\n".join("  " + l for l in lines)


def solution_source(task, theorem, stmt, inst, requirement, case):
    imports = ["Solution"] + [m for m in imports_of(challenge_text(task)) if m != "Solution"]
    for m in inst.get("imports") or []:
        if not m.startswith(f"{task.lib}.") or not re.fullmatch(r"[A-Za-z0-9_.]+", m):
            raise ValueError(f"adapter import outside the specification library: {m}")
        if m not in imports:
            imports.append(m)
    proof = inst.get("proof")
    proof = ("\n".join("  " + l if l.strip() else l for l in proof.strip("\n").splitlines())) if proof \
        else default_proof(inst, prop_defs(task))
    head = "".join(f"import {m}\n" for m in imports)
    doc = (f"/-!\nGenerated by harness/counterexample.py. Refutes `{task.ns}.{theorem}` ({requirement}) for the "
           f"candidate's definitions\non the failing case\n\n{_comment(json.dumps(case, sort_keys=True))}\n"
           + (f"\n{_comment(inst['note'])}\n" if inst.get("note") else "") + "-/\n")
    pre = (inst.get("preamble") or "").strip("\n")
    body = (f"namespace {task.ns}\n\n" + (pre + "\n\n" if pre else "")
            + f"theorem {cex_name(theorem)} : {negation(stmt)} := by\n{proof}\n\nend {task.ns}\n")
    obs = inst.get("observe") or []
    adapter_text = " ".join([pre, proof] + list(inst.get("args") or []) + list(inst.get("hints") or [])
                            + ([obs] if isinstance(obs, str) else list(obs)))
    bad = _scan(adapter_text)
    if bad:
        raise ValueError(f"forbidden construct in adapter output: {sorted(set(bad))}")
    return head + "\n" + doc + "\n" + OPTIONS + "\n" + body


def theorem_of(task, rid):
    return dict(task.requirements).get(rid)


def generate(task, witness):
    """A counterexample item for one witness: the Lean sources, or a reason why there are none."""
    rid = witness["requirement"]
    th = theorem_of(task, rid)
    item = {"requirement": rid, "input": witness.get("input"), "output": witness.get("output"),
            "message": witness.get("message")}
    if witness.get("origin"):
        item["origin"] = witness["origin"]
    if th is None:
        return {**item, "reason": "not a requirement of the task"}
    stmt = locked_statement(task, th)
    item.update(refutes=f"{task.ns}.{th}", theorem=f"{task.ns}.{cex_name(th)}",
                statement=negation(stmt) if stmt else None)
    mod, path = adapter(task)
    if mod is None:
        return {**item, "reason": "the task has no counterexample adapter"}
    item["adapter"] = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)
    item["adapter_sha256"] = taskmod.sha256(path)
    try:
        kw = {"origin": witness["origin"]} if witness.get("origin") else {}
        inst = mod.instance(task, rid, witness.get("input"), witness.get("output"), **kw)
    except Exception as e:  # an adapter failure is a missing counterexample, never a verdict
        return {**item, "reason": f"adapter error: {type(e).__name__}: {e}"}
    if not inst:
        return {**item, "reason": "the adapter has no instance for this case"}
    try:
        item["lean_source"] = solution_source(task, th, stmt, inst, rid, witness.get("input"))
    except ValueError as e:
        return {**item, "reason": str(e)}
    item["note"] = inst.get("note")
    return item


# Checking.

def _axioms(output, name):
    m = re.search(rf"'{re.escape(name)}' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
    return None if not m else sorted(x.strip() for x in (m.group(2) or "").replace("\n", " ").split(",") if x.strip())


def _record(r):
    return None if r is None else {k: r[k] for k in ("command", "exit_code", "elapsed_ms", "stdout_sha256", "stderr_sha256") if k in r}


def _errors(tail):
    lines = [l.strip() for l in tail.splitlines()]
    errs = [l for l in lines if re.search(r"\.lean:\d+:\d+: error", l)] or [l for l in lines if "error" in l.lower()]
    return errs[0][:400] if errs else tail.strip()[-400:]


def check_items(task, candidate, items, timeout=1800):
    """Check the items that carry `lean_source` against the candidate, each in its own module and
    with its own Comparator run. Returns the items with their results."""
    todo = [it for it in items if it.get("lean_source") and it.get("statement")]
    for it in items:
        it.setdefault("kernel_checked", False)
    if not todo:
        return items
    ws = judge.load_workspace(str(candidate))
    files = judge.candidate_files(ws)
    project = judge.fresh_project(ws, files, task)
    try:
        cex = project / "cex" / "Cex"
        cex.mkdir(parents=True)
        roots = []
        for k, it in enumerate(todo):
            th = it["refutes"].split(".")[-1]
            ch = challenge_source(task, th, locked_statement(task, th))
            it["challenge_sha256"] = sha256_text(ch)
            it["lean_file_sha256"] = sha256_text(it["lean_source"])
            it["statement_sha256"] = sha256_text(it["statement"])
            (cex / f"C{k}.lean").write_text(ch)
            (cex / f"S{k}.lean").write_text(it["lean_source"])
            (project / "cex" / f"c{k}.json").write_text(json.dumps({
                "challenge_module": f"Cex.C{k}", "solution_module": f"Cex.S{k}",
                "theorem_names": [it["theorem"]], "definition_names": [f"{task.ns}.{d}" for d in task.definitions],
                "permitted_axioms": PERMITTED}, indent=2) + "\n")
            (project / "cex" / f"A{k}.lean").write_text(f"import Cex.S{k}\n#print axioms {it['theorem']}\n")
            roots += [f"Cex.C{k}", f"Cex.S{k}"]
        with open(project / "lakefile.toml", "a") as f:
            f.write('\n# Added by harness/counterexample.py: generated refutations and their challenges.\n'
                    '[[lean_lib]]\nname = "Cex"\nsrcDir = "cex"\n'
                    f"roots = [{', '.join(json.dumps(r) for r in roots)}]\n")
        for k, it in enumerate(todo):
            b = judge.in_container(project, f"lake build Cex.S{k} > cex/b{k}.log 2>&1; rc=$?; head -c 6000 cex/b{k}.log; exit $rc",
                                   timeout=timeout)
            it["checks"] = {"build": _record(b)}
            if b["exit_code"] != 0:
                it["reason"] = ("time limit reached while building the refutation" if b["exit_code"] == 124
                                else f"refutation does not build: {_errors(b['output_tail'])}")
                continue
            c = judge.in_container(project, f"lake comparator --paranoid --config cex/c{k}.json", timeout=timeout)
            it["checks"]["comparator"] = _record(c)
            it["kernels"] = re.findall(r"^(.+?) kernel accepts the solution$", c["output_tail"], re.M)
            if c["exit_code"] != 0:
                it["reason"] = f"Comparator rejected the refutation: {_errors(c['output_tail'])}"
                continue
            lc = judge.in_container(project, f"lake env leanchecker Cex.S{k}", timeout=timeout)
            it["checks"]["leanchecker"] = _record(lc)
            if lc["exit_code"] != 0:
                it["reason"] = f"leanchecker exit {lc['exit_code']}"
                continue
            ax = judge.in_container(project, f"lake env lean cex/A{k}.lean", timeout=timeout)
            it["checks"]["axiom_audit"] = _record(ax)
            it["axioms"] = _axioms(ax["output_tail"], it["theorem"])
            if it["axioms"] is None or not set(it["axioms"]) <= set(PERMITTED):
                it["reason"] = f"axiom audit: {it['axioms']}"
                continue
            it["kernel_checked"] = True
            it["reason"] = None
    finally:
        shutil.rmtree(project, ignore_errors=True)
    return items


def witnesses_by_requirement(task, b):
    first = {}
    for w in b.get("witnesses") or []:
        first.setdefault(w["requirement"], w)
    return [first[rid] for rid, _ in task.requirements if rid in first and b.get("violations", {}).get(rid)]


ORDER = ["requirement", "refutes", "theorem", "statement", "statement_sha256", "kernel_checked", "reason",
         "kernels", "axioms", "input", "output", "origin", "message", "note", "adapter", "adapter_sha256",
         "challenge_sha256", "lean_file_sha256", "lean_source", "checks"]


def _ordered(it):
    return {k: it[k] for k in ORDER if k in it} | {k: v for k, v in it.items() if k not in ORDER}


def run(task, candidate, b, timeout=1800):
    """Counterexamples for every requirement the binary check refuted with a witness."""
    items = [generate(task, w) for w in witnesses_by_requirement(task, b)]
    check_items(task, candidate, items, timeout=timeout)
    return [_ordered(it) for it in items]


def recheck(task, candidate, recorded, timeout=1800):
    """Re-run the kernel checks on the Lean sources recorded in a Passport. The challenge and the
    statement are regenerated from the locked files, never taken from the Passport."""
    items = []
    for r in recorded:
        th = theorem_of(task, r.get("requirement"))
        stmt = locked_statement(task, th) if th else None
        it = {"requirement": r.get("requirement"), "refutes": f"{task.ns}.{th}" if th else None,
              "theorem": f"{task.ns}.{cex_name(th)}" if th else None,
              "statement": negation(stmt) if stmt else None}
        if r.get("lean_source") and th and stmt:
            it["lean_source"] = r["lean_source"]
        else:
            it["reason"] = r.get("reason") or "no Lean source recorded"
        items.append(it)
    return check_items(task, candidate, items, timeout=timeout)


if __name__ == "__main__":
    import binary_check  # noqa: E402
    ap = argparse.ArgumentParser()
    ap.add_argument("candidate")
    ap.add_argument("--task")
    ap.add_argument("--cases", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--json")
    a = ap.parse_args()
    t = taskmod.load(a.task)
    b = binary_check.check_binary(a.candidate, a.cases, a.seed, t)
    out = run(t, a.candidate, b)
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(out, indent=2) + "\n")
    for it in out:
        print(f"{it['requirement']:<28} {'KERNEL-CHECKED' if it['kernel_checked'] else 'not checked':<15} "
              f"{it.get('reason') or ', '.join(it.get('axioms') or []) or 'no axioms'}")
    sys.exit(0 if out and all(it["kernel_checked"] for it in out) else 1)
