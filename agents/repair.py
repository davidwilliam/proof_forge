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

Library (`--library on`, the default): the workspace has ProofForgeFin vendored (harness/fin_lib.py),
the system prompt gains a section generated from the library's declaration index (modules,
tactics, simp sets) with the rule that the candidate may import ProofForgeFin, the tools gain
`search_library` (retrieval over the index) and `add_import`, and each obligation's prompt lists
the library declarations the index ranks highest for it. `--library off` gives the harness
without the library. A0 (agents/baseline.py) never gets the library.

Loops: `--loop orchestrated` (default) fixes behavior first, then works obligation by obligation
in the task's listed order (phase 1), resolves what is left with planner decompositions (phase 2)
and spends the rest on whole-file repair (phase 3). `--loop free` is one tool dialog.
`--loop topdown` keeps phase 0 and phase 3 and replaces phases 1 and 2 by a structure phase (a
proof skeleton that derives every open required theorem from named helper theorems, accepted
only when Lean confirms that no required theorem uses `sorry` except through helpers) and a fill
phase (the open helpers, found from the compiled candidate's dependency graph, become the
obligations, shared helpers first); see topdown() and docs/ARCHITECTURE.md.

Attempt ledger: every run writes ledger.json (agents/ledger.py) into its run directory: the
declarations it proved, its skeletons and failure notes for the goals left open. `--resume-from
DIR[,DIR...]` starts from the best prior candidate (re-checked by Lean), carries the prior attempts'
proved declarations that still compile, works the goals they left open first and puts their failure
notes into the prompts for those goals. summary.json records the run directories in `resumed_from`.

Tactic portfolio (`--portfolio on`, the default; agents/portfolio.py): before the model spends a
turn on an open goal, a fixed list of Lean tactics is tried on it in one batch, and the first proof
that closes it is banked like a clean snippet. No dollars; the Lean time counts against the wall cap.

Goal tool (`--goal-tool on`, the default; agents/leanserver.py): a persistent Lean language server
per session gives the model `goal_at` (the proof state at each `sorry`, error or line of a
declaration) and answers a try_snippet with an error or a `sorry` from incremental elaboration,
without compiling the whole file again.

Refutation on concrete values (`--refute on`, the default; agents/refute.py): a planner lemma, a
skeleton helper or a helper the model states with `sorry` is evaluated on sampled instances (the
task's generator values first) before any turn is spent on it, and refused with the instance when
Lean's kernel accepts the refutation.

Parallel variants (`--variants K`, default 2, 0 for off; agents/variants.py): a goal still open
after its first dialog gets K short dialogs at once with different framings; the first that Lean
accepts is kept, the others stop; all are charged to the run's budget at list price.

Usage: repair.py [--task T] [--model muse-spark-1.3-contributor] [--planner muse-wonder-1.0|none]
                 [--mode repair|implement] [--loop orchestrated|free|topdown] [--library on|off]
                 [--budget-usd X] [--budget-wall S] [--out DIR] [--start FILE]
                 [--resume-from DIR[,DIR...]] [--portfolio on|off] [--goal-tool on|off]
                 [--refute on|off] [--variants K] [--variant-turns T]
"""
import argparse, hashlib, json, pathlib, re, shutil, sys, tempfile, threading, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "agents"))
sys.path.insert(0, str(ROOT / "harness"))
from meta_client import chat, APIError, DeadlineReached  # noqa: E402
from budget import Budget, BudgetExceeded, list_cost  # noqa: E402
import judge, binary_check, fin_lib, task as taskmod  # noqa: E402
import ledger, portfolio, leanserver, refute, variants  # noqa: E402

FORBIDDEN_TEXT = ("sorry, axiom, opaque, implemented_by, extern, unsafe, export, macro, elab, syntax, "
                  "initialize, #eval, run_cmd, native_decide, set_option")

# What may precede a declaration keyword on its first line: `open X in` (a snippet's `open`
# lines are banked that way, see Session._snippet_opens), attributes and modifiers.
DECL_PREFIX = (r"(?:open\s[^\n]*?\bin\s+)?(?:@\[[^\]]*\]\s*)?"
               r"(?:private\s+|protected\s+|noncomputable\s+)*")
DECL_KINDS = r"(?:theorem|lemma|def|instance|abbrev|structure|inductive)"
OPEN_IN = re.compile(r"^open\s[^\n]*?\bin\b")


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


# When to reach for each library tactic. The tactics themselves, their modules and their doc
# strings come from the generated index; a tactic without a line here is listed with the first
# sentence of its doc string only, and a line whose tactic is no longer in the index is dropped.
TACTIC_USE = {
    "struct_simp": "goals with projections of structure literals, projections of an `if`, updates read at a key "
                   "(`upd f k v j`) or constructor equations; pass the step's definitions, e.g. `struct_simp [step, upd, h]`",
    "step_cases": "a goal about one step of a model: splits on the operation and on every `if` and `match` in the step, "
                  "simplifies each branch and closes the refused ones; `step_cases op [step, f]`, or "
                  "`all_goals try step_cases` after another tactic",
    "run_induction": "a requirement over every sequence of operations (`Seq.run step s ops`, or a task's own `run` "
                     "after `run_induction [run_eq]`): one goal per operation constructor; `using J` for a stronger "
                     "invariant, `total Inv` for a ghost total such as COMP emitted so far",
    "fin_simp": "fixed-point and share conversions (`mulDown`, `divUp`, `previewRedeem`, `ceilDiv`, ...) put in "
                "`/` and `ceilDiv` normal form",
    "div_norm": "right before `omega` on goals with `ceilDiv` or division by literals or named literal scales",
    "round_bound": "rounding bounds on `Nat`: `x / d * d ≤ x`, `x ≤ ceilDiv x d * d`, `mulDown ≤ mulUp`, sums of "
                   "rounded parts, round trips",
    "generalize_divs": "goals whose quotients have variable divisors: replaces each quotient and remainder by a fresh "
                       "variable with its bounds, so `omega` can finish",
    "machine_norm": "state-machine goals over the `ProofForgeFin.Machine` models: reduces projections and the "
                    "`machine_simps` set in the goal and every hypothesis",
}


def _module_line(doc, n=170):
    """The opening of a module doc (its heading dropped): whole sentences up to `n` characters."""
    keep = [l for l in (doc or "").splitlines() if not l.lstrip().startswith(("#", "* ", "- "))]
    text = re.sub(r"\s+", " ", " ".join(keep).replace("**", "")).strip()
    if len(text) <= n:
        return text
    cut = text.rfind(". ", 0, n)
    return text[:cut + 1] if cut >= 60 else text[: n - 3] + "..."


REDUCTION_NOTE = (
    "- Reduction theorems: many library theorems have per-step or per-call hypotheses (one operation "
    "preserves an invariant, one call moves value between potentials by a bounded amount, a call's effect "
    "matches a specification) and conclude a statement about every sequence of operations or every reachable "
    "state. To prove a requirement over sequences, apply such a theorem and prove its per-step hypotheses for "
    "the implementation; requirements that are themselves per-call statements often supply them.")


def library_brief(index, tools=True):
    """The prompt section on ProofForgeFin, generated from the library's declaration index."""
    by_kind = {}
    for e in index.entries:
        by_kind.setdefault(e["kind"], []).append(e)
    mods = sorted(by_kind.get("module", []), key=lambda e: e["name"])
    lines = [
        "", "",
        "ProofForgeFin library (part of ProofForge; Lean 4 core only, every theorem proved with the permitted axioms):",
        "- candidate/Solution.lean may import ProofForgeFin modules in addition to the imports above: "
        "`import ProofForgeFin` for all of it, or one module such as `import ProofForgeFin.Rounding`. "
        "Imports go at the top of the file" + (
            "; add_import adds one and keeps it only if the file still compiles." if tools else "."),
        "- ProofForgeFinDemo is not importable. Library names are qualified (`ProofForgeFin.ceilDiv_spec`, "
        "`ProofForgeFin.Seq.run_invariant`); `open ProofForgeFin` shortens them. Library declarations you use are "
        "checked by the judge's kernels like your own.",
        "- Use the library's tactics; do not define tactics, macros, elaborators, syntax, simprocs or attributes "
        "yourself (the judge rejects them).",
        "- At a literal scale such as `10 ^ 36`, prove the arithmetic as a lemma over a variable scale and "
        "instantiate it: two of the judge's kernels unfold literal scales in equations that Lean's kernel accepts.",
    ]
    if tools:
        lines.append("- search_library finds library theorems, definitions and tactics by keywords, names or a "
                     "statement and returns each signature and doc string; search before proving a general fact "
                     "about rounding, shares, sequences of operations, ledgers or interest yourself.")
    lines.append(REDUCTION_NOTE + (" Search for one (search_library with words such as run, sequence, invariant, "
                                   "potential, bound, step) before proving a statement over sequences by hand."
                                   if tools else ""))
    lines.append("Modules:")
    lines += [f"- {e['name']}: {_module_line(e.get('doc'))}" for e in mods]
    tactics = sorted({e["name"]: e for e in reversed(by_kind.get("tactic", []))}.values(), key=lambda e: e["name"])
    if tactics:
        lines.append("Tactics (`import ProofForgeFin`, or the module named):")
        for e in tactics:
            use = TACTIC_USE.get(e["name"])
            lines.append(f"- `{e['name']}` ({e['module']}): " + (f"use for {use}." if use else fin_lib.short_doc(e.get("doc"), 200)))
    sets = sorted(by_kind.get("simp_set", []), key=lambda e: e["name"])
    if sets:
        lines.append("Simp sets (`simp only [fin_simp]` and so on): " + "; ".join(
            f"`{e['name']}`: {fin_lib.short_doc(e.get('doc'), 120)}" for e in sets))
    return "\n".join(lines)


# Most hits search_library returns in the top-down loop (each hit is a signature and a doc string
# that stays in the dialog for every later turn).
SEARCH_MAX_TOPDOWN = 10

TOPDOWN_TOOLS = [
    {"type": "function", "function": {"name": "submit_skeleton", "description": "Install a proof skeleton in candidate/Solution.lean: helper theorems (their proofs may be `sorry`), any definitions they need (complete bodies), and every unproved required theorem with exactly its statement and a proof that uses no `sorry` itself, only helper theorems. Kept only if the file compiles and Lean confirms that no required theorem uses `sorry` except through helper theorems; otherwise the file is unchanged and the reasons are returned.",
     "parameters": {"type": "object", "properties": {"code": {"type": "string"}}, "required": ["code"]}}},
    {"type": "function", "function": {"name": "refute_helper", "description": "Show that a helper theorem of the skeleton is false: give a proof of its negation (`¬ (type_of% @name)`, every binder universally quantified). If Lean accepts the proof with no sorry, the helper is marked false and the skeleton is revised around it.",
     "parameters": {"type": "object", "properties": {"name": {"type": "string"}, "proof": {"type": "string", "description": "a term or `by` tactic block proving the negation"}},
                    "required": ["name", "proof"]}}},
]


def tools_for(task, library=False, topdown=False, compact=False):
    """Tool definitions. The top-down tools are listed only with `topdown` (dialogs pick their
    tools by name, so the other loops never see them). `compact` (the top-down loop's dialogs)
    gives read_file its `name` argument and search_library its lower maximum."""
    read_props = {"path": {"type": "string", "enum": task.readable}}
    read_desc = "Read a file from the workspace."
    if compact:
        read_props["name"] = {"type": "string", "description": "a declaration of candidate/Solution.lean to show "
                                                               "in full (path is then ignored)"}
        read_desc = ("Read a file from the workspace. candidate/Solution.lean is shown with long proofs of proved "
                     "theorems elided; give `name` to see one declaration in full.")
    lib = [
        {"type": "function", "function": {"name": "search_library", "description": "Search the ProofForgeFin library index (theorems, definitions, structures, tactics, simp sets, modules) by keywords, declaration names or a statement. Returns the best matches with signature, module to import and doc string.",
         "parameters": {"type": "object", "properties": {"query": {"type": "string"},
                                                         "limit": {"type": "integer", "minimum": 1,
                                                                   "maximum": SEARCH_MAX_TOPDOWN if compact else 25}},
                        "required": ["query"]}}},
        {"type": "function", "function": {"name": "add_import", "description": "Add `import <module>` for a ProofForgeFin module at the top of candidate/Solution.lean; kept only if the file still compiles.",
         "parameters": {"type": "object", "properties": {"module": {"type": "string"}}, "required": ["module"]}}},
    ] if library else []
    return [
        {"type": "function", "function": {"name": "read_file", "description": read_desc,
         "parameters": {"type": "object", "properties": read_props, "required": ["path"]}}},
        {"type": "function", "function": {"name": "write_solution", "description": "Replace candidate/Solution.lean with the full given content.",
         "parameters": {"type": "object", "properties": {"content": {"type": "string"}}, "required": ["content"]}}},
        {"type": "function", "function": {"name": "replace_declaration", "description": f"Replace one top-level declaration (def, theorem, lemma, instance) in candidate/Solution.lean, identified by its name, with the given full text. If no declaration has that name, the text is inserted before `end {task.ns}`.",
         "parameters": {"type": "object", "properties": {"name": {"type": "string"}, "text": {"type": "string"}}, "required": ["name", "text"]}}},
        {"type": "function", "function": {"name": "try_snippet", "description": f"Compile the given Lean code appended inside `namespace {task.ns}` after the current candidate, without modifying the file. Returns errors and unsolved goals in the snippet." + (" `import ProofForgeFin...` lines in the snippet are moved to the file header (and added to candidate/Solution.lean when the snippet compiles); `open` lines apply to the snippet's later declarations." if library else ""),
         "parameters": {"type": "object", "properties": {"code": {"type": "string"}}, "required": ["code"]}}},
        {"type": "function", "function": {"name": "check", "description": "Compile candidate/Solution.lean. Returns Lean errors with goal states, remaining sorries and rule violations. If it compiles cleanly, runs the official judge and returns ACCEPTED or the rejection reason.",
         "parameters": {"type": "object", "properties": {}}}},
        {"type": "function", "function": {"name": "run_tests", "description": "Build the executable from the current candidate and run property tests against the requirements. Returns violated requirements and counterexamples.",
         "parameters": {"type": "object", "properties": {}}}},
    ] + lib + (TOPDOWN_TOOLS if topdown else [])


SCRATCH_EXIT = "PF_SCRATCH_EXIT="
SCRATCH_HEADER = re.compile(r"^Scratch\.lean:(\d+):(\d+): (error|warning)\b")
MESSAGE_CHARS = 1500     # characters of one Lean message shown for a snippet
SNIPPET_CHARS = 6000     # characters of all messages shown for a snippet
UNSHOWN = ("linter", "Hint:", "deprecated")   # header words of warnings Session._clean drops


def scratch_verdict(output, offset, exit_code):
    """(clean, messages) of a snippet compiled at line `offset` + 1 of Scratch.lean, from Lean's
    complete output and the exit status of `lean`. Messages located in the snippet are renumbered
    from 1 (`snippet:L:C`) and cleaned as Session._clean does, each shortened to MESSAGE_CHARS so
    that every header stays visible; a warning whose header Session._clean drops (a deprecation)
    is left out whole. The snippet is clean when it has no error and every warning in it is raised
    by a linter (it names a `linter.` option: an unused variable or simp argument, a style check)
    or is a deprecation: neither makes a proof wrong, and the judge decides on errors. A `sorry`
    warning is not clean. A missing exit status, or a failed `lean` that reported no error at all,
    is not clean either."""
    msgs, blocking, any_error = [], False, False
    for b in re.split(r"(?m)^(?=Scratch\.lean:\d+:\d+: (?:error|warning))", output or ""):
        m = SCRATCH_HEADER.match(b)
        if not m:
            continue
        sev, ln = m.group(3), int(m.group(1)) - offset
        any_error = any_error or sev == "error"
        if ln < 0:
            continue
        header = b.split("\n", 1)[0]
        if sev == "warning" and any(u in header for u in UNSHOWN):
            continue
        if sev == "error" or not re.search(r"\blinter\.\w+", b):
            blocking = True
        text = Session._clean(re.sub(r"^Scratch\.lean:\d+", f"snippet:{ln}", b)).strip("\n")
        if len(text) > MESSAGE_CHARS:
            text = text[:MESSAGE_CHARS].rstrip() + "\n  ... [message shortened]"
        msgs.append(text)
    if exit_code is None or (exit_code != 0 and not any_error):
        blocking = True
        msgs = msgs or [f"error: Lean stopped without reporting an error (exit status {exit_code}); "
                        "nothing is established"]
    return not blocking, msgs


EXPLORE = re.compile(r"^(?:#(?:check|print|eval|reduce|synth|guard_msgs|find|help)\b|example\b)")


def strip_explorations(text):
    """A banked chunk without the exploration commands a snippet may carry after a declaration
    (`#check`, `#print`, `#eval`, `example` ...), each with its indented continuation lines: they
    add nothing to the candidate, and `#eval` is forbidden there."""
    out, skipping = [], False
    for l in text.split("\n"):
        if EXPLORE.match(l):
            skipping = True
            continue
        if skipping and (not l.strip() or l[:1].isspace()):
            continue
        skipping = False
        out.append(l)
    return "\n".join(out).strip("\n")


def join_messages(msgs, limit=SNIPPET_CHARS):
    """Messages for the model, the first ones whole up to `limit` characters; the headers of the
    ones left out are listed."""
    out, used, rest = [], 0, []
    for k, m in enumerate(msgs):
        if used + len(m) > limit and out:
            rest = [x.split("\n", 1)[0] for x in msgs[k:]]
            break
        out.append(m)
        used += len(m) + 1
    text = "\n".join(out)
    if rest:
        text += f"\n... {len(rest)} more message(s): " + "; ".join(r[:160] for r in rest[:12])
    return text


class Session:
    # Class defaults, so that a session built without __init__ (tests) behaves as in the other loops.
    topdown = False
    prior_notes = {}
    resume_goals = ()
    round_offset = 0
    goal_tool = False        # --goal-tool: persistent Lean session (agents/leanserver.py)
    refute_samples = 0       # --refute: instances per new helper statement (agents/refute.py)
    variants_k = 0           # --variants (agents/variants.py)
    LOG_LOCK = threading.Lock()   # parallel variants log into the same events

    def __init__(self, task, model, start, out, budget=None, mode="repair", library=False):
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
        # ProofForgeFin in the workspace, so that the candidate can import it in every compile;
        # the judge vendors the same version into its own fresh project.
        self.library = library
        self.lib_index = None
        if library:
            fin_lib.vendor(self.ws, force=True)
            self.lib_index = fin_lib.Index.load()
        self.version = 0
        self.targets = set()   # planned helper lemmas the bank may replace while they are sorry
        self.plan_count = 0
        self.accepted = False
        self.last_good = None  # source of the newest version known to compile
        self.events = []
        # Top-down loop state (unused by the other loops): helpers shown false with a Lean-checked
        # refutation, notes from dialogs that did not prove a declaration, and tools added to the
        # obligation dialogs.
        self.refuted = {}
        self.notes = {}
        self.extra_tools = set()
        self.skeleton_ctx = None
        self.topdown = False   # compact candidate views, read_file by declaration, checked decompositions
        # Attempt ledger (agents/ledger.py): every source that compiled, keyed by hash; accepted
        # skeletons; failure notes of resumed prior attempts per goal; their open goals; the offsets
        # that keep new skeleton and planner names apart from carried ones.
        self.compiled = {}
        self.skeletons = []
        self.prior_notes = {}
        self.resume_goals = []
        self.round_offset = 0
        self.portfolio_seen = set()
        # Declaration boundary: the next top-level item, an `open` command or the namespace end.
        self.boundary = (r"(?:@\[|/--|private |protected |noncomputable |theorem |lemma |def |instance |abbrev "
                         rf"|structure |inductive |open |{re.escape(self.end)})")

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
            with self.budget.lock:   # concurrent variants: the dollar check and the reservation are one step
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
        with self.LOG_LOCK:
            self.events.append(kw)
            with (self.out / "events.jsonl").open("a") as f:
                f.write(json.dumps(kw) + "\n")

    def read_file(self, path, name=None):
        """A readable file. In the top-down loop the candidate is returned as compact_view() and
        `name` returns one declaration of the candidate in full."""
        if self.topdown and name:
            text = decl_text(self, str(name).split(".")[-1].strip())
            return text.rstrip() if text else f"error: no declaration `{name}` in candidate/Solution.lean"
        if path not in self.task.readable:
            return "error: not readable"
        if self.topdown and path == "candidate/Solution.lean":
            return compact_view(self)
        return (self.ws / path).read_text()

    def write_solution(self, content):
        if len(content) > 80_000:
            return "error: file too large"
        self._save(content, "write_solution")
        return f"written (version {self.version}, {len(content)} bytes)"

    DECL = re.compile(rf"^{DECL_PREFIX}{DECL_KINDS}\s+([^\s:({{\[]+)", re.M)

    def _source(self):
        return (self.ws / "candidate/Solution.lean").read_text()

    def _normalize(self, text):
        """Keep the required theorems at the end of the file, after every helper."""
        chunks = []
        for t in self.theorems:
            m = re.search(rf"^{DECL_PREFIX}theorem\s+{re.escape(t)}(?![\w.'])", text, re.M)
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
            while a > 0 and (lines[a - 1].startswith("@[") or lines[a - 1].rstrip().endswith("-/")
                             or OPEN_IN.match(lines[a - 1])):
                if lines[a - 1].rstrip().endswith("-/"):
                    while a > 0 and not lines[a - 1].lstrip().startswith("/-"):
                        a -= 1
                a -= 1
            b = starts[k + 1][0] if k + 1 < len(starts) else (ends_at[-1] if ends_at else len(lines))
            # `open` commands between declarations are not part of the one replaced.
            while b - 1 > a and (lines[b - 1].startswith("@[") or lines[b - 1].strip() == ""
                                 or lines[b - 1].startswith("open ")):
                b -= 1
            return "\n".join(lines[:a] + body + [""] + lines[b:]), "replaced"
        e = ends_at[-1] if ends_at else len(lines)
        return "\n".join(lines[:e] + body + [""] + lines[e:]), "inserted"

    def compile(self, tail=9000):
        src = self._source()
        r = judge.in_container(self.ws, f"lake build Solution 2>&1 | tail -c {tail}", timeout=600)
        if "error:" not in r["output_tail"]:
            self.last_good = src
            self.__dict__.setdefault("compiled", {})[hashlib.sha256(src.encode()).hexdigest()] = (self.version, src)
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
        short = name.split(".")[-1]
        if self.refute_samples and "sorry" in (text or "") and short not in self.theorems:
            false = refute.check(self, [short], f"replace_declaration:{short}")
            if false:   # a helper the model states with sorry is refused when Lean shows it false
                self._save(before, f"revert false {short}")
                return (f"REVERTED: `{short}` is false, so the file is unchanged (version {self.version}). Lean "
                        f"evaluated it on concrete values: counterexample {false[short]} (the kernel checked the "
                        "refutation). State a true helper instead.")
        return f"{action} declaration {name} (version {self.version}); file compiles"

    @staticmethod
    def _clean(text):
        keep = [l for l in text.splitlines()
                if not l.startswith("trace:") and not re.match(r"^[✔✖⚠] \[\d+/\d+\]", l)
                and "linter" not in l and "Hint:" not in l and "deprecated" not in l]
        return "\n".join(keep)

    def _snippet_imports(self, code, src):
        """Import lines of a snippet: (code with them blanked, ProofForgeFin modules to hoist into
        the header, refusal or None). Imports already in the candidate are dropped; a module that
        is not a ProofForgeFin module (or any import when the library is off) is refused. Blanking
        keeps the snippet's line numbers."""
        lines, hoist, refused = code.split("\n"), [], []
        for i, l in enumerate(lines):
            m = re.match(r"^\s*import\s+(\S+)\s*$", l)
            if not m:
                continue
            lines[i] = ""
            mod = m.group(1)
            if re.search(rf"^\s*import\s+{re.escape(mod)}\s*$", src, re.M) or mod in hoist:
                continue
            if self.library and fin_lib.IMPORT_RE.match(mod) and fin_lib.module_file(mod).is_file():
                hoist.append(mod)
            else:
                refused.append(mod)
        if not refused:
            return "\n".join(lines), hoist, None
        allowed = ("only ProofForgeFin modules can be imported from a snippet (they are moved to the file header)"
                   if self.library else "the library is not available in this run, so a snippet cannot import modules")
        return code, [], (f"error: not compiled: `import {'`, `import '.join(refused)}` refused; {allowed}. "
                          "The candidate's own imports are already in scope; remove the line and resend the snippet.")

    def _snippet_opens(self, code):
        """Top-level `open X` lines of a snippet apply to its later declarations: each line is
        blanked and every later declaration gets `open X in` on its first line (attribute lines
        joined to it, a doc comment above it made a plain comment, since `open ... in` must come
        first). The snippet compiles as written and its declarations bank with the same scope.
        Line numbers are kept."""
        lines, active = code.split("\n"), []
        for i, l in enumerate(lines):
            if l.startswith("open ") and not OPEN_IN.match(l):
                active.append(l[len("open "):].split("--")[0].strip())
                lines[i] = ""
                continue
            if not active or not self.DECL.match(l) or OPEN_IN.match(l):
                continue
            j, attrs = i, []
            while j > 0 and lines[j - 1].startswith("@["):
                j -= 1
                attrs.insert(0, lines[j].strip())
                lines[j] = ""
            if j > 0 and lines[j - 1].rstrip().endswith("-/"):
                k = j - 1
                while k > 0 and not lines[k].lstrip().startswith("/-"):
                    k -= 1
                lines[k] = lines[k].replace("/--", "/-", 1)
            lines[i] = f"open {' '.join(active)} in " + " ".join(attrs + [l])
        return "\n".join(lines)

    def scratch_text(self, code, hoist=()):
        """The scratch document of a snippet: the current candidate with the declarations `code`
        redefines removed and the modules in `hoist` added to the header, then `code`, then the
        namespace end. Returns (document, number of lines before the snippet)."""
        src = self._source()
        # Declarations redefined by the snippet are removed from the context first.
        for m in self.DECL.finditer(code):
            if re.search(rf"^{DECL_PREFIX}{DECL_KINDS}\s+{re.escape(m.group(1).split('.')[-1])}(?![\w.'])", src, re.M):
                src, _ = self._replace_in(src, m.group(1), "")
        body = src.rsplit(self.end, 1)[0] if self.end in src else src
        if hoist:
            bl = body.split("\n")
            last = max([i for i, l in enumerate(bl) if re.match(r"^\s*import\s+\S+", l)], default=-1)
            bl[last + 1:last + 1] = [f"import {m}" for m in hoist]
            body = "\n".join(bl)
        offset = body.count("\n") + 1
        return body + "\n" + code + f"\n\n{self.end}\n", offset

    def _scratch(self, code, hoist=()):
        """Compile `code` after the current candidate (scratch_text). Returns (clean, messages
        located in the code renumbered from 1, elapsed ms)."""
        scratch, offset = self.scratch_text(code, hoist)
        if self.goal_tool:   # a snippet with an error or a sorry is answered by the persistent session
            fast = leanserver.fast_snippet(self, scratch, offset, code)
            if fast and fast[0] is False:
                self.log(kind="fast_check", version=self.version, ok=False, ms=fast[2])
                return fast
        (self.ws / "Scratch.lean").write_text(scratch)
        # Lean's whole output goes to a file the host reads back, with the exit status of `lean`:
        # the verdict never rests on a truncated tail (goal states of a large definition can push
        # every error header out of a few kilobytes of output).
        name = judge.output_name("scratch")
        r = judge.in_container(self.ws, f"lake build {self.task.lib} >/dev/null 2>&1; lake env lean Scratch.lean > {name} 2>&1; "
                                        f"echo {SCRATCH_EXIT}$?", timeout=300)
        path = self.ws / name
        output = path.read_text(errors="replace") if path.exists() else ""
        path.unlink(missing_ok=True)
        m = re.search(rf"{SCRATCH_EXIT}(\d+)", r["output_tail"])
        clean, msgs = scratch_verdict(output, offset, int(m.group(1)) if m else None)
        if judge.TIMEOUT_MARK in r["output_tail"]:   # stopped at the time limit: nothing is established
            clean = False
            msgs = msgs or [judge.TIMEOUT_MARK]
        return clean, msgs, r["elapsed_ms"]

    def try_snippet(self, code):
        src = self._source()
        code, hoist, refusal = self._snippet_imports(code, src)
        if refusal:
            self.log(kind="snippet_import", version=self.version, refused=True, result=refusal[:300])
            return refusal
        code = self._snippet_opens(code)
        clean, msgs, ms = self._scratch(code, hoist)
        self.log(kind="snippet", version=self.version, ok=clean, ms=ms, **({"hoisted": hoist} if hoist else {}))
        if not clean:
            return join_messages(msgs)
        note = ""
        for mod in hoist:   # the candidate gets the imports the snippet compiled with
            res = self.add_import(mod)
            self.log(kind="snippet_import", version=self.version, module=mod, added=res.startswith("added"))
            if not res.startswith("added"):
                return ("snippet compiles, but " + res.split("\n")[0] + " so nothing was banked. Errors:\n"
                        + "\n".join(res.split("\n")[1:])[-3000:])
            note += f"; added `import {mod}` to candidate/Solution.lean"
        self.bank_notes = []
        banked = self.bank(code)
        notes, self.bank_notes = self.bank_notes, []
        return ("snippet compiles with no errors" + (" (linter warnings only)" if msgs else " or warnings")) + note + (
            f"; banked into candidate/Solution.lean: {', '.join(banked)} (version {self.version})" if banked else "") + (
            "; " + "; ".join(notes) if notes else "")

    def _chunks(self, code):
        """Top-level declarations of `code` as (name, text), each with the attribute and doc
        comment lines directly above it."""
        lines = code.split("\n")
        starts = [i for i, l in enumerate(lines) if self.DECL.match(l)]
        out = []
        for k, a in enumerate(starts):
            while a > 0 and (lines[a - 1].startswith("@[") or lines[a - 1].lstrip().startswith("/--")):
                a -= 1
            b = starts[k + 1] if k + 1 < len(starts) else len(lines)
            while b > 0 and b - 1 > a and (lines[b - 1].startswith("@[") or lines[b - 1].lstrip().startswith("/--")):
                b -= 1
            out.append((self.DECL.match(lines[starts[k]]).group(1).split(".")[-1], "\n".join(lines[a:b]).strip("\n")))
        return out

    def bank(self, code):
        """Install declarations from a clean snippet: new names are appended, and a required
        theorem that is currently `sorry` is replaced by the proved version. When the snippet has
        several new declarations they are first installed together with one compile; if that
        does not compile they are installed one at a time as before."""
        src = self._source()
        existing = {m.group(1).split(".")[-1] for m in self.DECL.finditer(src)}
        new = [(n, strip_explorations(c)) for n, c in self._chunks(code) if "sorry" not in c and n not in existing]
        if len(new) > 1 and len({n for n, _ in new}) == len(new):
            before, text = src, src
            for n, c in new:
                text, _ = self._replace_in(text, n, c)
            self._save(text, f"banked {len(new)} declarations")
            if "error:" in self.compile(2000)["output_tail"]:
                self._save(before, f"revert banked {len(new)} declarations")
            else:
                done = [n for n, _ in new]
                rest = self._bank_each(code, skip=set(done))
                return done + rest
        return self._bank_each(code)

    def _bank_each(self, code, skip=()):
        lines = code.split("\n")
        starts = [i for i, l in enumerate(lines) if self.DECL.match(l)]
        src = self._source()
        existing = {m.group(1).split(".")[-1]: m.start() for m in self.DECL.finditer(src)}
        banked = []
        for k, a in enumerate(starts):
            if self.DECL.match(lines[starts[k]]).group(1).split(".")[-1] in skip:
                continue
            while a > 0 and (lines[a - 1].startswith("@[") or lines[a - 1].lstrip().startswith("/--")):
                a -= 1
            b = starts[k + 1] if k + 1 < len(starts) else len(lines)
            while b > 0 and b - 1 > a and (lines[b - 1].startswith("@[") or lines[b - 1].lstrip().startswith("/--")):
                b -= 1
            chunk = strip_explorations("\n".join(lines[a:b]))
            name = self.DECL.match(lines[starts[k]]).group(1).split(".")[-1]
            if "sorry" in chunk:
                continue
            if name not in existing:
                res = self.replace_declaration(name, chunk)
                if res.startswith("REVERTED"):   # the file is unchanged: nothing was banked
                    self.__dict__.setdefault("bank_notes", []).append(
                        f"`{name}` was not banked: " + res.split(" (version")[0].replace("REVERTED: ", ""))
                else:
                    banked.append(name)
            elif name in self.theorems or name in self.targets:
                decl = re.search(rf"theorem\s+{re.escape(name)}\b.*?(?=\n{self.boundary})", self._source(), re.S)
                if decl and "sorry" in decl.group(0):
                    # The proved theorem goes to the end, after the helpers it uses, or stays in
                    # place when it uses nothing declared after it (declarations after it may use
                    # it); the other placement is tried if the first does not compile. Kept only
                    # if the whole file compiles.
                    before = self._source()
                    removed, _ = self._replace_in(before, name, "")
                    moved, _ = self._replace_in(removed, name, chunk)
                    inplace, _ = self._replace_in(before, name, chunk)
                    at = next((m.start() for m in self.DECL.finditer(before) if m.group(1).split(".")[-1] == name), 0)
                    later = {m.group(1).split(".")[-1] for m in self.DECL.finditer(before) if m.start() > at} - {name}
                    uses_later = any(re.search(rf"(?<![\w.']){re.escape(n)}(?![\w'])", chunk) for n in later)
                    order = [moved, inplace] if uses_later else [inplace, moved]
                    if self._normalize(order[0]) == self._normalize(order[1]):
                        order = order[:1]
                    for cand in order:
                        self._save(cand, f"banked {name}")
                        out = self.compile(2000)["output_tail"]
                        if "error:" not in out:
                            banked.append(name)
                            break
                        self.log(kind="bank_failed", name=name, version=self.version, output=self._clean(out)[-1500:])
                    else:
                        self._save(before, f"revert banked {name}")
                        errs = [l for l in self._clean(out).splitlines() if "error" in l and "build failed" not in l]
                        self.__dict__.setdefault("bank_notes", []).append(
                            f"`{name}` was not banked: with it candidate/Solution.lean does not compile"
                            + (f" ({'; '.join(e.strip()[:200] for e in errs[:2])})" if errs else ""))
                elif decl:
                    self.__dict__.setdefault("bank_notes", []).append(
                        f"`{name}` already has a proof in candidate/Solution.lean, which was kept")
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

    def dep_graph(self):
        """The compiled candidate's declarations from Lean: {full name: {"kind", "sorry", "deps"}},
        where `sorry` says the declaration's own type or value mentions `sorryAx` and `deps` are
        the candidate's declarations it mentions. Compiler-generated auxiliaries (`foo.proof_1`,
        `foo.match_1`, `foo.eq_1`, ...) are merged into their owner. Returns (graph, None), or
        (None, compiler output) when the file does not compile or the probe fails."""
        r = self.compile(8000)
        if "error:" in r["output_tail"]:
            return None, self._clean(r["output_tail"])
        (self.ws / "Deps.lean").write_text(DEPS_PROBE)
        name = judge.output_name("deps")
        out = self.ws / name
        p = judge.in_container(self.ws, f"lake env lean Deps.lean > {name} 2>&1; tail -c 1500 {name}", timeout=600)
        text = out.read_text(errors="replace") if out.exists() else ""
        out.unlink(missing_ok=True)
        if "PFDEPS " not in text:
            return None, "dependency probe failed: " + (p["output_tail"] or text)[-1500:]
        raw = {}
        for line in text.split("PFDEPS ", 1)[1].splitlines()[1:]:
            parts = line.split("\t")
            if len(parts) == 4:
                raw[parts[0]] = {"kind": parts[1], "sorry": parts[2] == "1", "deps": set(parts[3].split())}
        owner = {n: aux_owner(n, raw) for n in raw}
        graph = {}
        for n, rec in raw.items():
            o = owner[n]
            g = graph.setdefault(o, {"kind": raw[o]["kind"], "sorry": False, "deps": set()})
            g["sorry"] = g["sorry"] or rec["sorry"]
            g["deps"] |= {owner.get(d, d) for d in rec["deps"]} - {o}
        return graph, None

    def refute_helper(self, name, proof):
        """Lean-checked refutation of a helper theorem: `¬ (type_of% @name)` proved after the
        current candidate, with no errors, warnings or sorry. Marks the helper false; the
        candidate is not changed."""
        short = (name or "").split(".")[-1].strip()
        text = decl_text(self, short)
        if not text or not re.search(rf"\b(?:theorem|lemma)\s", text.split(":")[0] + " ") or short in self.theorems:
            return f"error: `{short}` is not a helper theorem of candidate/Solution.lean"
        if own_sorry_free(self, short):
            return f"error: `{short}` is proved, so it cannot be refuted"
        proof = (proof or "").strip()
        if not proof or "sorry" in proof:
            return "error: give a complete proof of the negation, without sorry"
        code = f"theorem {short}_refuted : ¬ (type_of% @{short}) :=\n{textwrap_indent(proof)}"
        clean, msgs, ms = self._scratch(code)
        self.log(kind="refute", name=short, ok=clean, ms=ms, proof=proof[:2000])
        if not clean:
            return "refutation not accepted:\n" + "\n".join(msgs)[-4000:]
        self.refuted[short] = {"proof": proof, "stmt": statement_of(text)}
        return (f"REFUTED: Lean accepts a proof of ¬ `{short}`. The helper is false; the skeleton will be "
                "revised without it. Stop working on it.")

    def submit_skeleton(self, code):
        """Tool of the structure dialog (top-down loop): accept_skeleton() for the current round."""
        if self.skeleton_ctx is None:
            return "error: no structure phase is running"
        return accept_skeleton(self, code or "", self.skeleton_ctx)[1]

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

    def search_library(self, query, limit=10):
        if not self.lib_index:
            return "error: the library is not available in this run"
        try:
            limit = max(1, min(SEARCH_MAX_TOPDOWN if self.topdown else 25, int(limit or 10)))
        except (TypeError, ValueError):
            limit = 10
        # Goal-aware ranking: the obligation being proved, when known (set by library_hints).
        hits = self.lib_index.search(query or "", limit=limit, goal=getattr(self, "lib_goal", None))
        self.log(kind="library_search", query=(query or "")[:500], hits=[e["name"] for e in hits])
        if not hits:
            return "no library declaration matches; try other words or a declaration name"
        return fin_lib.render(hits)

    def add_import(self, module):
        """Transactional: the import is kept only if the file still compiles."""
        module = (module or "").strip()
        if not self.library:
            return "error: the library is not available in this run"
        if not fin_lib.IMPORT_RE.match(module) or not fin_lib.module_file(module).is_file():
            return f"error: no ProofForgeFin module {module!r}"
        before = self._source()
        if re.search(rf"^\s*import\s+{re.escape(module)}\s*$", before, re.M):
            return f"`import {module}` is already present"
        lines = before.split("\n")
        last = max([i for i, l in enumerate(lines) if re.match(r"^\s*import\s+\S+", l)], default=-1)
        lines.insert(last + 1, f"import {module}")
        self._save("\n".join(lines), f"import {module}")
        r = self.compile()
        if "error:" in r["output_tail"]:
            self._save(before, f"revert import {module}")
            return (f"REVERTED: with `import {module}` the file does not compile (names may clash with the "
                    "library's), so the file is unchanged. Errors:\n" + self._clean(r["output_tail"])[-4000:])
        return f"added `import {module}` (version {self.version}); file compiles"

    def library_hints(self, text, limit=8, goal=None):
        """The library declarations the index ranks highest for `text` (and the obligation's
        statement `goal`, which later searches also rank against), for an obligation's prompt."""
        if not self.lib_index:
            return ""
        self.lib_goal = goal
        hits = [e for e in self.lib_index.search(text, limit=limit + 6, goal=goal) if e["kind"] != "module"][:limit]
        return fin_lib.render(hits, sig_chars=300) if hits else ""

    def run_tests(self):
        b = binary_check.check_binary(str(self.ws / "candidate/Solution.lean"), n_cases=300,
                                      seed=self.version, task=self.task)
        self.log(kind="tests", version=self.version, status=b["status"], violations=b.get("violations"))
        if b["status"] == "BUILD_FAILED":
            return "executable build failed:\n" + b["build"].get("output_tail", "")[-3000:]
        ws = [{"requirement": w["requirement"], "message": w["message"],
               "input": w["input"], "output": w["output"]} for w in b["witnesses"][:3]]
        return json.dumps({"status": b["status"], "violations": b["violations"], "examples": ws})


def dialog(s, model, effort, system, user, tool_names, max_turns, done, label, stop=None):
    """Run one tool-using dialog until done() or the turn budget is spent. A set `stop` event
    (parallel variants) ends it before its next turn or tool call."""
    tools = [t for t in tools_for(s.task, s.library, topdown=True, compact=s.topdown) + [leanserver.GOAL_TOOL]
             if t["function"]["name"] in tool_names]
    messages = [{"role": "system", "content": system}, {"role": "user", "content": user}]
    extra = {} if effort == "default" else {"reasoning_effort": effort}
    for turn in range(max_turns):
        if stop is not None and stop.is_set():
            return False, messages
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
            if stop is not None and stop.is_set():
                return False, messages
            if s.budget.past_deadline():
                s.budget.stop = "wall"
                raise BudgetExceeded("wall")
            name = c["function"]["name"]
            try:
                args = json.loads(c["function"].get("arguments") or "{}")
            except json.JSONDecodeError:
                args = {}
            fn = {"read_file": lambda: s.read_file(args.get("path", ""), args.get("name")),
                  "write_solution": lambda: s.write_solution(args.get("content", "")),
                  "replace_declaration": lambda: s.replace_declaration(args.get("name", ""), args.get("text", "")),
                  "try_snippet": lambda: s.try_snippet(args.get("code", "")),
                  "check": s.check, "run_tests": s.run_tests,
                  "search_library": lambda: s.search_library(args.get("query", ""), args.get("limit", 10)),
                  "add_import": lambda: s.add_import(args.get("module", "")),
                  "submit_skeleton": lambda: s.submit_skeleton(args.get("code", "")),
                  "refute_helper": lambda: s.refute_helper(args.get("name", ""), args.get("proof", "")),
                  "goal_at": lambda: leanserver.goal_at(s, args.get("name", ""), args.get("line"))
                  }.get(name) if name in tool_names else None
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


LIBRARY_TOOLS = {"search_library", "add_import"}


def system_prompt(s):
    """Task brief and workflow; with the library, the library section generated from its index."""
    return task_brief(s.task, s.mode) + WORKFLOW + (library_brief(s.lib_index) if s.library else "")


def lib_tools(s):
    return LIBRARY_TOOLS if s.library else set()


def goal_tools(s):
    return {"goal_at"} if s.goal_tool else set()


def obligation_query(s, stmt):
    """Retrieval text for an obligation: its statement and the doc strings of the specification
    definitions it names."""
    spec = (s.task.root / s.task.spec_dir / "Spec.lean").read_text()
    docs = []
    for name in sorted(set(re.findall(r"[A-Za-z_][\w.']*", stmt))):
        m = re.search(rf"/--((?:(?!-/).)*)-/\s*\n(?:@\[[^\]]*\]\s*)?(?:def|abbrev|structure|inductive) {re.escape(name)}\b", spec, re.S)
        if m:
            docs.append(re.sub(r"\s+", " ", m.group(1)).strip())
    return stmt + "\n" + "\n".join(docs)


def orchestrate(s, a, middle=None):
    """Phase 0 (behavior first), then `middle` (default: phases 1 and 2, structured(); the
    top-down loop passes topdown_phases()), then phase 3 (whole-file repair) if not accepted."""
    system = system_prompt(s)
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
    ok0 = tests_ok["v"] or dialog(s, a.model, a.effort, system, user0, {"write_solution", "run_tests", "read_file"} | lib_tools(s),
                                  a.phase0_turns, lambda: tests_ok["v"], "implement")[0]
    s.log(kind="phase", phase="implement", ok=ok0)
    if ok0:
        (middle or structured)(s, a, system, spec)
    # Phase 3: spend the rest of the budget on whole-file repair from the current file,
    # with the same protocol as the compile-and-retry baseline.
    if not s.accepted:
        import baseline
        s.log(kind="phase", phase="whole-file")
        baseline.run(s, argparse.Namespace(model=a.model, effort=a.effort, max_turns=200),
                     state="current, partly implemented" if impl else "current, partly repaired",
                     library_text=library_brief(s.lib_index, tools=False) if s.library else "")


def structured(s, a, system, spec):
    """Phases 1 and 2: per-obligation dialogs, then planner-assisted resolution rounds."""
    resume_phase(s, a, system, spec)
    # Phase 1: one focused dialog per obligation, in the task's listed order. The tactic portfolio
    # first tries every pending required theorem in one batch.
    status = s.check_status()
    if portfolio.close_goals(s, a, [t for t in s.theorems if status.get(t) != "PROVED"], "pass1"):
        status = s.check_status()
    for t in s.theorems:
        if status.get(t) == "PROVED" or own_sorry_free(s, t):
            continue
        prove_target(s, a, system, spec, t, a.obligation_turns, "pass1")
        status = s.check_status()
    # Phase 2: resolve what is left, decomposing hard goals with the planner (A2), and
    # repeat while a round makes progress.
    pending = [t for t, v in s.check_status().items() if v != "PROVED"]
    for _ in range(a.rounds):
        if not pending:
            break
        for t in pending:
            resolve(s, a, system, spec, t, 0)
        prune(s)
        now = [t for t, v in s.check_status().items() if v != "PROVED"]
        progress = len(now) < len(pending)
        pending = now
        if not progress:
            break
    s.check()


def decl_text(s, name, src=None):
    m = re.search(rf"^{DECL_PREFIX}{DECL_KINDS}\s+{re.escape(name)}(?=[\s:({{\[]).*?"
                  rf"(?=^{s.boundary})", s._source() if src is None else src, re.S | re.M)
    return m.group(0) if m else ""


COMPACT_NOTE = ("-- Proofs of proved theorems longer than {n} lines are elided below (`...`); "
                "read_file with `name` shows one declaration in full.\n")


def compact_view(s, src=None, keep=(), min_lines=4):
    """The candidate as shown to the top-down dialogs and the planner: definitions, statements and
    open proofs in full, the proof of a theorem without `sorry` replaced by `...` when it has at
    least `min_lines` lines (declarations in `keep` stay whole). The file itself is unchanged."""
    src = s._source() if src is None else src
    out, n = src, 0
    for m in s.DECL.finditer(src):
        name = m.group(1).split(".")[-1]
        if name in keep:
            continue
        text = decl_text(s, name, src)
        if not text or "sorry" in text or not re.match(rf"^{DECL_PREFIX}(?:theorem|lemma)\s", text):
            continue
        body = text.rstrip()
        lines = body.count("\n") + 1
        stmt = statement_of(body)
        if lines < min_lines or stmt == body.strip():
            continue
        out = out.replace(body, f"{stmt} := by\n  ...  -- proved ({lines} lines)", 1)
        n += 1
    if not n:
        return out
    head, sep, rest = out.partition(f"namespace {s.ns}\n")
    return head + sep + COMPACT_NOTE.format(n=min_lines - 1) + rest if sep else COMPACT_NOTE.format(n=min_lines - 1) + out


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
    """Make `name` sorry-free: try directly, then decompose with the planner (bounded depth).
    A helper refuted during the attempt (top-down loop) is left alone."""
    if not own_sorry_free(s, name):
        prove_target(s, a, system, spec, name, a.obligation_turns, f"d{depth}", plan_text)
    if not own_sorry_free(s, name) and depth < a.max_depth and a.planner != "none" and name not in s.refuted:
        lemmas, text = plan(s, a, spec, name, s.plan_count)
        portfolio.close_goals(s, a, lemmas, f"plan:{name}")
        for l in lemmas:
            resolve(s, a, system, spec, l, depth + 1, text)
        if name not in s.refuted:
            prove_target(s, a, system, spec, name, a.obligation_turns, f"d{depth}", text)
    if own_sorry_free(s, name):
        for dep in pending_deps(s, name):
            if dep not in s.refuted:
                resolve(s, a, system, spec, dep, depth + 1, plan_text)
    ok = s.check_status([name]).get(name) == "PROVED"
    s.log(kind="resolve", name=name, depth=depth, ok=ok)
    return ok


def prune(s):
    """Delete helper declarations that still use sorry and are referenced by nothing else.
    A declaration with a dotted name (`Foo.bar`) is kept, since dot notation (`h.bar`) uses it
    without naming it, and so is one whose text cannot be located. The deletions are kept only
    if the file still compiles."""
    before = s._source()
    removed = []
    changed = True
    while changed:
        changed = False
        src = s._source()
        for m in list(s.DECL.finditer(src)):
            if "." in m.group(1):
                continue
            n = m.group(1)
            text = decl_text(s, n)
            if n in s.theorems or not text or "sorry" not in text:
                continue
            others = src.replace(text, "")
            if not re.search(rf"(?<![\w.]){re.escape(n)}(?![\w?!'])", others):
                new, _ = s._replace_in(src, n, "")
                s._save(new, f"prune {n}")
                removed.append(n)
                changed = True
                break
    if removed and "error:" in s.compile(2000)["output_tail"]:
        s._save(before, f"revert prune {', '.join(removed)}")


PLANNER_SYSTEM = """You are a Lean 4 proof architect (Lean v4.35.0 core library only, no Mathlib).
Given a specification, a candidate implementation, and a required theorem that a prover failed to prove,
you design a chain of helper lemmas that makes the proof routine. Each lemma must be TRUE, stated in
Lean 4 syntax that elaborates against the given file, and small enough to prove by induction or simp/omega.
Prefer general lemmas over specific ones. Avoid Mathlib names (no Finset, no linarith, no BigOperators)."""


def plan(s, a, spec, t, attempt):
    """Ask the planner model for helper lemma statements; install them as sorry targets."""
    stmt = re.search(rf"theorem\s+{re.escape(t)}\s*:[^\n]*",
                     s.read_file(f"{s.task.spec_dir}/Challenge.lean") + s._source())
    user = (f"{spec}\n\n=== candidate/Solution.lean (current) ===\n"
            f"{compact_view(s) if getattr(s, 'resume_record', None) else s._source()}\n\n"
            f"The prover could not prove `{stmt.group(0).replace(' := sorry', '') if stmt else t}`.\n"
            "Reply with (1) a short proof plan in prose, then (2) exactly one ```lean code block containing 2 to 6 "
            "helper lemmas, each written as `theorem <unique_name> ... := by sorry`, in dependency order, inside no "
            f"namespace (the code is inserted inside `namespace {s.ns}`). Use names prefixed with `plan"
            f"{attempt}_` and no `?` or `!` in names.")
    extra = {} if a.planner_effort == "default" else {"reasoning_effort": a.planner_effort}
    for tries in range(3):
        try:
            r, u = s.call(a.planner, [{"role": "system", "content": PLANNER_SYSTEM}, {"role": "user", "content": user}],
                          f"plan:{s.task.id}:{t}:{attempt}", timeout=900, **extra)
        except APIError as e:
            s.log(kind="api_error", status=e.status, body=e.body[:300])
            s.pause(20)
            continue
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
        false = refute.check(s, names, f"plan:{t}")
        if false:   # refused before any turn is spent on them
            s._save(before, f"revert false plan {t} {attempt}")
            s.log(kind="plan_refuted", theorem=t, attempt=attempt, false=false, model=a.planner,
                  usd_list=round(list_cost(a.planner, u or {}), 4))
            user += ("\n\nLean evaluated these lemmas on concrete values and found them false:\n"
                     + refute.feedback(false) + "\nReply again with a plan whose lemmas are all true.")
            continue
        s.targets.update(names)
        s.plan_count += 1
        prose = text[: m.start()].strip()[-3000:]
        (s.out / f"plan_{t}_{attempt}.md").write_text(text)
        s.log(kind="plan", theorem=t, attempt=attempt, lemmas=names, model=a.planner, prose=prose[:3000], code=code[:6000],
              usd_list=round(list_cost(a.planner, u or {}), 4))
        print(f"[plan {t}] {names}", flush=True)
        return names, prose
    return [], ""


def prove_target(s, a, system, spec, t, budget, label, plan_text=""):
    if portfolio.close_goals(s, a, [t], label).get(t):
        s.log(kind="obligation", label=label, theorem=t, ok=True, by="portfolio")
        return True
    if t not in s.theorems and t not in s.refuted and (false := refute.check(s, [t], label)):
        # A helper Lean shows false on concrete values gets no turns.
        s.refuted[t] = {"proof": "", "counterexample": false[t], "stmt": statement_of(decl_text(s, t))}
        s.log(kind="obligation", label=label, theorem=t, ok=False, by="refuted", counterexample=false[t])
        return False
    src = s._source()
    m = re.search(rf"theorem\s+{re.escape(t)}\b[^\n]*(?:\n(?!theorem|lemma|def|end )[^\n]*)*", src)
    stmt = (m.group(0).split(":= by")[0].split(":= sorry")[0] if m else t).strip()
    status = s.check_status()
    defs = ", ".join(f"`{d}`" for d in s.task.definitions)
    hints = s.library_hints(obligation_query(s, stmt), goal=stmt) if s.library else ""
    if hints:
        s.log(kind="library_hints", theorem=t, hits=re.findall(r"^\[\w+\] (\S+)", hints, re.M))
    # The top-down loop and resumed runs (whose files hold the carried declarations) show the
    # candidate with long proofs of proved theorems elided.
    shown = compact_view(s, src, keep={t}) if s.topdown or getattr(s, "resume_record", None) else src
    user = (f"{spec}\n\n=== candidate/Solution.lean (current) ===\n{shown}\n\n"
            f"Current requirement status: {', '.join(f'{k}={v}' for k, v in status.items())}\n\n"
            + (f"Proof plan from the architect:\n{plan_text}\n\n" if plan_text else "")
            + (f"ProofForgeFin declarations the library index ranks highest for this obligation "
               f"(search_library finds more; add_import adds a module):\n{hints}\n\n" if hints else "")
            + f"Your task now: prove `{stmt}`. Do not change {defs} or anything already proved. "
            "Develop the proof with try_snippet; a clean snippet that proves "
            f"`{t}` replaces its sorry automatically. You may use the other helper lemmas in the file even if "
            "they are still sorry; they are proved separately."
            + (" If you find that the statement is false, prove its negation with refute_helper; the skeleton "
               "is then revised without it." if "refute_helper" in s.extra_tools and t not in s.theorems else "")
            + (f"\n\nEarlier attempts at this target ended like this (the file may have changed since):\n"
               f"{notes_text(s, t)}" if s.extra_tools and s.notes.get(t) else "")
            + (f"\n\n{prior}" if (prior := ledger.prompt_notes(s.prior_notes, t)) else ""))
    def own_proof_done():
        """The target's own proof is sorry-free and the file compiles (dependencies may be pending),
        or the target was refuted."""
        if t in s.refuted:
            return True
        m2 = re.search(rf"^{DECL_PREFIX}theorem\s+{re.escape(t)}(?![\w.']).*?(?=^{s.boundary})", s._source(), re.S | re.M)
        return bool(m2) and "sorry" not in m2.group(0) and s.check_status([t]).get(t) != "ERROR"
    ok, messages = dialog(s, a.model, a.effort, system, user,
                          {"try_snippet", "replace_declaration", "check", "read_file"} | lib_tools(s) | goal_tools(s)
                          | s.extra_tools, budget, own_proof_done, f"{label}:{t}")
    ok = ok and t not in s.refuted
    by_variant = False
    if not ok:
        remember(s, t, messages)
        # Still open after its first dialog: K short variants at once (agents/variants.py).
        if t not in s.refuted and variants.run(s, a, system, spec, t, label, plan_text):
            ok = by_variant = True
    s.log(kind="obligation", label=label, theorem=t, ok=ok, **({"by": "variant"} if by_variant else {}))
    return ok


# Top-down loop (--loop topdown): structure phase, then fill phase

# Harness probe run in the session workspace after `lake build Solution` (never part of a
# candidate, never judged): one line per declaration of the candidate module.
DEPS_PROBE = """import Solution
import Lean
open Lean

/-! Harness probe: for every declaration of the compiled candidate module, its kind, whether its
own type or value mentions `sorryAx`, and the candidate declarations it mentions. -/
#eval show CoreM Unit from do
  let env ← getEnv
  let some sol := env.getModuleIdx? `Solution | throwError "module Solution not found"
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some sol then
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
      let used := ci.getUsedConstantsAsSet
      let deps := used.toList.filter (fun m => env.getModuleIdxFor? m == some sol)
      out := out.push s!"{n}\\t{kind}\\t{if used.contains ``sorryAx then 1 else 0}\\t{String.intercalate " " (deps.map toString)}"
  IO.println s!"PFDEPS {out.size}"
  for l in out do IO.println l
"""

# Last name components of compiler-generated declarations, merged into their owner.
AUX_LAST = re.compile(r"^(?:_.*|proof_\d+|match_\d+|eq_\d+|eq_def|induct|mutual_induct|fun_cases|brecOn|below|"
                      r"binductionOn|ibelow|recOn|casesOn|noConfusion|noConfusionType|sizeOf_spec|injEq|inj|ctorIdx)$")


def aux_owner(name, names):
    """The declaration a compiler-generated auxiliary belongs to (`foo.proof_1` -> `foo`)."""
    parts = name.split(".")
    while len(parts) > 1 and AUX_LAST.match(parts[-1]) and ".".join(parts[:-1]) in names:
        parts = parts[:-1]
    return ".".join(parts)


def short_name(full):
    """The name the source tools address a declaration by: the last component, with Lean's
    mangling of private names removed."""
    full = re.sub(r"^_private\.[^.]+(?:\.[^.]+)*?\.0\.", "", full)
    return full.split(".")[-1]


def textwrap_indent(text, pad="  "):
    return "\n".join(pad + l if l.strip() else l for l in text.split("\n"))


def notes_text(s, name, limit=1600):
    return "\n".join(f"- {n}" for n in s.notes.get(name) or [])[-limit:]


def remember(s, name, messages):
    """Keep the end of a dialog that did not prove `name` (the model's last words and the last
    tool result) for the next attempt and for a revised skeleton."""
    said = next((m["content"] for m in reversed(messages) if m["role"] == "assistant" and m.get("content")), "")
    got = next((m["content"] for m in reversed(messages) if m["role"] == "tool"), "")
    note = said.strip()[:600]
    if got:
        note += ("\n  Last tool result: " if note else "Last tool result: ") + got.strip()[-1000:]
    if note:
        s.notes[name] = (s.notes.get(name, []) + [note])[-2:]


def statement_of(text):
    """A declaration's text up to its proof."""
    return re.split(r":=\s*(?:by\b|sorry\b)|:=\s*$", text, maxsplit=1)[0].strip() if text else ""


def _norm(text):
    return re.sub(r"\s+", " ", text or "").strip()


def analyze(s, graph):
    """Required theorems against the dependency graph: `missing` (not in the module), `direct`
    (their own proof mentions sorry), `proved` (nothing they depend on mentions sorry),
    `open` (helper declarations whose own proof mentions sorry, with the required theorems that
    depend on each) and `reach` (every declaration each required theorem depends on)."""
    req = {t: f"{s.ns}.{t}" for t in s.theorems}
    reqfull = set(req.values())
    reach = {}
    for t, full in req.items():
        seen, todo = set(), [full]
        while todo:
            for d in graph.get(todo.pop(), {}).get("deps", ()):
                if d not in seen:
                    seen.add(d)
                    todo.append(d)
        reach[t] = seen
    opens = {}
    for t in s.theorems:
        for n in sorted(reach[t]):
            if n in graph and graph[n]["sorry"] and n not in reqfull:
                opens.setdefault(n, []).append(t)
    return {"missing": [t for t, f in req.items() if f not in graph],
            "direct": [t for t, f in req.items() if f in graph and graph[f]["sorry"]],
            "proved": [t for t, f in req.items() if f in graph and not graph[f]["sorry"]
                       and not any(graph.get(n, {}).get("sorry") for n in reach[t])],
            "open": opens, "reach": reach}


def reach_from(graph, roots):
    """Every declaration of the dependency graph that one of `roots` (full names) uses, directly or
    through others."""
    seen, todo = set(), list(roots)
    while todo:
        for d in graph.get(todo.pop(), {}).get("deps", ()):
            if d not in seen:
                seen.add(d)
                todo.append(d)
    return seen


def unreached_open(graph, roots, names):
    """The names among `names` (short names) whose declaration mentions `sorry` and that nothing
    in `roots` uses. A skeleton or a decomposition that leaves such a helper has not wired it into
    a proof, and prune() would delete it."""
    full = {}
    for n in graph:
        full.setdefault(short_name(n), n)
    seen = reach_from(graph, roots)
    return [n for n in names if n in full and graph[full[n]]["sorry"] and full[n] not in seen]


def lib_score(s, stmt):
    """How strongly the library index matches a statement (top BM25 score of a non-module hit);
    0 without the library."""
    if not s.lib_index or not stmt:
        return 0.0
    hits = [x for x in s.lib_index.scored(obligation_query(s, stmt), limit=8) if x[1]["kind"] != "module"]
    return round(hits[0][0], 2) if hits else 0.0


def open_helpers(s, an):
    """The open helpers the source tools can address, in fill order: shared by more required
    theorems first, then the ones the library index matches best, then file order."""
    src = s._source()
    out = []
    for full, users in an["open"].items():
        short = short_name(full)
        text = decl_text(s, short, src)
        if not text:
            continue
        stmt = statement_of(text)
        out.append({"name": short, "full": full, "users": sorted(set(users), key=s.theorems.index),
                    "lib": lib_score(s, stmt), "pos": src.find(text), "stmt": stmt})
    out.sort(key=lambda h: (-len(h["users"]), -h["lib"], h["pos"]))
    return out


SCOPE_CMD = re.compile(r"^\s*(namespace|section|end|variable|include|omit|universe|set_option|mutual|noncomputable section)\b")


def install_skeleton(s, code, status):
    """Install a skeleton into the current source (nothing is saved). Returns (source, info,
    problems): a required theorem that is not PROVED takes the skeleton's proof under its locked
    statement; a new declaration is appended; a helper that still uses sorry is replaced; a
    declaration that exists with a complete proof is kept. `import ProofForgeFin...` lines go to
    the header, top-level `open` lines apply to the later declarations (as in try_snippet)."""
    src = s._source()
    problems, notes, derived, helpers = [], [], [], []
    code = fin_lib.strip_comments(code)   # comments, doc comments included
    code, hoist, refusal = s._snippet_imports(code, src)
    if refusal:
        problems.append(refusal.replace("error: not compiled: ", ""))
    keep = []
    for l in code.split("\n"):
        if re.match(rf"^\s*(?:namespace|end)\s+{re.escape(s.ns)}\s*$", l) or re.match(r"^\s*#\w+", l):
            continue   # the task's namespace wrapper and #check-style commands are dropped
        if SCOPE_CMD.match(l):
            problems.append(f"`{l.strip()}` is not supported in a skeleton: state every helper at the top level of "
                            f"`namespace {s.ns}` with its hypotheses as explicit binders")
        keep.append(l)
    code = s._snippet_opens("\n".join(keep))
    chunks = s._chunks(code)
    if not chunks:
        problems.append("the code block has no declarations")
    names = [n for n, _ in chunks]
    for n in sorted({n for n in names if names.count(n) > 1}):
        problems.append(f"`{n}` is declared more than once")
    append = []
    for name, text in chunks:
        kind = re.match(rf"^{DECL_PREFIX}({DECL_KINDS[3:-1]})\s", text.split("\n", 1)[0] + " ")
        kind = kind.group(1) if kind else re.search(DECL_KINDS, text).group(0)
        cur = decl_text(s, name, src)
        if name in s.task.definitions:
            if _norm(fin_lib.strip_comments(cur)) != _norm(fin_lib.strip_comments(text)):
                problems.append(f"`{name}` is a required definition; a skeleton cannot change it (leave it out)")
            continue
        if name in s.theorems:
            if status.get(name) == "PROVED":
                notes.append(f"`{name}` is already proved and was kept")
                continue
            head = re.match(r"(.*?):=", re.sub(r"^open\s[^\n]*?\bin\s+", "", cur), re.S)
            body = re.match(r".*?(:=.*)$", text, re.S)
            if not head or not body:
                problems.append(f"`{name}`: no proof after `:=`")
                continue
            pre = re.match(r"^open\s[^\n]*?\bin\s+", text)
            src, _ = s._replace_in(src, name, (pre.group(0) if pre else "") + head.group(1).rstrip() + " "
                                   + body.group(1).strip())
            derived.append(name)
            continue
        if cur:
            if "sorry" not in cur:
                if _norm(cur) != _norm(text):
                    notes.append(f"`{name}` already exists with a complete proof; the existing declaration was kept")
                continue
            src, _ = s._replace_in(src, name, "")   # an open helper is replaced
        if "sorry" in text and kind not in ("theorem", "lemma"):
            problems.append(f"`{name}` is a {kind} with `sorry`: definitions need complete bodies; only theorems may "
                            "be left open")
        append.append((name, text))
        if "sorry" in text:
            helpers.append(name)
    for name, text in append:
        src, _ = s._replace_in(src, name, text)
    pending = [t for t in s.theorems if status.get(t) != "PROVED"]
    for t in pending:
        if t not in derived and "sorry" in decl_text(s, t, src):
            problems.append(f"`{t}` is not derived: the skeleton must give every unproved required theorem a proof "
                            "from helper theorems")
    if hoist:
        lines = src.split("\n")
        last = max([i for i, l in enumerate(lines) if re.match(r"^\s*import\s+\S+", l)], default=-1)
        lines[last + 1:last + 1] = [f"import {m}" for m in hoist]
        src = "\n".join(lines)
    return src, {"derived": derived, "helpers": helpers, "hoisted": hoist, "notes": notes}, problems


def accept_skeleton(s, code, ctx):
    """Install a skeleton and keep it only if the file compiles and Lean's dependency graph shows
    that no required theorem mentions sorry in its own proof (every open obligation is a helper
    theorem), that no definition is left open and that no refuted helper is used. Returns
    (accepted, message for the model)."""
    rnd, before = ctx["round"], s._source()

    def reject(msg):
        ctx["tries"] += 1
        s.log(kind="skeleton", round=rnd, source=ctx["source"], attempt=ctx["tries"], accepted=False,
              problems=msg[:3000], code=code[:8000])
        return False, ("SKELETON REJECTED; candidate/Solution.lean is unchanged.\n" + msg)
    src, info, problems = install_skeleton(s, code, ctx["status"])
    if problems:
        return reject("\n".join(f"- {p}" for p in problems))
    if s._normalize(src) == s._normalize(before):
        return reject("Nothing in the code is new: every declaration in it already exists with a complete proof.")
    s._save(src, f"skeleton {rnd}")
    graph, err = s.dep_graph()
    if graph is None:
        s._save(before, f"revert skeleton {rnd}")
        return reject("The file does not compile with the skeleton. Lean output:\n" + err[-5000:])
    an = analyze(s, graph)
    bad = [f"`{t}` uses `sorry` in its own proof; move that step into a named helper theorem and use it"
           for t in an["direct"]]
    bad += [f"`{t}` is missing from the compiled file" for t in an["missing"]]
    for full, users in an["open"].items():
        short = short_name(full)
        if graph[full]["kind"] != "theorem":
            bad.append(f"`{short}` ({graph[full]['kind']}) uses `sorry`; only helper theorems may be left open")
        ref = s.refuted.get(short)
        if ref and _norm(ref["stmt"]) == _norm(statement_of(decl_text(s, short))):
            bad.append(f"`{short}` was refuted (Lean accepted a proof of its negation); the skeleton must not use it")
    bad += [f"`{n}` is left open (`sorry`) but no required theorem uses it, so it would be dropped: use it in the "
            f"proof of the helper or required theorem it is meant for (write that proof now; a statement over every "
            f"sequence follows from its one-step helper by induction), or leave it out"
            for n in unreached_open(graph, [f"{s.ns}.{t}" for t in s.theorems], info["helpers"])]
    if not bad:   # open helpers that Lean shows false on concrete values
        false = refute.check(s, [short_name(f) for f in an["open"]], f"skeleton:{rnd}")
        bad += [f"`{n}` is false: Lean evaluated it on concrete values and the kernel checked the refutation; "
                f"counterexample {cex}. Replace it with a true statement" for n, cex in false.items()]
    if bad:
        s._save(before, f"revert skeleton {rnd}")
        return reject("Lean's dependency check:\n" + "\n".join(f"- {b}" for b in bad))
    hs = open_helpers(s, an)
    s.targets.update(h["name"] for h in hs)
    for name in list(s.refuted):   # a name reused for another statement is a new helper
        if _norm(statement_of(decl_text(s, name))) != _norm(s.refuted[name]["stmt"]):
            del s.refuted[name]
    rec = {"round": rnd, "source": ctx["source"], "prose": ctx.get("prose", ""), "derived": info["derived"],
           "helpers": [h["name"] for h in hs], "version": s.version}
    ctx["accepted"] = rec
    s.__dict__.setdefault("skeletons", []).append({"round": rnd, "code": code, "helpers": rec["helpers"],
                                                    "derived": rec["derived"], "prose": rec["prose"][:3000]})
    (s.out / f"skeleton_{rnd}.lean").write_text(code)
    s.log(kind="skeleton", round=rnd, source=ctx["source"], attempt=ctx["tries"] + 1, accepted=True,
          derived=info["derived"], hoisted=info["hoisted"], proved=an["proved"],
          helpers={h["name"]: h["users"] for h in hs}, notes=info["notes"], code=code[:8000])
    listing = "\n".join(f"- {h['name']} (used by {len(h['users'])} required theorem(s))" for h in hs)
    return True, (f"SKELETON ACCEPTED (version {s.version}): Lean confirms every required theorem uses sorry only "
                  f"through helper theorems. Open helper theorems, in the order they will be proved:\n{listing}"
                  + ("\nNotes: " + "; ".join(info["notes"]) if info["notes"] else ""))


SKELETON_SYSTEM = """You are a Lean 4 proof architect (Lean v4.35.0 core library only, no Mathlib).
Given a specification, a candidate implementation and the required theorems that are not yet proved,
you write a proof skeleton: helper theorems, each TRUE and small enough for one focused proof, whose
proofs may be left as `sorry`, any definitions they need (invariants, potentials) with complete bodies,
and a proof of every required theorem from them that contains no `sorry` itself. Everything you write
must elaborate against the given file. Avoid Mathlib names (no Finset, no linarith, no BigOperators)."""

TOPDOWN_GUIDANCE = """How to write the skeleton:
- Prove each required theorem in a few lines from named helper theorems. A helper's proof may be `sorry`; every `sorry` must sit inside a helper theorem, because a required theorem whose own proof contains `sorry` is rejected (Lean checks this on the compiled file).
- Every helper you leave as `sorry` must be used by a proof in the skeleton: if a helper follows from other helpers (a statement over every sequence from its one-step helper, by induction), write that proof now instead of `sorry`. An open helper that no required theorem uses is rejected.
- Prefer helpers that several required theorems share. State each helper with its hypotheses as explicit binders (no `variable`, `section` or `namespace`), small enough for one focused proof: one operation, one call or one case where possible.
- A requirement about every sequence of operations or every reachable state follows from facts about one step: an invariant that holds at the start, is preserved by every step and implies the requirement, or, for an upper bound on a quantity that only accumulates, a potential (what was accumulated plus what is still owed) that no step raises by more than what the step adds. Such a reduction can be one helper about every implementation that satisfies the per-step facts, taking them as hypotheses.
- Required theorems that are themselves about single calls are per-step facts: the proof of a required theorem may use the required theorems listed before it. Required theorems stay at the end of the file in the listed order, after every helper, so helpers cannot use them.
- Definitions you introduce need complete bodies. Do not restate declarations that already exist; use them."""

REDUCTION_QUERY = ("statement for every sequence of operations run from per-step hypotheses: invariant preserved "
                   "by each step, potential bound, accumulated total")


def skeleton_hints(s, pending):
    """Library declarations for a skeleton: the best matches of each pending requirement and of
    a fixed query for reduction theorems (per-step hypotheses, conclusion over sequences)."""
    if not s.lib_index:
        return ""
    seen, hits = set(), []
    queries = [obligation_query(s, statement(s, t)) for t in pending] + [REDUCTION_QUERY]
    for q in queries:
        for e in [e for e in s.lib_index.search(q, limit=12) if e["kind"] != "module"][:5]:
            if e["name"] not in seen:
                seen.add(e["name"])
                hits.append(e)
    s.log(kind="library_hints", theorem="skeleton", hits=[e["name"] for e in hits])
    return fin_lib.render(hits, sig_chars=300)


def statement(s, t):
    m = re.search(rf"theorem\s+{re.escape(t)}\s*:[^\n]*", s.read_file(f"{s.task.spec_dir}/Challenge.lean"))
    return m.group(0).replace(" := sorry", "").strip() if m else t


def skeleton_user(s, spec, status, pending, rnd, feedback, for_tools):
    defs = ", ".join(f"`{d}`" for d in s.task.definitions)
    hints = skeleton_hints(s, pending) if s.library else ""
    ask = ("Write the skeleton and submit it with submit_skeleton (use read_file, try_snippet"
           + (" and search_library" if s.library else "") + " as needed). " if for_tools else
           "Reply with (1) a short plan in prose: the shared facts, invariants or potentials and how each required "
           "theorem follows; then (2) exactly one ```lean code block, inserted inside "
           f"`namespace {s.ns}` after the current declarations, containing in dependency order: any `import "
           "ProofForgeFin...` and `open` lines first, new definitions with complete bodies, helper theorems "
           "(`theorem <name> ... := by sorry` unless the proof is immediate), and every required theorem listed "
           "above with exactly its statement and a proof without `sorry`. ")
    return (f"{spec}\n\n=== candidate/Solution.lean (current) ===\n{compact_view(s)}\n\n"
            f"Requirement status: {', '.join(f'{k}={v}' for k, v in status.items())}\n\n"
            "Required theorems not yet proved:\n" + "\n".join(f"- `{statement(s, t)}`" for t in pending) + "\n\n"
            + (f"ProofForgeFin declarations the library index ranks highest for these requirements and for "
               f"reduction theorems (hypotheses about one step, conclusion about every sequence):\n{hints}\n\n"
               if hints else "")
            + TOPDOWN_GUIDANCE + "\n\n"
            + (f"{feedback}\n\n" if feedback else "")
            + "Task: design how these required theorems are proved together, top down. " + ask
            + f"New helper names start with `td{rnd}_` and contain no `?` or `!`. Do not change {defs}. "
            "The harness keeps the skeleton only if the file compiles and Lean confirms that no required theorem "
            "uses `sorry` except through helper theorems; the helpers are then proved one at a time.")


def architecture_prose(replies, limit=3000):
    """The plan passed to the helper dialogs: the prose of the first reply that has any,
    followed by the prose of later replies (corrections after feedback), so a correction never
    replaces the plan."""
    proses = [re.split(r"```lean", r, maxsplit=1)[0].strip() for r in replies]
    proses = [p for p in proses if p]
    if not proses:
        return ""
    plan_, later = proses[0], [p for p in proses[1:] if p != proses[0]]
    tail = "".join(f"\n\nRevision after feedback: {p[:600]}" for p in later)
    return plan_[: max(limit - len(tail), limit // 2)] + tail[:limit // 2]


def structure(s, a, system, spec, rnd, feedback=""):
    """Structure phase: the planner (A2) writes the skeleton, with compiler and dependency
    feedback, up to --skeleton-tries replies; without a planner, or if it fails, the prover
    writes it in a tool dialog (submit_skeleton). Returns the accepted skeleton record or None."""
    status = s.check_status()
    pending = [t for t, v in status.items() if v != "PROVED"]
    ctx = {"round": rnd, "status": status, "pending": pending, "tries": 0, "accepted": None, "source": None}
    s.skeleton_ctx = ctx
    s.log(kind="phase", phase="structure", round=rnd, pending=pending)
    if not pending:
        return None
    last = ""
    if a.planner != "none":
        ctx["source"] = "planner"
        user = skeleton_user(s, spec, status, pending, rnd, feedback, for_tools=False)
        messages = [{"role": "system", "content": SKELETON_SYSTEM}, {"role": "user", "content": user}]
        extra = {} if a.planner_effort == "default" else {"reasoning_effort": a.planner_effort}
        replies = []
        for tries in range(a.skeleton_tries):
            try:
                r, _ = s.call(a.planner, messages, f"skeleton:{s.task.id}:{rnd}:{tries}", timeout=900, **extra)
            except APIError as e:
                s.log(kind="api_error", status=e.status, body=e.body[:300])
                break   # the prover writes the skeleton instead
            text = r["choices"][0]["message"].get("content") or ""
            messages.append({"role": "assistant", "content": text})
            replies.append(text)
            blocks = re.findall(r"```lean\s*\n(.*?)```", text, re.S)
            if not blocks:
                messages.append({"role": "user", "content": "Your reply had no ```lean code block. Reply again in the required format."})
                continue
            ctx["prose"] = architecture_prose(replies)
            ok, msg = accept_skeleton(s, blocks[-1], ctx)
            if ok:
                (s.out / f"skeleton_{rnd}.md").write_text("\n\n".join(replies))
                return ctx["accepted"]
            last = msg
            messages.append({"role": "user", "content": msg + "\n\nReply with the corrected plan and the complete "
                             "corrected code block."})
        if replies:
            (s.out / f"skeleton_{rnd}_rejected.md").write_text("\n\n".join(replies))
    ctx["source"] = "prover"
    user = skeleton_user(s, spec, status, pending, rnd, feedback, for_tools=True)
    if last:
        user += ("\n\nThe architect's last skeleton was rejected:\n" + last[-3000:]
                 + "\nIts plan:\n" + ctx.get("prose", "")[-2000:])
    ok, messages = dialog(s, a.model, a.effort, system, user,
                          {"submit_skeleton", "read_file", "try_snippet"} | lib_tools(s) | goal_tools(s),
                          a.skeleton_turns,
                          lambda: ctx["accepted"] is not None, f"structure{rnd}")
    if ctx["accepted"] is not None:
        ctx["accepted"]["prose"] = architecture_prose([m["content"] for m in messages
                                                       if m["role"] == "assistant" and m.get("content")])
    return ctx["accepted"]


def fill(s, a, system, spec, sk):
    """Fill phase: the open helpers of the compiled candidate (dependency graph) are the
    obligations, in open_helpers() order, each dispatched through resolve() (dialog with
    snippets and library hints, planner decomposition in A2). Rounds repeat until no helper is
    open ("done"), a helper is refuted or every open helper has had --helper-attempts attempts
    ("restructure", with the details), or --fill-rounds is reached ("stalled")."""
    s.log(kind="phase", phase="fill", round=sk["round"])
    attempts = {}
    hs = []
    for rnd in range(a.fill_rounds):
        graph, err = s.dep_graph()
        if graph is None:
            s.log(kind="deps", round=rnd, error=(err or "")[-500:])
            return "stalled", {}
        an = analyze(s, graph)
        hs = open_helpers(s, an)
        s.log(kind="deps", round=rnd, proved=an["proved"], direct=an["direct"],
              open={h["name"]: h["users"] for h in hs})
        if not an["open"] and not an["direct"] and not an["missing"]:
            return "done", {}
        if not hs:   # open declarations the source tools cannot address (or a required theorem lost its proof)
            return "stalled", {"stuck": [], "attempts": attempts}
        refuted = [h for h in hs if h["name"] in s.refuted]
        todo = [h for h in hs if attempts.get(h["name"], 0) < a.helper_attempts and h["name"] not in s.refuted]
        if refuted or not todo:
            return "restructure", {"refuted": [h["name"] for h in refuted], "attempts": attempts,
                                   "stuck": [h for h in hs if h["name"] not in s.refuted and attempts.get(h["name"])]}
        s.log(kind="fill_order", round=rnd, order=[{"name": h["name"], "users": len(h["users"]), "lib": h["lib"],
                                                     "attempts": attempts.get(h["name"], 0)} for h in todo])
        portfolio.close_goals(s, a, [h["name"] for h in todo], f"fill{rnd}")
        for h in todo:
            if own_sorry_free(s, h["name"]):
                continue
            attempts[h["name"]] = attempts.get(h["name"], 0) + 1
            ok = resolve(s, a, system, spec, h["name"], 1, sk.get("prose", ""))
            s.log(kind="helper", name=h["name"], users=h["users"], ok=ok, attempt=attempts[h["name"]],
                  refuted=h["name"] in s.refuted)
            if h["name"] in s.refuted:
                s.refuted[h["name"]]["stmt"] = h["stmt"]
                return "restructure", {"refuted": [h["name"]], "stuck": [], "attempts": attempts}
        prune(s)
    return "stalled", {"stuck": hs, "attempts": attempts}


def restructure_feedback(s, info):
    """What the revised skeleton is told: refuted helpers with their refutations, stuck helpers
    with the end of their failed attempts, and the helpers already proved."""
    lines = ["The previous skeleton did not work out."]
    for name in info.get("refuted", []):
        ref = s.refuted.get(name, {})
        if ref.get("counterexample"):
            lines.append(f"- FALSE: `{ref.get('stmt') or name}`. Counterexample (the kernel checked the refutation): "
                         f"{ref['counterexample'][:800]}")
            continue
        lines.append(f"- FALSE: `{ref.get('stmt') or name}`. Lean accepted this proof of its negation:\n"
                     f"{textwrap_indent(ref.get('proof', '')[:800], '    ')}")
    for h in info.get("stuck", []):
        n = info.get("attempts", {}).get(h["name"], 0)
        lines.append(f"- STUCK after {n} attempt(s): `{h['stmt']}`"
                     + (f"\n  Last attempts:\n{textwrap_indent(notes_text(s, h['name'], 1200), '  ')}" if s.notes.get(h["name"]) else ""))
    proved = [m.group(1).split(".")[-1] for m in s.DECL.finditer(s._source())
              if m.group(1).split(".")[-1] in s.targets and own_sorry_free(s, m.group(1).split(".")[-1])]
    if proved:
        lines.append("Helper theorems already proved (they stay in the file; use them): "
                     + ", ".join(f"`{p}`" for p in proved[:40]))
    lines.append("Write a revised skeleton for the unproved required theorems: replace the false and stuck helpers "
                 "with true statements that are easier to prove, or a different decomposition.")
    return "\n".join(lines)


def topdown_phases(s, a, system, spec):
    """The top-down loop between phase 0 and phase 3: a structure phase, then fill rounds, with
    up to --restructures revised skeletons when a helper is refuted or every open helper is
    stuck. If no skeleton is accepted at all, the run continues with the per-obligation phases
    of the orchestrated loop (structured())."""
    s.extra_tools = {"refute_helper"}
    s.topdown = True
    try:
        status = s.check_status()
        if all(v == "PROVED" for v in status.values()):
            s.check()
            return
        resumed = resumed_skeleton(s) if s.resume_goals else None
        resume_phase(s, a, system, spec, helpers_only=True)
        feedback = ""
        for k in range(a.restructures + 1):
            sk = resumed if (k == 0 and resumed) else structure(s, a, system, spec, k + s.round_offset, feedback)
            if sk is None:
                s.log(kind="phase", phase="structure", round=k, ok=False)
                if k == 0:
                    s.log(kind="phase", phase="obligations", reason="no skeleton accepted")
                    s.extra_tools = set()
                    structured(s, a, system, spec)
                    return
                break
            prune(s)
            outcome, info = fill(s, a, system, spec, sk)
            s.log(kind="fill_end", round=k, outcome=outcome, refuted=info.get("refuted", []),
                  stuck=[h["name"] for h in info.get("stuck", [])])
            if outcome != "restructure" or k == a.restructures:
                break
            feedback = restructure_feedback(s, info)
            s.log(kind="restructure", round=k + 1, refuted=info.get("refuted", []),
                  stuck=[h["name"] for h in info.get("stuck", [])])
        s.check()
    finally:
        s.extra_tools = set()
        s.topdown = False


def resume_phase(s, a, system, spec, helpers_only=False):
    """A resumed run works the goals its prior attempts left open first (helpers, then required
    theorems; helpers only in the top-down loop, whose structure phase handles required theorems):
    the tactic portfolio on all of them in one batch, then one dialog per goal still open, with the
    prior attempts' failure notes in its prompt (prove_target)."""
    goals = [g for g in s.resume_goals if decl_text(s, g) and not own_sorry_free(s, g)
             and not (helpers_only and g in s.theorems)]
    s.resume_goals = [g for g in s.resume_goals if g not in goals]
    if not goals:
        return
    s.log(kind="phase", phase="resume", goals=goals)
    s.targets.update(g for g in goals if g not in s.theorems)
    portfolio.close_goals(s, a, goals, "resume")
    for g in goals:
        if not own_sorry_free(s, g):
            prove_target(s, a, system, spec, g, a.obligation_turns, "resume")


def resumed_skeleton(s):
    """The skeleton a resumed candidate already has: when Lean's dependency graph shows every
    unproved required theorem derived from open helper theorems (no direct `sorry`, nothing
    missing), the fill phase starts on those helpers without a new structure phase."""
    graph, _ = s.dep_graph()
    if graph is None:
        return None
    an = analyze(s, graph)
    hs = open_helpers(s, an)
    if an["direct"] or an["missing"] or not hs:
        return None
    s.targets.update(h["name"] for h in hs)
    prose = "\n\n".join(sk.get("prose", "") for sk in getattr(s, "resumed_skeletons", []) if sk.get("prose"))
    rec = {"round": max(0, s.round_offset - 1), "source": "resumed", "prose": prose[-3000:], "derived": [],
           "helpers": [h["name"] for h in hs], "version": s.version}
    s.log(kind="skeleton", round=rec["round"], source="resumed", attempt=0, accepted=True, derived=[],
          hoisted=[], proved=an["proved"], helpers={h["name"]: h["users"] for h in hs}, notes=[], code="")
    return rec


def topdown(s, a):
    """--loop topdown: phase 0 and phase 3 of the orchestrated loop around topdown_phases()."""
    orchestrate(s, a, middle=topdown_phases)


def library_summary(s):
    """The library arm of a run: off, or on with the version and index the run used."""
    if not s.library:
        return {"enabled": False}
    built = json.loads((fin_lib.ensure_built() / "built.json").read_text())
    return {"enabled": True, "package": fin_lib.PACKAGE, "source_tree_sha256": built["source_tree_sha256"],
            "index_sha256": built["index_sha256"], "index_entries": len(s.lib_index.entries),
            "git_commit": fin_lib.git_commit()}


def finish(s, out, arm, extra):
    """Write summary.json and the final candidate; final judging is done by the evaluator.
    A final file that does not compile is replaced by the newest version that did; this
    selection among already produced versions happens after the deadline."""
    judge.DEADLINE = None
    leanserver.close(s)
    if "error:" in s.compile(2000)["output_tail"] and s.last_good is not None:
        s._save(s.last_good, "restore last compiling version")
    shutil.copy(s.ws / "candidate/Solution.lean", out / "final.lean")
    writes = [e for e in s.events if e.get("kind") == "write"]
    snapshot = {"sha256": taskmod.sha256(out / "final.lean"), "version": s.version,
                "selected": writes[-1]["why"] if writes else "start candidate",
                "written_at_s": round(writes[-1]["t"] - s.events[0]["t"], 1) if writes else 0.0}
    summary = {"task": s.task.id, "arm": arm, "model": s.model, **extra, "final_snapshot": snapshot,
               "accepted_in_session": s.accepted,
               "versions": s.version, "budget": s.budget.summary(), "final_status": s.check_status()}
    rec = getattr(s, "resume_record", None)
    if rec:   # only a resumed run has these fields
        summary["resumed_from"] = [r["run_dir"] for r in rec["ledgers"] if r["used"]]
        summary["resume"] = rec
    (out / "summary.json").write_text(json.dumps(summary, indent=2))
    try:
        led = ledger.write(s, out, arm, summary)
        print(f"ledger: {len(led['proved'])} proved declarations, {len(led['open_goals'])} open goals", flush=True)
    except Exception as e:   # the summary and final candidate stand without it
        print(f"ledger not written: {e!r}", flush=True)
    shutil.rmtree(s.ws, ignore_errors=True)
    return summary


def parser():
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", help="task id or directory (default: flagship)")
    ap.add_argument("--model", default="muse-spark-1.3-contributor")
    ap.add_argument("--mode", default="repair", choices=["repair", "implement", "orchestrated", "free"],
                    help="repair (default): start from the task's buggy candidate with its issue report; "
                         "implement: start from a stub generated from the locked challenge and implement "
                         "the definitions from the spec. 'orchestrated' and 'free' are kept for "
                         "compatibility and mean --mode repair with that --loop")
    ap.add_argument("--loop", default="orchestrated", choices=["orchestrated", "free", "topdown"],
                    help="orchestrated (default): obligations in listed order, then planner rounds; free: one "
                         "dialog; topdown: a proof skeleton checked by Lean, then its open helpers")
    ap.add_argument("--max-turns", type=int, default=40, help="free mode only")
    ap.add_argument("--skeleton-tries", type=int, default=3,
                    help="topdown: planner replies per structure phase (compiler and dependency feedback between them)")
    ap.add_argument("--skeleton-turns", type=int, default=12,
                    help="topdown: turns of the prover's structure dialog (A1, or when the planner fails)")
    ap.add_argument("--helper-attempts", type=int, default=2,
                    help="topdown: resolutions of one open helper before it counts as stuck")
    ap.add_argument("--fill-rounds", type=int, default=6, help="topdown: fill rounds per skeleton")
    ap.add_argument("--restructures", type=int, default=2,
                    help="topdown: revised skeletons after a refuted helper or when every open helper is stuck")
    ap.add_argument("--phase0-turns", type=int, default=12)
    ap.add_argument("--obligation-turns", type=int, default=12)
    ap.add_argument("--start", help="starting candidate (default: the task's candidate/Solution.lean)")
    ap.add_argument("--effort", default="medium", choices=["low", "medium", "high", "default"])
    ap.add_argument("--planner", default="muse-wonder-1.0", help="planner model, or 'none' (arm A1)")
    ap.add_argument("--planner-effort", default="high", choices=["low", "medium", "high", "default"])
    ap.add_argument("--max-depth", type=int, default=2)
    ap.add_argument("--rounds", type=int, default=3, help="phase 2 rounds while they make progress")
    ap.add_argument("--budget-usd", type=float, help="cap at standard-tier list prices")
    ap.add_argument("--budget-wall", type=float, help="wall-clock cap in seconds")
    ap.add_argument("--out", help="run directory (default: runs/repair-<time>-<task>-<arm>)")
    ap.add_argument("--library", default="on", choices=["on", "off"],
                    help="on (default): ProofForgeFin in the workspace, its index in the prompt, search_library and "
                         "add_import; off: the harness without the library")
    ap.add_argument("--resume-from", help="comma-separated run directories (or ledger.json files) of prior attempts on "
                                          "the same task and locked spec: start from their best candidate and their "
                                          "proved declarations (re-checked by Lean), open goals first")
    ap.add_argument("--portfolio", default="on", choices=["on", "off"],
                    help="on (default): try a fixed list of Lean tactics on an open goal before a model turn")
    ap.add_argument("--portfolio-heartbeats", type=int, default=portfolio.HEARTBEATS,
                    help="per-tactic limit of the portfolio, in Lean maxHeartbeats units")
    ap.add_argument("--portfolio-seconds", type=float, default=portfolio.SECONDS,
                    help="wall allowance per portfolio attempt; a batch is stopped after 60 s plus this per attempt")
    ap.add_argument("--goal-tool", default="on", choices=["on", "off"],
                    help="on (default): a persistent Lean server per session for goal_at and the fast check of "
                         "try_snippet; off: every check compiles")
    ap.add_argument("--refute", default="on", choices=["on", "off"],
                    help="on (default): evaluate new helper statements on concrete values and refuse false ones")
    ap.add_argument("--refute-samples", type=int, default=refute.SAMPLES, help="instances per statement")
    ap.add_argument("--variants", type=int, default=variants.DEFAULT_K,
                    help="parallel short variants for a goal still open after its first dialog (0: off)")
    ap.add_argument("--variant-turns", type=int, default=variants.TURNS, help="turns of each variant")
    return ap


def configure(s, a):
    """Session switches of the goal tool, refutation and variants from the options."""
    s.goal_tool = getattr(a, "goal_tool", "on") != "off"
    s.refute_samples = (getattr(a, "refute_samples", refute.SAMPLES) or refute.SAMPLES) \
        if getattr(a, "refute", "on") != "off" else 0
    s.variants_k = variants.settings(a)[0]


def features_summary(s, a):
    """The summary.json records of the tactic portfolio and the three feedback features."""
    return {"portfolio": {"enabled": a.portfolio == "on", "heartbeats": a.portfolio_heartbeats,
                          "seconds": a.portfolio_seconds, **portfolio.summary(s)},
            "goal_tool": leanserver.summary(s, a), "refute": refute.summary(s, a), "variants": variants.summary(s, a)}


def resume_setup(s, a, priors, record):
    """Start a session from prior attempts: their best candidate (re-checked by Lean, unless
    --start names one), their proved declarations that still compile, their open goals and failure
    notes, and new-name offsets. Recorded in summary.json as `resume`."""
    rec = {"ledgers": record, "base": None, "carried": [], "dropped": [], "goals": []}
    s.resume_record = rec
    s.log(kind="resume", ledgers=record)
    if not a.start:
        base = ledger.best_base(s, priors)
        rec["base"] = base and {k: v for k, v in base.items() if k != "text"}
    rec["carried"], dropped = ledger.carry(s, priors)
    rec["dropped"] = dropped[:200]
    s.prior_notes = ledger.notes_by_goal(priors)
    s.resume_goals = ledger.resume_goals(s, priors)
    s.round_offset, s.plan_count = ledger.round_offset(priors)
    s.resumed_skeletons = [sk for led in priors for sk in led.get("skeletons", [])]
    rec["goals"] = list(s.resume_goals)
    print(f"[resume] base {rec['base'] and rec['base']['run_dir']}, carried {len(rec['carried'])}, "
          f"dropped {len(dropped)}, open goals {rec['goals']}", flush=True)


def load_priors(ap, a, task):
    """The usable ledgers of --resume-from, or exit when none is usable."""
    if not a.resume_from:
        return [], []
    priors, record = ledger.load_many([x.strip() for x in a.resume_from.split(",")], task)
    for r in record:
        print(f"[resume] {r['path']}: " + ("used" if r["used"] else f"refused ({r['refused']})"), flush=True)
    if not priors:
        ap.error("--resume-from: no usable prior attempt: " + "; ".join(f"{r['path']}: {r['refused']}" for r in record))
    return priors, record


def main():
    ap = parser()
    a = ap.parse_args()
    if a.mode in ("orchestrated", "free"):
        a.loop, a.mode = a.mode, "repair"
    if a.mode == "implement" and a.start:
        ap.error("--start cannot be combined with --mode implement (the start is generated)")
    task = taskmod.load(a.task)
    priors, record = load_priors(ap, a, task)
    arm = "A1" if a.planner == "none" else "A2"
    kind = "implement" if a.mode == "implement" else "repair"
    out = pathlib.Path(a.out) if a.out else \
        ROOT / "runs" / f"{kind}-{time.strftime('%Y%m%d-%H%M%S')}-{task.id}-{arm}"
    out.mkdir(parents=True, exist_ok=True)
    start = a.start or task.start
    if a.mode == "implement":
        start = out / "start.lean"
        start.write_text(stub_candidate(task))
    s = Session(task, a.model, start, out, Budget(a.budget_usd, a.budget_wall), mode=a.mode,
                library=a.library == "on")
    configure(s, a)
    s.log(kind="start", arm=arm, **vars(a))
    try:
        if priors:
            resume_setup(s, a, priors, record)
        if a.loop == "orchestrated":
            orchestrate(s, a)
        elif a.loop == "topdown":
            topdown(s, a)
        else:
            status = s.check_status()
            portfolio.close_goals(s, a, [t for t, v in status.items() if v != "PROVED"], "free")
            dialog(s, a.model, a.effort, system_prompt(s),
                   "Begin. The current candidate is candidate/Solution.lean."
                   + (f"\n\nPrevious attempts on this task ended as follows; do not repeat what failed:\n"
                      f"{ledger.summary_text(priors)}" if priors else ""),
                   {t["function"]["name"] for t in tools_for(task, s.library)} | goal_tools(s), a.max_turns,
                   lambda: s.accepted, "free")
    except BudgetExceeded as e:
        s.log(kind="budget_stop", reason=str(e))
        print(f"budget exhausted: {e}", flush=True)
    variants.join(s)
    summary = finish(s, out, arm, {"mode": a.loop, "task_mode": a.mode, "effort": a.effort, "planner": a.planner,
                                   "library": library_summary(s), **features_summary(s, a)})
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
