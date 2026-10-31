#!/usr/bin/env python3
"""Specification strength gate: how many plausible wrong implementations a locked specification
rejects, and with what evidence.

A proof is only as strong as the statement it proves. This tool measures the statements: it
mutates a task's reference implementation (the hidden known-good solution under `reference/`),
compiles every mutant in the judge image, and decides for each one whether the specification
rejects it.

Pipeline for one task:

  1. Proof stripping. The first reference solution (sorted by file name) has every `theorem`,
     `lemma` and `example` body replaced by `sorry`. Definitions, instances and structures are
     kept byte for byte, so the stripped reference computes exactly what the reference computes.
     It must build and pass the property tests (the baseline); otherwise the task is reported as
     unsupported.
  2. Mutation. Lean-source mutation operators (OPERATORS below) are applied to the bodies of the
     definitions reachable from the task's definition holes: rounding direction, comparison
     boundaries, arithmetic operators, dropped guards and conjuncts, state field updates,
     swapped arguments and constants. Each mutant differs from the stripped reference at exactly
     one site. Mutant generation is deterministic; `--max-mutants` selects a deterministic,
     operator-stratified subset.
  3. Compilation. All mutants are built sequentially in one container of the judge image
     (`lake build <exe>`, LEAN_NUM_THREADS and the container CPU count bounded). Mutants that
     do not compile are discarded and counted.
  4. Property tests. Each compiled mutant whose executable differs from the reference's runs the
     task's property tests with the judge's own harness (`binary_check.property_tests`, the same
     2,001 cases and seed as a Passport). A mutant with a violation is killed. A mutant that
     passes runs a further `--extended-cases` cases with another seed; a violation there kills
     it too (recorded separately). A mutant whose executable is byte-identical to the reference's
     is equivalent.
  5. Kernel-checked counterexamples. For each killed mutant of a task with a counterexample
     adapter (`harness/counterexample.py`), the witnesses of the property tests become Lean
     refutations `cex_<req> : ¬ (<locked statement>)` about the mutant's definitions, checked
     with `lake comparator --paranoid` (six kernels), `leanchecker` and the axiom audit, exactly
     as the counterexample stage of a Passport does. Requirements without a kernel-checked
     refutation yet are tried first; one accepted refutation per mutant is enough.
  6. Classification of survivors. A surviving mutant whose outputs equal the reference's on
     every standard and extended case is "survived, no observed difference" (possibly
     equivalent; equivalence is not proved). A surviving mutant whose outputs differ on some
     case that the property tests accept is "survived, behaviour differs": the specification
     (or the oracle that mirrors it) admits a behaviour the reference does not have. These are
     the candidates for specification gaps, listed with their diff and the first differing case.
  7. Vacuity checks. For every requirement: the number of mutants whose executable violates it
     and the number of kernel-checked refutations of it (each one proves the requirement is not
     trivially true). The conjunction is satisfiable: the task's references are accepted by the
     judge (validation.json) and the stripped reference passes the property tests here.

The report is a JSON document with a content hash (`report_sha256`, the SHA-256 of the
canonical JSON of every other field), plus a Markdown rendering. `passport_record(report)` is the
optional `spec_strength` field designed for Passports; `verify_report` and
`verify_passport_record` check a report and a record without running Lean (docs/SPEC_STRENGTH.md).

Usage:
  spec_strength.py --task T [--out DIR] [--max-mutants N] [--cases 2000] [--seed 0]
                   [--extended-cases 10000] [--extended-seed 1] [--no-counterexample]
  spec_strength.py --task T --list            (generate and list mutants, no Lean)
  spec_strength.py --verify report.json       (hash, lock and mutant regeneration check)

No model is called. Containers run sequentially per task; at most `PF_SPEC_SLOTS` (default 2)
containers of this tool run at once on the host, in slots separate from the judge's.
"""
import argparse, difflib, hashlib, json, os, pathlib, random, re, shutil, subprocess, sys, tempfile, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import binary_check, counterexample as cexmod, judge, lock, task as taskmod  # noqa: E402

SCHEMA = 1
ROOT = taskmod.ROOT
THREADS = int(os.environ.get("PF_SPEC_LEAN_THREADS", "4"))
SLOTS = int(os.environ.get("PF_SPEC_SLOTS", "2"))
SLOT_DIR = pathlib.Path(tempfile.gettempdir()) / "proofforge-spec-strength-slots"
TOOL_SHA256 = taskmod.sha256(pathlib.Path(__file__))   # the code this process runs
BUILD_TIMEOUT = 300          # seconds per mutant build
TEST_TIMEOUT = 300           # seconds per property-test run of one mutant

# Tokenizer.

SYMBOLS = sorted([
    "<;>", ":=", "=>", "<=", ">=", "==", "!=", "&&", "||", "->", "<-", "++", "::", "<|>", "<|", "|>.", "|>",
    "<<<", ">>>", "^^^", "&&&", "|||", "..", "⁻¹",
], key=len, reverse=True)
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"
_IDENT_START = r"A-Za-z_À-ɏΑ-Ωα-κμ-ωἀ-῿℀-⅏"
_IDENT_REST = _IDENT_START + r"0-9'!?₀-ₜᵢ-ᵪ"
_IDENT_PART = rf"(?:[{_IDENT_START}][{_IDENT_REST}]*|«[^»]*»)"
IDENT_RE = re.compile(rf"{_IDENT_PART}(?:\.(?:{_IDENT_PART}|\d+))*")
NUM_RE = re.compile(r"0x[0-9a-fA-F_]+|0b[01_]+|\d[\d_]*")
KEYWORDS = {
    "if", "then", "else", "match", "with", "fun", "let", "have", "show", "from", "at", "by", "do",
    "return", "in", "where", "for", "unless", "mut", "calc", "termination_by", "decreasing_by",
    "deriving", "instance", "def", "theorem", "lemma", "abbrev", "structure", "inductive", "class",
    "namespace", "end", "open", "section", "variable", "example", "sorry", "Type", "Prop", "Sort",
    "private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "mutual", "opaque", "axiom",
    "true", "false", "True", "False", "decide", "this",
}
DECL_KW = {"def", "theorem", "lemma", "abbrev", "instance", "structure", "inductive", "class", "example",
           "opaque", "axiom"}
MODIFIERS = {"private", "protected", "noncomputable", "partial", "unsafe", "nonrec"}
PROOF_KW = {"theorem", "lemma", "example"}
CODE_KW = {"def", "abbrev", "instance"}


class Tok:
    __slots__ = ("kind", "text", "start", "end", "col", "depth", "nl", "indent")

    def __init__(self, kind, text, start, end, col, nl):
        self.kind, self.text, self.start, self.end, self.col, self.nl, self.depth = kind, text, start, end, col, nl, 0
        self.indent = col

    def __repr__(self):
        return f"Tok({self.kind},{self.text!r},{self.start})"


def tokenize(text):
    """Lean source to tokens (whitespace dropped, comments kept as `comment` tokens). Each token
    records its column, whether a line break precedes it, and its bracket depth."""
    toks, i, n, line_start, nl = [], 0, len(text), 0, True

    def push(kind, j):
        nonlocal nl
        toks.append(Tok(kind, text[i:j], i, j, i - line_start, nl))
        nl = False

    while i < n:
        c = text[i]
        if c == "\n":
            i += 1
            line_start, nl = i, True
            continue
        if c.isspace():
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
        elif text.startswith("/-", i):
            lvl, j = 1, i + 2
            while j < n and lvl:
                if text.startswith("/-", j):
                    lvl, j = lvl + 1, j + 2
                elif text.startswith("-/", j):
                    lvl, j = lvl - 1, j + 2
                else:
                    j += 1
        else:
            j = None
        if j is not None:
            push("comment", j)
            if "\n" in text[i:j]:
                line_start = text.rfind("\n", i, j) + 1
            i = j
            continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            push("string", j + 1)
            i = j + 1
            continue
        if c == "'" and (i == 0 or not re.match(rf"[{_IDENT_REST}]", text[i - 1])):
            m = re.match(r"'(?:[^'\\]|\\.)'", text[i:])
            if m:
                push("char", i + m.end())
                i += m.end()
                continue
        m = NUM_RE.match(text, i) if c.isdigit() else None
        if m:
            push("num", m.end())
            i = m.end()
            continue
        m = IDENT_RE.match(text, i)
        if m:
            push("ident", m.end())
            i = m.end()
            continue
        sym = next((s for s in SYMBOLS if text.startswith(s, i)), c)
        push("sym", i + len(sym))
        i += len(sym)
    d, indent = 0, 0
    for t in toks:
        if t.nl:
            indent = t.col
        t.indent = indent
        if t.kind == "sym" and t.text in OPEN:
            t.depth = d
            d += 1
        elif t.kind == "sym" and t.text in CLOSE:
            d -= 1
            t.depth = d
        else:
            t.depth = d
    return toks


# Declarations.

class Decl:
    def __init__(self, kind, name, toks, start, end):
        self.kind, self.name, self.toks, self.start, self.end = kind, name, toks, start, end
        self.body = body_index(toks) if kind in DECL_KW else None

    def code(self):
        """Non-comment tokens."""
        return [t for t in self.toks if t.kind != "comment"]

    def __repr__(self):
        return f"Decl({self.kind},{self.name})"


def body_index(toks):
    """Index (into the decl's non-comment tokens) of the token that starts the body: the first
    `:=` or `where` at the declaration's bracket depth, or the first `|` that begins a line."""
    code = [t for t in toks if t.kind != "comment"]
    if not code:
        return None
    base, pending = code[0].depth, 0
    for k, t in enumerate(code[1:], 1):
        if t.depth != base:
            continue
        if t.text in ("let", "have"):      # a `let x := v` inside the statement
            pending += 1
        elif t.text == ":=" and pending:
            pending -= 1
        elif t.text in (":=", "where"):
            return k
        if t.text == "|" and t.nl:
            return k
    return None


def declarations(text):
    """Split a Lean file into top-level commands: a command starts at a token in column 0 that is
    not a line comment. Returns Decl objects with kind (`def`, `theorem`, ..., `comment` or
    `other`), name and token range."""
    toks = tokenize(text)
    starts = [k for k, t in enumerate(toks) if t.col == 0 and not t.text.startswith("--")]
    out = []
    for a, b in zip(starts, starts[1:] + [len(toks)]):
        seg = toks[a:b]
        head = seg[0]
        start, end = head.start, (toks[b].start if b < len(toks) else len(text))
        if head.kind == "comment":
            out.append(Decl("comment", None, seg, start, end))
            continue
        k = 0
        if head.text == "@" and len(seg) > 1 and seg[1].text == "[":
            k = 2
            while k < len(seg) and not (seg[k].text == "]" and seg[k].depth == head.depth):
                k += 1
            k += 1
        while k < len(seg) and seg[k].text in MODIFIERS:
            k += 1
        kind = seg[k].text if k < len(seg) and seg[k].text in DECL_KW else "other"
        name = None
        if kind != "other" and k + 1 < len(seg) and seg[k + 1].kind == "ident":
            name = seg[k + 1].text
        out.append(Decl(kind, name, seg, start, end))
    return out


def strip_proofs(text):
    """Replace the body of every theorem, lemma and example by `sorry`; keep everything else."""
    edits = []
    for d in declarations(text):
        if d.kind not in PROOF_KW or d.body is None:
            continue
        code = d.code()
        b = code[d.body]
        last = code[-1]
        edits.append((b.start, last.end, ":= sorry"))
    for s, e, r in sorted(edits, reverse=True):
        text = text[:s] + r + text[e:]
    return text


def short(name):
    return name.split(".")[-1] if name else name


def reachable(decls, roots):
    """Names of code declarations reachable from `roots` through identifier references."""
    code = {short(d.name): d for d in decls if d.kind in CODE_KW | {"structure"} and d.name}
    seen, todo = set(), [r for r in roots if r in code]
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        for t in code[n].code():
            if t.kind == "ident":
                for part in t.text.split("."):
                    if part in code and part not in seen:
                        todo.append(part)
    return seen


# Mutation operators.

OPERATORS = {
    "rounding": "floor and ceiling division swapped; Down/Up and floor/ceil helpers swapped",
    "boundary": "comparison boundary moved (< and <=, > and >=)",
    "equality": "equality test negated (= and !=)",
    "arith": "arithmetic operator swapped (+ and -, * to /), unary minus dropped",
    "logic": "boolean connective swapped (&& and ||, and and or), boolean literal flipped",
    "drop-conjunct": "one conjunct of a guard replaced by true",
    "guard": "if-condition replaced by true or false (guard dropped or branch removed)",
    "field": "state field update dropped, or a field read replaced by another field of the same value",
    "swap": "arguments swapped (non-commutative operator operands, adjacent function arguments, min and max)",
    "constant": "numeric constant changed (n+1, n-1, n*10, n/10)",
}
OP_ORDER = list(OPERATORS)

CEIL_HELPER = """
/-- Inserted by harness/spec_strength.py for a rounding mutant: ceiling division. -/
class PfCeilDiv (α : Type) where
  cdiv : α → α → α
instance : PfCeilDiv Nat := ⟨fun a b => (a + b - 1) / b⟩
instance : PfCeilDiv Int := ⟨fun a b => -((-a) / b)⟩
infixl:70 " ⌈/⌉ " => PfCeilDiv.cdiv
"""

REL_SWAP = {"<": "≤", "≤": "<", ">": "≥", "≥": ">", "<=": "<", ">=": ">"}
EQ_SWAP = {"=": "≠", "≠": "=", "==": "!=", "!=": "=="}
ARITH_SWAP = {"+": "-", "-": "+", "*": "/"}
LOGIC_SWAP = {"&&": "||", "||": "&&", "∧": "∨", "∨": "∧", "true": "false", "false": "true"}
UPDOWN = [("Down", "Up"), ("Up", "Down"), ("down", "up"), ("up", "down"), ("Floor", "Ceil"), ("Ceil", "Floor"),
          ("floor", "ceil"), ("ceil", "floor")]
NONCOMM = {"-", "/", "%", "<", "≤", ">", "≥", "<=", ">=", "^"}
BOUNDARY_FWD = {"&&", "∧", "||", "∨", "then", "else", ":=", ",", "with", "|", "=>", "do", "if", "fun", "let",
                "match", "in", ";", "↔", "→"}
BOUNDARY_BWD = BOUNDARY_FWD | {"return"}


class Site:
    __slots__ = ("op", "start", "end", "repl", "desc", "decl", "helper")

    def __init__(self, op, start, end, repl, desc, decl, helper=False):
        self.op, self.start, self.end, self.repl, self.desc, self.decl, self.helper = \
            op, start, end, repl, desc, decl, helper


def _is_operand_end(t):
    return t.kind in ("ident", "num", "string", "char") and t.text not in KEYWORDS - {"true", "false", "this"} \
        or (t.kind == "sym" and t.text in CLOSE)


def _is_atom_start(t):
    return (t.kind in ("ident", "num") and t.text not in KEYWORDS) or (t.kind == "sym" and t.text in "(⟨")


def _new_line(t, head):
    """`t` starts a line no deeper than the line of `head`: it cannot continue an application."""
    return t.nl and t.col <= head.indent


def _group_end(code, k):
    """Index of the token that closes the bracket opened at code[k]."""
    d = code[k].depth
    for j in range(k + 1, len(code)):
        if code[j].kind == "sym" and code[j].text in CLOSE and code[j].depth == d:
            return j
    return None


def _group_start(code, k):
    d = code[k].depth
    for j in range(k - 1, -1, -1):
        if code[j].kind == "sym" and code[j].text in OPEN and code[j].depth == d:
            return j
    return None


def _projection_at(code, k):
    """True when code[k] is `.` directly after a closing bracket and directly before a field."""
    return (0 < k < len(code) - 1 and code[k].text == "." and code[k - 1].end == code[k].start
            and code[k - 1].text in CLOSE and code[k + 1].start == code[k].end and code[k + 1].kind in ("ident", "num"))


def _atom_after(code, k):
    """(first, last) token indices of the atom starting at code[k], or None. A bracketed group
    includes its projections, as in `(s.acct u).e`."""
    if k >= len(code) or not _is_atom_start(code[k]):
        return None
    if code[k].kind == "sym":
        e = _group_end(code, k)
        if e is None:
            return None
        while e + 2 < len(code) and _projection_at(code, e + 1):
            e += 2
        return (k, e)
    return (k, k)


def _atom_before(code, k):
    """(first, last) of the atom ending at code[k], or None."""
    if k < 0:
        return None
    t = code[k]
    if t.kind in ("ident", "num") and k >= 2 and _projection_at(code, k - 1):
        r = _atom_before(code, k - 2)
        return None if r is None else (r[0], k)
    if t.kind in ("ident", "num") and t.text not in KEYWORDS:
        return (k, k)
    if t.kind == "sym" and t.text in ")⟩":
        s = _group_start(code, k)
        return None if s is None else (s, k)
    return None


def _operand_fwd(code, k, stop_at_line_start=False):
    """Right operand of the connective at code[k]: tokens up to the next boundary at its depth."""
    d = code[k].depth
    j = k + 1
    while j < len(code):
        t = code[j]
        if t.depth < d or (t.depth == d and t.text in BOUNDARY_FWD):
            break
        j += 1
    return (k + 1, j - 1) if j - 1 >= k + 1 else None


def _operand_bwd(code, k, lo):
    d = code[k].depth
    j = k - 1
    while j >= lo:
        t = code[j]
        if t.depth < d or (t.depth == d and t.text in BOUNDARY_BWD):
            break
        j -= 1
    return (j + 1, k - 1) if k - 1 >= j + 1 else None


def sites(text, task, defined_names=()):
    """Every mutation site in the bodies of the code declarations reachable from the task's
    definition holes, in source order."""
    decls = declarations(text)
    keep = reachable(decls, [short(d) for d in task.definitions])
    out = []
    names_all = set(defined_names) | {short(d.name) for d in decls if d.name}
    for d in decls:
        if d.kind not in CODE_KW or d.body is None:
            continue
        if d.kind != "instance" and short(d.name) not in keep:
            continue
        code = d.code()
        body = code[d.body:]
        lo = d.body
        label = d.name or f"instance@{line_of(text, d.start)}"

        def add(op, s, e, repl, desc, helper=False):
            out.append(Site(op, s, e, repl, desc, label, helper))

        # field reads x.f per base
        fields = {}
        for t in body:
            if t.kind == "ident" and "." in t.text:
                base, f = t.text.rsplit(".", 1)
                if re.fullmatch(r"[a-z_][\w']*", f):
                    fields.setdefault(base, [])
                    if f not in fields[base]:
                        fields[base].append(f)
        for j in range(lo, len(code)):
            if _projection_at(code, j) and code[j + 1].kind == "ident":
                fields.setdefault("()", [])
                if code[j + 1].text not in fields["()"]:
                    fields["()"].append(code[j + 1].text)
        tactic = tactic_tokens(code, lo)
        for idx in range(lo, len(code)):
            if idx in tactic:
                continue
            t = code[idx]
            prev = code[idx - 1] if idx > 0 else None
            nxt = code[idx + 1] if idx + 1 < len(code) else None
            tx = t.text
            if t.kind == "sym":
                if tx == "/" and prev is not None and _is_operand_end(prev) and idx > lo:
                    add("rounding", t.start, t.end, "⌈/⌉", "floor division `/` replaced by ceiling division", True)
                if tx in REL_SWAP:
                    add("boundary", t.start, t.end, REL_SWAP[tx], f"`{tx}` replaced by `{REL_SWAP[tx]}`")
                if tx in EQ_SWAP:
                    add("equality", t.start, t.end, EQ_SWAP[tx], f"`{tx}` replaced by `{EQ_SWAP[tx]}`")
                binary = prev is not None and _is_operand_end(prev) and idx > lo
                if tx in ARITH_SWAP and binary:
                    add("arith", t.start, t.end, ARITH_SWAP[tx], f"`{tx}` replaced by `{ARITH_SWAP[tx]}`")
                if tx == "-" and not binary and nxt is not None and _is_atom_start(nxt):
                    add("arith", t.start, t.end, "", "unary minus dropped")
                if tx in LOGIC_SWAP:
                    add("logic", t.start, t.end, LOGIC_SWAP[tx], f"`{tx}` replaced by `{LOGIC_SWAP[tx]}`")
                if tx in ("&&", "∧"):
                    lit = "true" if tx == "&&" else "True"
                    for rng in (_operand_bwd(code, idx, lo), _operand_fwd(code, idx)):
                        if rng:
                            a, b = code[rng[0]], code[rng[1]]
                            add("drop-conjunct", a.start, b.end, lit,
                                f"conjunct `{_snip(text[a.start:b.end])}` replaced by `{lit}`")
                if tx in NONCOMM and binary:
                    left, right = _atom_before(code, idx - 1), _atom_after(code, idx + 1)
                    if left and right and left[0] > lo:
                        before = code[left[0] - 1]
                        after = code[right[1] + 1] if right[1] + 1 < len(code) else None
                        if not _is_operand_end(before) and not (after and _is_atom_start(after) and after.depth == t.depth
                                                                and not _new_line(after, t)):
                            ls, le = code[left[0]].start, code[left[1]].end
                            rs, re_ = code[right[0]].start, code[right[1]].end
                            lt, rt = text[ls:le], text[rs:re_]
                            if lt != rt:
                                add("swap", ls, re_, rt + text[le:rs] + lt, f"operands of `{tx}` swapped")
                if tx == "{":
                    out.extend(_field_drops(text, code, idx, label))
            elif t.kind == "ident":
                if tx in LOGIC_SWAP:
                    add("logic", t.start, t.end, LOGIC_SWAP[tx], f"`{tx}` replaced by `{LOGIC_SWAP[tx]}`")
                if tx == "if":
                    s = idx + 1
                    if s + 1 < len(code) and code[s].kind == "ident" and code[s + 1].text == ":":
                        s += 2
                    e = s
                    while e < len(code) and not (code[e].text == "then" and code[e].depth == t.depth):
                        e += 1
                    if e < len(code) and e > s:
                        a, b = code[s], code[e - 1]
                        cond = _snip(text[a.start:b.end])
                        add("guard", a.start, b.end, "true", f"condition `{cond}` replaced by `true`")
                        add("guard", a.start, b.end, "false", f"condition `{cond}` replaced by `false`")
                last = tx.split(".")[-1]
                for x, y in UPDOWN:
                    if last.endswith(x):
                        cand = last[: -len(x)] + y
                        if cand in names_all:
                            new = tx[: len(tx) - len(last)] + cand
                            add("rounding", t.start, t.end, new, f"`{tx}` replaced by `{new}`")
                if last in ("min", "max"):
                    other = "max" if last == "min" else "min"
                    add("swap", t.start, t.end, tx[: -3] + other, f"`{tx}` replaced by `{tx[:-3] + other}`")
                if "." in tx:
                    base, f = tx.rsplit(".", 1)
                    for g in fields.get(base, []):
                        if g != f:
                            add("field", t.start, t.end, f"{base}.{g}", f"field read `{tx}` replaced by `{base}.{g}`")
                if idx >= 1 and _projection_at(code, idx - 1):
                    for g in fields.get("()", []):
                        if g != tx:
                            add("field", t.start, t.end, g, f"projection `.{tx}` replaced by `.{g}`")
                # adjacent function arguments: f a b -> f b a
                if tx not in KEYWORDS and (prev is None or not _is_operand_end(prev) or idx == lo
                                           or _new_line(t, prev)):
                    args, j = [], idx + 1
                    while True:
                        at = _atom_after(code, j)
                        if not at or code[at[0]].depth != t.depth or _new_line(code[at[0]], t):
                            break
                        args.append(at)
                        j = at[1] + 1
                    for (a1, b1), (a2, b2) in zip(args, args[1:]):
                        s1, e1, s2, e2 = code[a1].start, code[b1].end, code[a2].start, code[b2].end
                        x1, x2 = text[s1:e1], text[s2:e2]
                        if x1 != x2:
                            add("swap", s1, e2, x2 + text[e1:s2] + x1,
                                f"arguments `{_snip(x1)}` and `{_snip(x2)}` of `{tx}` swapped")
            elif t.kind == "num":
                if prev is not None and prev.text == ".":
                    continue
                v = int(tx.replace("_", ""), 0)
                alts = [v + 1] + ([v - 1] if v > 0 else []) + ([v * 10, v // 10] if v >= 10 else [])
                for w in dict.fromkeys(alts):
                    add("constant", t.start, t.end, str(w), f"constant `{tx}` replaced by `{w}`")
        # rounding: ceiling idioms to floor
        btext_start = code[lo].start
        btext = text[btext_start:code[-1].end]
        for m in re.finditer(r"\(([^()]+?) \+ ([\w.]+) - 1\) / ([\w.]+)", btext):
            if m.group(2) == m.group(3):
                add("rounding", btext_start + m.start(), btext_start + m.end(), f"({m.group(1)}) / {m.group(3)}",
                    "ceiling division idiom `(a + b - 1) / b` replaced by floor division")
        for m in re.finditer(r"\(([^()]+?) - 1\) / ([\w.]+) \+ 1", btext):
            add("rounding", btext_start + m.start(), btext_start + m.end(), f"({m.group(1)}) / {m.group(2)}",
                "ceiling division idiom `(a - 1) / b + 1` replaced by floor division")
    return out


def tactic_tokens(code, lo):
    """Indices of tokens inside `by` blocks (proofs inside code: they are not mutated). A block
    runs from `by` to the end of its bracket group, the next comma at its depth, or the end of
    the declaration."""
    out, k = set(), lo
    while k < len(code):
        if code[k].text == "by":
            d, j = code[k].depth, k
            while j < len(code) and not (code[j].depth < d or (code[j].depth == d and code[j].text == "," and j > k)):
                out.add(j)
                j += 1
            k = j
        else:
            k += 1
    return out


def _field_drops(text, code, k, label):
    """Sites removing one `f := v` from a structure update `{ s with f := v, ... }`."""
    d = code[k].depth + 1
    e = _group_end(code, k)
    if e is None:
        return []
    w = next((j for j in range(k + 1, e) if code[j].text == "with" and code[j].depth == d), None)
    if w is None:
        return []
    parts, cur = [], [w + 1]
    for j in range(w + 1, e):
        if code[j].text == "," and code[j].depth == d:
            cur.append(j - 1)
            parts.append(tuple(cur))
            cur = [j + 1]
    cur.append(e - 1)
    parts.append(tuple(cur))
    parts = [(a, b) for a, b in parts if b >= a and any(code[x].text == ":=" for x in range(a, b + 1))]
    out = []
    for i, (a, b) in enumerate(parts):
        fname = code[a].text
        if len(parts) == 1:
            s, en = code[a].start, code[b].end
        elif i + 1 < len(parts):
            s, en = code[a].start, code[parts[i + 1][0]].start
        else:
            s, en = code[parts[i - 1][1]].end, code[b].end
        out.append(Site("field", s, en, "", f"update of field `{fname}` dropped", label))
    return out


def _snip(s, n=60):
    s = re.sub(r"\s+", " ", s).strip()
    return s if len(s) <= n else s[: n - 3] + "..."


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def apply(text, site):
    out = text[:site.start] + site.repl + text[site.end:]
    if site.helper:
        out = insert_helper(out)
    return out


def insert_helper(text):
    """Put the ceiling-division helper after the import block."""
    lines = text.split("\n")
    k = max((i for i, l in enumerate(lines) if l.startswith("import ")), default=-1)
    return "\n".join(lines[:k + 1] + CEIL_HELPER.split("\n") + lines[k + 1:])


def sha256_text(s):
    return hashlib.sha256(s.encode()).hexdigest()


def unified(a, b, name="Solution.lean"):
    return "".join(difflib.unified_diff(a.splitlines(True), b.splitlines(True), f"a/{name}", f"b/{name}", n=1))


def spec_names(task):
    names = set()
    for f in sorted((task.root / task.spec_dir).glob("*.lean")):
        names.update(re.findall(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:def|abbrev)\s+([\w.']+)",
                                f.read_text(), re.M))
    return {short(n) for n in names}


def reference_file(task):
    refs = sorted((task.root / "reference").glob("*.lean"))
    if not refs:
        raise FileNotFoundError(f"{task.id} has no reference solution")
    return refs[0]


def mutants(task, max_mutants=None):
    """The stripped reference and the deterministic list of mutants (dicts) for a task."""
    ref = reference_file(task)
    stripped = strip_proofs(ref.read_text())
    seen, out = {sha256_text(stripped)}, []
    for s in sites(stripped, task, spec_names(task)):
        src = apply(stripped, s)
        h = sha256_text(src)
        if h in seen:
            continue
        seen.add(h)
        out.append({"operator": s.op, "decl": s.decl, "line": line_of(stripped, s.start),
                    "column": s.start - stripped.rfind("\n", 0, s.start) - 1, "description": s.desc,
                    "source": src, "source_sha256": h, "_pos": s.start})
    total = len(out)
    if max_mutants and total > max_mutants:
        out = select(out, max_mutants, task.id)
    out.sort(key=lambda m: (OP_ORDER.index(m["operator"]), m["_pos"], m["source_sha256"]))
    for i, m in enumerate(out):
        m["id"] = f"M{i + 1:03d}"
        m["diff"] = unified(stripped, m["source"])
        del m["_pos"]
    return {"reference": str(ref.relative_to(ROOT)), "reference_sha256": taskmod.sha256(ref),
            "stripped": stripped, "stripped_sha256": sha256_text(stripped), "generated": total, "mutants": out}


def select(ms, k, key):
    """Deterministic operator-stratified subset of size k: round robin over operators, each
    operator's sites in an order shuffled by a seed derived from the task id."""
    rng = random.Random(int(hashlib.sha256(key.encode()).hexdigest()[:16], 16))
    groups = {}
    for m in sorted(ms, key=lambda m: (m["_pos"], m["source_sha256"])):
        groups.setdefault(m["operator"], []).append(m)
    for g in groups.values():
        rng.shuffle(g)
    order = [op for op in OP_ORDER if op in groups]
    out = []
    while len(out) < k:
        for op in order:
            if groups[op] and len(out) < k:
                out.append(groups[op].pop(0))
        if not any(groups[op] for op in order):
            break
    return out


# Containers.

def _slot():
    judge.SLOT_DIR, judge.SLOTS = SLOT_DIR, SLOTS
    return judge.container_slot()


def container(project, script, timeout):
    """Run `script` in the judge image with bounded CPUs and Lean threads, in this tool's slots."""
    if judge.IN_IMAGE:
        with _slot():
            return judge.run(["bash", "-lc", f"export LEAN_NUM_THREADS={THREADS}; cd '{project}' && {script}"],
                             timeout=timeout)
    name = f"pf-ss-{os.getpid()}-{time.monotonic_ns()}"
    cmd = ["docker", "run", "--rm", "--name", name, "--network", "none",
           "--security-opt", "seccomp=unconfined", "--security-opt", "apparmor=unconfined",
           "--security-opt", "systempaths=unconfined", "--cap-add", "SYS_ADMIN",
           "--memory", "4g", "--pids-limit", "512", "--cpus", str(THREADS), "-e", f"LEAN_NUM_THREADS={THREADS}",
           "-v", f"{project}:/work", "-w", "/work", judge.IMAGE, "bash", "-lc", script]
    with _slot():
        return judge.run(cmd, timeout=timeout,
                         on_timeout=lambda: subprocess.run(["docker", "kill", name], capture_output=True))


def build_all(project, task, ms, log):
    """Build the stripped reference and every mutant in one container, sequentially. Returns
    {"reference": rec, mutant id: rec} with exit code, binary sha256 and the first error."""
    mdir = project / "mut"
    mdir.mkdir(exist_ok=True)
    for m in ms:
        (mdir / f"{m['id']}.lean").write_text(m["source"])
    ids = " ".join(m["id"] for m in ms)
    exe = task.exe
    script = (
        "set -u; cp candidate/Solution.lean mut/REF.lean; "
        f"for i in REF {ids}; do cp mut/$i.lean candidate/Solution.lean; "
        f"timeout {BUILD_TIMEOUT} lake build {exe} > mut/$i.log 2>&1; rc=$?; echo \"$i $rc\" >> mut/status; "
        f"if [ $rc = 0 ]; then cp .lake/build/bin/{exe} mut/$i.bin; sha256sum mut/$i.bin | cut -d' ' -f1 > mut/$i.sha; fi; "
        "done; cp mut/REF.lean candidate/Solution.lean")
    t0 = time.monotonic()
    r = container(project, script, timeout=900 + (BUILD_TIMEOUT + 30) * (len(ms) + 1))
    log(f"  built {len(ms) + 1} sources in {int(time.monotonic() - t0)} s (container exit {r['exit_code']})")
    status = {}
    if (mdir / "status").exists():
        for line in (mdir / "status").read_text().splitlines():
            i, rc = line.split()
            status[i] = int(rc)
    out = {}
    for i in ["REF"] + [m["id"] for m in ms]:
        rc = status.get(i)
        rec = {"exit_code": rc}
        if rc == 0:
            rec["binary_sha256"] = (mdir / f"{i}.sha").read_text().strip()
        else:
            logf = mdir / f"{i}.log"
            rec["error"] = first_error(logf.read_text(errors="replace") if logf.exists() else "no build log")
        out[i] = rec
    return out


def first_error(log_text):
    lines = [l.strip() for l in log_text.splitlines()]
    errs = [l for l in lines if re.search(r"error", l)]
    e = errs[0] if errs else (lines[-1] if lines else "")
    return re.sub(r"/work/|\S*/candidate/", "", e)[:300]


def install_binary(project, task, mid):
    dst = project / ".lake" / "build" / "bin" / task.exe
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy(project / "mut" / f"{mid}.bin", dst)
    os.chmod(dst, 0o755)


def run_tests(project, task, n, seed):
    """The judge's property tests on the installed executable, plus the round-1 outputs."""
    result = {}
    with judge.time_limit(TEST_TIMEOUT):
        binary_check.property_tests(project, task, n, seed, result)
    outf = project / "round1.out"
    outs = outf.read_text().splitlines() if outf.exists() else []
    cases = (project / "round1.jsonl").read_text().splitlines() if (project / "round1.jsonl").exists() else []
    for f in ("round1.out", "round2.out"):
        (project / f).unlink(missing_ok=True)
    return result, cases, outs


def _canon(line):
    try:
        return json.dumps(json.loads(line), sort_keys=True)
    except ValueError:
        return line


def first_difference(cases, outs, ref_outs):
    diff, first = 0, None
    for k, (c, o, r) in enumerate(zip(cases, outs, ref_outs)):
        if _canon(o) != _canon(r):
            diff += 1
            if first is None:
                first = {"case": k, "input": json.loads(c), "output": _loads(o), "reference_output": _loads(r)}
    diff += abs(len(outs) - len(ref_outs))
    return diff, first


def _loads(s):
    try:
        return json.loads(s)
    except ValueError:
        return s


# Kernel-checked counterexamples, in the task's project, one mutant at a time.

def add_cex_lib(project):
    (project / "cex" / "Cex").mkdir(parents=True, exist_ok=True)
    with open(project / "lakefile.toml", "a") as f:
        f.write('\n# Added by harness/spec_strength.py: generated refutations and their challenges.\n'
                '[[lean_lib]]\nname = "Cex"\nsrcDir = "cex"\nglobs = ["Cex.+"]\n')


def check_cex(project, task, mutant_source, item, k):
    """Check one counterexample item (from counterexample.generate) against the mutant now
    installed as candidate/Solution.lean: build, Comparator (six kernels), leanchecker, axioms."""
    (project / "candidate" / "Solution.lean").write_text(mutant_source)
    th = item["refutes"].split(".")[-1]
    ch = cexmod.challenge_source(task, th, cexmod.locked_statement(task, th))
    item["challenge_sha256"] = sha256_text(ch)
    item["lean_file_sha256"] = sha256_text(item["lean_source"])
    item["statement_sha256"] = sha256_text(item["statement"])
    cex = project / "cex"
    (cex / "Cex" / f"C{k}.lean").write_text(ch)
    (cex / "Cex" / f"S{k}.lean").write_text(item["lean_source"])
    (cex / f"c{k}.json").write_text(json.dumps({
        "challenge_module": f"Cex.C{k}", "solution_module": f"Cex.S{k}", "theorem_names": [item["theorem"]],
        "definition_names": [f"{task.ns}.{d}" for d in task.definitions],
        "permitted_axioms": cexmod.PERMITTED}, indent=2) + "\n")
    (cex / f"A{k}.lean").write_text(f"import Cex.S{k}\n#print axioms {item['theorem']}\n")
    script = (
        f"lake build Cex.S{k} Cex.C{k} > cex/b{k}.log 2>&1; echo $? > cex/b{k}.rc; "
        f"if [ $(cat cex/b{k}.rc) = 0 ]; then "
        f"lake comparator --paranoid --config cex/c{k}.json > cex/k{k}.log 2>&1; echo $? > cex/k{k}.rc; "
        f"if [ $(cat cex/k{k}.rc) = 0 ]; then lake env leanchecker Cex.S{k} > cex/l{k}.log 2>&1; echo $? > cex/l{k}.rc; "
        f"if [ $(cat cex/l{k}.rc) = 0 ]; then lake env lean cex/A{k}.lean > cex/a{k}.log 2>&1; echo $? > cex/a{k}.rc; fi; fi; fi")
    t0 = time.monotonic()
    r = container(project, script, timeout=1800)
    item["elapsed_ms"] = int((time.monotonic() - t0) * 1000)
    item["kernel_checked"] = False

    def rc(p):
        f = cex / f"{p}{k}.rc"
        return int(f.read_text().strip()) if f.exists() else None

    def log(p):
        f = cex / f"{p}{k}.log"
        return f.read_text(errors="replace") if f.exists() else ""

    if r["exit_code"] == 124:
        item["reason"] = "time limit reached while checking the refutation"
    elif rc("b") != 0:
        item["reason"] = f"refutation does not build: {cexmod._errors(log('b'))}"
    elif rc("k") != 0:
        item["reason"] = f"Comparator rejected the refutation: {cexmod._errors(log('k')[-4000:])}"
    else:
        item["kernels"] = re.findall(r"^(.+?) kernel accepts the solution$", log("k"), re.M)
        if rc("l") != 0:
            item["reason"] = f"leanchecker exit {rc('l')}"
        else:
            item["axioms"] = cexmod._axioms(log("a"), item["theorem"])
            if item["axioms"] is None or not set(item["axioms"]) <= set(cexmod.PERMITTED):
                item["reason"] = f"axiom audit: {item['axioms']}"
            else:
                item["kernel_checked"] = True
                item["reason"] = None
    (project / "candidate" / "Solution.lean").write_text((project / "mut" / "REF.lean").read_text())
    return item


CEX_KEYS = ["requirement", "refutes", "theorem", "statement", "statement_sha256", "kernel_checked", "reason",
            "kernels", "axioms", "input", "output", "origin", "note", "adapter", "adapter_sha256",
            "challenge_sha256", "lean_file_sha256", "lean_source", "elapsed_ms"]


# One task.

def validation_record(task):
    """Satisfiability evidence: the task's validation receipt for its references."""
    f = task.root / "validation.json"
    if not f.exists():
        return {"source": None, "references": {}}
    v = json.loads(f.read_text())
    refs = (v.get("checks") or {}).get("references") or {}
    return {"source": str(f.relative_to(ROOT)),
            "references": {k: {"judge": r.get("judge"), "binary": r.get("binary")} for k, r in refs.items()}}


def run_task(task, max_mutants=None, cases=2000, seed=0, ext_cases=10000, ext_seed=1, counterexamples=True,
             log=print):
    judge.SLOT_DIR, judge.SLOTS = SLOT_DIR, SLOTS     # this tool's own container slots
    t0 = time.monotonic()
    gen = mutants(task, max_mutants)
    ms = gen["mutants"]
    log(f"{task.id}: {gen['generated']} mutants generated, {len(ms)} selected")
    ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-ss-ws-"))
    (ws / "candidate").mkdir()
    (ws / "candidate" / "Solution.lean").write_text(gen["stripped"])
    project = judge.fresh_project(ws, judge.candidate_files(ws), task)
    shutil.rmtree(ws, ignore_errors=True)
    adapter_mod, adapter_path = cexmod.adapter(task)
    try:
        if counterexamples and adapter_mod is not None:
            add_cex_lib(project)
        builds = build_all(project, task, ms, log)
        ref = builds["REF"]
        report = base_report(task, gen, max_mutants, cases, seed, ext_cases, ext_seed, adapter_path)
        if ref["exit_code"] != 0:
            report["baseline"] = {"status": "BUILD_FAILED", "error": ref.get("error")}
            report["supported"] = False
            return finish(report, ms, t0)
        install_binary(project, task, "REF")
        base_std, std_cases, ref_std = run_tests(project, task, cases, seed)
        base_ext, ext_cases_l, ref_ext = run_tests(project, task, ext_cases, ext_seed)
        report["baseline"] = {"status": base_std["status"], "extended_status": base_ext["status"],
                              "binary_sha256": ref["binary_sha256"], "cases": base_std["cases"],
                              "followup_cases": base_std.get("followup_cases", 0),
                              "extended_cases": base_ext["cases"],
                              "violations": base_std["violations"], "extended_violations": base_ext["violations"]}
        if base_std["status"] != "PASS" or base_ext["status"] != "PASS":
            report["supported"] = False
            return finish(report, ms, t0)
        report["supported"] = True
        for m in ms:
            b = builds.get(m["id"], {})
            m["compiled"] = b.get("exit_code") == 0
            if not m["compiled"]:
                m["status"] = "not_compiled"
                m["compile_error"] = b.get("error")
                continue
            m["binary_sha256"] = b["binary_sha256"]
            if b["binary_sha256"] == ref["binary_sha256"]:
                m["status"] = "equivalent"
                m["evidence"] = "executable byte-identical to the reference's"
                continue
            install_binary(project, task, m["id"])
            r, cs, outs = run_tests(project, task, cases, seed)
            m["tests"] = summarize(r)
            if r["status"] in ("REFUTED", "TIMEOUT"):
                m["status"] = "killed" if r["status"] == "REFUTED" else "killed_timeout"
                m["killed_by"] = "property tests"
                m["_witnesses"] = r.get("witnesses") or []
                m["differing_cases"], _ = first_difference(cs, outs, ref_std)
                continue
            r2, cs2, outs2 = run_tests(project, task, ext_cases, ext_seed)
            m["extended_tests"] = summarize(r2)
            if r2["status"] in ("REFUTED", "TIMEOUT"):
                m["status"] = "killed_extended" if r2["status"] == "REFUTED" else "killed_timeout"
                m["killed_by"] = "extended property tests"
                m["_witnesses"] = r2.get("witnesses") or []
                continue
            d1, f1 = first_difference(cs, outs, ref_std)
            d2, f2 = first_difference(cs2, outs2, ref_ext)
            m["differing_cases"] = d1 + d2
            if d1 + d2:
                m["status"] = "survived_differs"
                m["first_difference"] = f1 or (f2 and {**f2, "extended": True})
            else:
                m["status"] = "survived_same"
        log(f"  property tests done in {int(time.monotonic() - t0)} s")
        if counterexamples and adapter_mod is not None:
            run_counterexamples(project, task, ms, log)
        return finish(report, ms, t0)
    finally:
        shutil.rmtree(project, ignore_errors=True)


def summarize(r):
    return {"status": r.get("status"), "cases": r.get("cases"), "followup_cases": r.get("followup_cases", 0),
            "violations": r.get("violations", {})}


class _Counter:
    def __init__(self):
        self.k = 0

    def next(self):
        self.k += 1
        return self.k - 1


def _attempt(project, task, m, witness, counter):
    """Generate and, when the adapter expresses it, kernel-check one refutation; returns the
    attempt record (without checking when there is no Lean source)."""
    item = cexmod.generate(task, witness)
    if not item.get("lean_source"):
        return {k2: item.get(k2) for k2 in ("requirement", "reason")}
    check_cex(project, task, m["source"], item, counter.next())
    return {k2: item[k2] for k2 in CEX_KEYS if k2 in item}


def run_counterexamples(project, task, ms, log, per_mutant_attempts=2, per_requirement_extra=2):
    """Kernel-checked refutations for killed mutants, then a probe of the survivors.

    1. Each killed mutant: its witnesses' requirements, those without a kernel-checked refutation
       in this task first; stop at the first accepted refutation or after `per_mutant_attempts`
       checked attempts.
    2. Each requirement violated by some mutant but not yet refuted in the kernel: up to
       `per_requirement_extra` further mutants' witnesses for it.
    3. Each survivor whose behaviour differs from the reference's: every requirement in turn on
       the first differing case. An accepted refutation shows that the specification rejects the
       mutant although the property tests did not (status `killed_kernel`)."""
    covered, counter = set(), _Counter()
    killed = [m for m in ms if m.get("status") in ("killed", "killed_extended") and m.get("_witnesses")]
    for m in killed:
        b = {"witnesses": m["_witnesses"], "violations": {w["requirement"]: 1 for w in m["_witnesses"]}}
        ws = cexmod.witnesses_by_requirement(task, b)
        ws.sort(key=lambda w: w["requirement"] in covered)
        attempts = []
        for w in ws:
            if sum(1 for a in attempts if "kernel_checked" in a) >= per_mutant_attempts:
                break
            a = _attempt(project, task, m, w, counter)
            attempts.append(a)
            if a.get("kernel_checked"):
                covered.add(a["requirement"])
                break
        m["counterexamples"] = attempts
        ok = next((a for a in attempts if a.get("kernel_checked")), None)
        m["kernel_checked"] = bool(ok)
        log(f"  {task.id} {m['id']} {m['operator']:<13} " + (f"kernel-checked refutation of {ok['requirement']}" if ok else
            "no kernel-checked refutation: " + "; ".join(f"{a.get('requirement')}: {str(a.get('reason'))[:80]}"
                                                        for a in attempts)))
    for rid, _ in task.requirements:
        if rid in covered:
            continue
        tried = 0
        for m in killed:
            if tried >= per_requirement_extra:
                break
            if any(a.get("requirement") == rid for a in m["counterexamples"]):
                continue
            w = next((w for w in m["_witnesses"] if w["requirement"] == rid), None)
            if w is None:
                continue
            a = _attempt(project, task, m, w, counter)
            m["counterexamples"].append(a)
            if "kernel_checked" in a:
                tried += 1
            if a.get("kernel_checked"):
                m["kernel_checked"] = True
                covered.add(rid)
                log(f"  {task.id} {m['id']} kernel-checked refutation of {rid} (requirement pass)")
                break
    for m in ms:
        if m.get("status") != "survived_differs" or not m.get("first_difference"):
            continue
        f = m["first_difference"]
        attempts = []
        for rid, _ in task.requirements:
            a = _attempt(project, task, m, {"requirement": rid, "input": f["input"], "output": f["output"],
                                            "message": "probe of a surviving mutant on its first differing case"},
                         counter)
            attempts.append(a)
            if a.get("kernel_checked"):
                break
        m["kernel_probe"] = attempts
        ok = next((a for a in attempts if a.get("kernel_checked")), None)
        if ok:
            m["status"], m["killed_by"], m["kernel_checked"] = "killed_kernel", "kernel-checked counterexample", True
            m["counterexamples"] = [ok]
        log(f"  {task.id} {m['id']} survivor probe: " + (f"kernel-checked refutation of {ok['requirement']}" if ok
                                                          else "no requirement refuted on the first differing case"))


def base_report(task, gen, max_mutants, cases, seed, ext_cases, ext_seed, adapter_path):
    locked = task.locked()
    return {
        "schema_version": SCHEMA,
        "kind": "proofforge-spec-strength",
        "task": {"id": task.id, "family": task.family, "split": task.split, "lib": task.lib,
                 "definitions": task.definitions, "requirements": [r for r, _ in task.requirements]},
        "locked": {"manifest_sha256": locked["manifest_sha256"],
                   "manifest_matches_files": lock.manifest(task) == locked["files"]},
        "reference": {"file": gen["reference"], "sha256": gen["reference_sha256"],
                      "stripped_sha256": gen["stripped_sha256"]},
        "settings": {"max_mutants": max_mutants, "cases": cases, "seed": seed, "extended_cases": ext_cases,
                     "extended_seed": ext_seed, "lean_threads": THREADS},
        "generator": {"tool": "harness/spec_strength.py", "tool_sha256": TOOL_SHA256,
                      "operators": OPERATORS},
        "counterexample_adapter": None if adapter_path is None else {
            "file": str(adapter_path.relative_to(ROOT)), "sha256": taskmod.sha256(adapter_path)},
        "toolchain": {"judge_image": judge.image_id(), "platform": judge.image_platform(),
                      "lean": (task.root / "lean-toolchain").read_text().strip()},
        "satisfiability": validation_record(task),
        "mutants_generated": gen["generated"],
    }


def finish(report, ms, t0):
    for m in ms:
        m.pop("_witnesses", None)
        m.pop("source", None)
        m.setdefault("status", "not_run")
    report["mutants"] = ms
    report["summary"] = summary(report)
    report["vacuity"] = vacuity(report)
    report["elapsed_s"] = int(time.monotonic() - t0)
    report["report_sha256"] = content_hash(report)
    return report


KILLED = ("killed", "killed_extended", "killed_timeout", "killed_kernel")
SURVIVED = ("survived_differs", "survived_same")


def summary(report):
    ms = report.get("mutants") or []
    by = lambda *s: sum(1 for m in ms if m.get("status") in s)  # noqa: E731
    compiled = sum(1 for m in ms if m.get("compiled"))
    equivalent = by("equivalent")
    killed = by(*KILLED)
    nonequiv = compiled - equivalent
    s = {"generated": report.get("mutants_generated", len(ms)), "selected": len(ms), "compiled": compiled,
         "not_compiled": by("not_compiled"), "equivalent": equivalent,
         "killed_property": by("killed"), "killed_extended": by("killed_extended"),
         "killed_timeout": by("killed_timeout"), "killed_kernel_only": by("killed_kernel"), "killed": killed,
         "killed_kernel": sum(1 for m in ms if m.get("kernel_checked")),
         "survived": by(*SURVIVED), "survived_differs": by("survived_differs"),
         "survived_same": by("survived_same"),
         "kill_ratio": f"{killed} of {nonequiv}" if nonequiv else "no non-equivalent mutants",
         "kill_rate": round(killed / nonequiv, 4) if nonequiv else None}
    s["by_operator"] = {}
    for op in OP_ORDER:
        sel = [m for m in ms if m["operator"] == op]
        if sel:
            s["by_operator"][op] = {"selected": len(sel), "compiled": sum(1 for m in sel if m.get("compiled")),
                                    "equivalent": sum(1 for m in sel if m.get("status") == "equivalent"),
                                    "killed": sum(1 for m in sel if m.get("status") in KILLED),
                                    "survived": sum(1 for m in sel if m.get("status") in SURVIVED)}
    return s


def vacuity(report):
    """Per requirement: mutants whose executable violates it, and kernel-checked refutations."""
    ms = report.get("mutants") or []
    out = []
    for rid in report["task"]["requirements"]:
        viol = [m["id"] for m in ms if (m.get("tests") or {}).get("violations", {}).get(rid)
                or (m.get("extended_tests") or {}).get("violations", {}).get(rid)]
        kern = [m["id"] for m in ms for a in (m.get("counterexamples") or [])
                if a.get("kernel_checked") and a.get("requirement") == rid]
        out.append({"requirement": rid, "violated_by": len(viol), "kernel_refuted_by": len(kern),
                    "mutants": viol[:12], "kernel_mutants": kern,
                    "not_trivially_true": "kernel-checked" if kern else ("tested" if viol else "not shown")})
    return out


def content_hash(report):
    body = {k: v for k, v in report.items() if k != "report_sha256"}
    return hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest()


# Passport record and verification.

def passport_record(report):
    """The optional `spec_strength` field of a Passport: a summary bound to the report by its hash
    and to the task by its locked manifest."""
    s = report["summary"]
    return {"report_sha256": report["report_sha256"],
            "locked_manifest_sha256": report["locked"]["manifest_sha256"],
            "reference_sha256": report["reference"]["sha256"],
            "tool_sha256": report["generator"]["tool_sha256"],
            "mutants": {k: s[k] for k in ("generated", "selected", "compiled", "equivalent", "killed",
                                          "killed_kernel", "survived")},
            "kill_ratio": s["kill_ratio"],
            "requirements_not_shown_nontrivial": [v["requirement"] for v in report["vacuity"]
                                                  if v["not_trivially_true"] == "not shown"]}


def verify_report(report, task=None, regenerate=True):
    """Problems with a report (empty list when it checks): content hash, locked manifest of the
    task in this checkout, and, with `regenerate`, that every listed mutant is regenerated from the
    reference with the same source hash and diff. Regeneration needs the generator version the
    report records (`generator.tool_sha256`); with another version it is skipped and noted."""
    problems = []
    if report.get("report_sha256") != content_hash(report):
        problems.append("report content hash differs")
    task = task or taskmod.load(report["task"]["id"])
    if task.locked()["manifest_sha256"] != report["locked"]["manifest_sha256"]:
        problems.append("locked manifest differs from the task in this checkout")
    if regenerate and report["generator"]["tool_sha256"] != TOOL_SHA256:
        print(f"note  the report was generated by harness/spec_strength.py {report['generator']['tool_sha256'][:16]}, "
              f"this checkout has {TOOL_SHA256[:16]}; mutant regeneration skipped")
        regenerate = False
    if regenerate:
        ref = ROOT / report["reference"]["file"]
        if taskmod.sha256(ref) != report["reference"]["sha256"]:
            problems.append("reference solution differs")
        else:
            gen = mutants(task, report["settings"].get("max_mutants"))
            have = {m["id"]: m for m in gen["mutants"]}
            if gen["generated"] != report.get("mutants_generated"):
                problems.append(f"{gen['generated']} mutants generated, report says {report.get('mutants_generated')}")
            for m in report.get("mutants") or []:
                g = have.get(m["id"])
                if not g or g["source_sha256"] != m["source_sha256"] or g["diff"] != m["diff"]:
                    problems.append(f"mutant {m['id']} is not regenerated")
    if report.get("summary") != summary(report):
        problems.append("summary does not match the mutant records")
    if report.get("vacuity") != vacuity(report):
        problems.append("vacuity records do not match the mutant records")
    return problems


def verify_passport_record(passport, report):
    """Problems with a Passport's `spec_strength` field against the report it names."""
    rec = passport.get("spec_strength")
    if rec is None:
        return []
    problems = []
    if rec != passport_record(report):
        problems.append("spec_strength record does not match the report")
    if report.get("report_sha256") != content_hash(report):
        problems.append("report content hash differs")
    if (passport.get("locked") or {}).get("manifest_sha256") != rec.get("locked_manifest_sha256"):
        problems.append("spec_strength record is for another locked manifest")
    return problems


# Rendering.

STATUS_TEXT = {
    "killed": "killed by property tests", "killed_extended": "killed by extended property tests",
    "killed_timeout": "killed (property tests stopped at the time limit)",
    "killed_kernel": "killed by a kernel-checked counterexample only",
    "equivalent": "equivalent (identical executable)", "survived_differs": "survived, behaviour differs",
    "survived_same": "survived, no observed difference", "not_compiled": "does not compile",
    "not_run": "not run",
}


def markdown(report):
    s, t = report.get("summary") or {}, report["task"]
    lines = [f"# Specification strength: {t['id']}", "",
             f"Reference `{report['reference']['file']}` with every proof replaced by `sorry`; locked manifest "
             f"`{report['locked']['manifest_sha256'][:16]}`; report `{report['report_sha256'][:16]}`.", ""]
    if not report.get("supported"):
        lines += [f"Not measured: the stripped reference did not pass the baseline ({report.get('baseline')}).", ""]
        return "\n".join(lines) + "\n"
    lines += ["| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | "
              "Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |",
              "|---|---|---|---|---|---|---|---|---|---|---|",
              f"| {s['generated']} | {s['selected']} | {s['compiled']} | {s['equivalent']} | "
              f"{s['killed_property'] + s['killed_timeout']} | {s['killed_extended']} | {s['killed_kernel_only']} | "
              f"{s['killed_kernel']} | {s['survived_differs']} | {s['survived_same']} | {s['kill_ratio']} |", "",
              "## Requirements", "", "| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |",
              "|---|---|---|---|"]
    for v in report["vacuity"]:
        lines.append(f"| {v['requirement']} | {v['violated_by']} | {v['kernel_refuted_by']} | {v['not_trivially_true']} |")
    lines += ["", "## Mutants", "", "| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |",
              "|---|---|---|---|---|---|---|"]
    for m in report["mutants"]:
        viol = ", ".join(sorted(((m.get("tests") or {}).get("violations") or {}) |
                                ((m.get("extended_tests") or {}).get("violations") or {})))
        kc = next((a["requirement"] for a in m.get("counterexamples") or [] if a.get("kernel_checked")), "")
        lines.append(f"| {m['id']} | {m['operator']} | `{m['decl']}` | {m['description'].replace('|', '/')} | "
                     f"{STATUS_TEXT.get(m['status'], m['status'])} | {viol} | {kc} |")
    surv = [m for m in report["mutants"] if m["status"] in SURVIVED]
    if surv:
        lines += ["", "## Survivors", ""]
        for m in surv:
            lines += [f"### {m['id']}: {STATUS_TEXT[m['status']]}", "", f"{m['description']} in `{m['decl']}` "
                      f"(line {m['line']}); outputs differ from the reference on {m.get('differing_cases', 0)} cases.", "",
                      "```diff", m["diff"].rstrip("\n"), "```", ""]
            if m.get("first_difference"):
                f = m["first_difference"]
                lines += ["First differing case:", "", "```json",
                          json.dumps({"input": f["input"], "output": f["output"],
                                      "reference_output": f["reference_output"]}, sort_keys=True), "```", ""]
    return "\n".join(lines) + "\n"


def write(report, out_dir):
    out_dir = pathlib.Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    (out_dir / "report.md").write_text(markdown(report))


def main(argv=None):
    ap = argparse.ArgumentParser(prog="spec-strength", description=__doc__.split("\n\n")[0])
    ap.add_argument("--task")
    ap.add_argument("--out", help="output directory (report.json, report.md)")
    ap.add_argument("--max-mutants", type=int, default=None)
    ap.add_argument("--cases", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--extended-cases", type=int, default=10000)
    ap.add_argument("--extended-seed", type=int, default=1)
    ap.add_argument("--no-counterexample", action="store_true")
    ap.add_argument("--list", action="store_true", help="list the mutants without building them")
    ap.add_argument("--verify", metavar="REPORT", help="check a report's hash, lock and mutant regeneration")
    a = ap.parse_args(argv)
    if a.verify:
        rep = json.loads(pathlib.Path(a.verify).read_text())
        problems = verify_report(rep)
        for p in problems:
            print(f"DIFFERENT  {p}")
        print("verified" if not problems else f"NOT verified: {len(problems)} problems")
        return 0 if not problems else 1
    if not a.task:
        ap.error("--task is required")
    t = taskmod.load(a.task)
    if a.list:
        gen = mutants(t, a.max_mutants)
        print(f"{t.id}: {gen['generated']} mutants generated, {len(gen['mutants'])} selected")
        for m in gen["mutants"]:
            print(f"{m['id']}  {m['operator']:<13} {m['decl']:<24} {m['line']:>4}:{m['column']:<3} {m['description']}")
        return 0
    rep = run_task(t, a.max_mutants, a.cases, a.seed, a.extended_cases, a.extended_seed,
                   counterexamples=not a.no_counterexample)
    if a.out:
        write(rep, a.out)
    s = rep["summary"]
    print(f"{t.id}: {s['generated']} generated, {s['selected']} selected, {s['compiled']} compiled, "
          f"{s['equivalent']} equivalent, {s['killed']} killed ({s['killed_kernel']} kernel-checked), "
          f"{s['survived']} survived ({s['survived_differs']} with a behaviour difference); kill ratio {s['kill_ratio']}")
    return 0 if rep.get("supported") else 2


if __name__ == "__main__":
    sys.exit(main())
