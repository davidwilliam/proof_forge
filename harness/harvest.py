#!/usr/bin/env python3
"""Proof harvesting: helper lemmas of verified candidates into ProofForgeFin.

Every verified run leaves helper lemmas in its final candidate. This tool collects them, keeps
the ones that state a general fact, checks them the way library code is checked, and writes them
to lib/ProofForgeFin/Harvested/. No model is called; Lean runs in the pinned image.

  sources      VERIFIED candidates with their evidence: results/**/final.lean next to a
               passport.json whose status is VERIFIED and whose content hash and solution hash
               match; results/**/final.lean next to an eval.json with judge ACCEPT, binary PASS
               and the final file's hash (E1 runs, which have no Passport); formal/evidence/*/
               Solution.lean with a VERIFIED verification record. Tasks of the frozen test split
               are held out of the library (LIBRARY_SPLITS); their candidates are listed and not
               harvested.
  parse        every `theorem` of a source except the task's required theorems, with its
               namespace, `open` commands and attributes (a line-based reader of the top-level
               commands; comments and strings are respected).
  variants     the statement as written (v0); restated over library definitions and type
               aliases (v1: a task definition whose text equals a library definition is replaced
               by the library's, a task type alias by its type, a task lemma by the library lemma
               of the same name); with task structures abstracted (v2: a binder `(s : S)` used
               only through fields of general types becomes one variable per field).
  statements   pass 1: every variant elaborated with `sorry` proofs in a file that imports only
               ProofForgeFin, with `autoImplicit` off. A statement that elaborates is general; the
               first general variant is kept. Otherwise the lemma is task-specific.
  proofs       pass 2: the general lemmas of each source with their own proofs, in source order
               (so a proof may use an earlier general lemma of its source). Kept when Lean accepts
               the proof and the axioms are within propext, Classical.choice and Quot.sound.
               Lean also reports the statement's fingerprint (the type with universe levels set to
               zero; equal fingerprints are alpha-equivalent statements, binder names ignored),
               the existing constants with the same statement and the source lemmas the proof uses.
  dedup        pass 3, for one representative of each fingerprint, in a file without the
               harvested lemmas: closed by a default tactic (`rfl`, `decide`, `omega`, `simp`,
               `simp_all`) or a library tactic (`fin_simp`, `div_norm`) is trivial; closed by
               `exact?` is already in the library or the core library. Equal fingerprints among
               harvested lemmas keep one lemma with every source in its provenance.
  modules      the accepted lemmas, renamed (prefixes such as `my_` and `planN_` removed, clashes
               numbered), with a provenance doc string each, in lib/ProofForgeFin/Harvested/
               (Arith, List, Fin by the types the statement mentions), imported by
               ProofForgeFin.Harvested and ProofForgeFin. A lemma whose proof uses a lemma that was
               not accepted keeps that lemma as a support lemma. The modules are compiled, the
               fingerprints compared with pass 2 and the axioms audited; a lemma that fails is
               dropped with the lemmas that use it, until the modules compile cleanly.
  kernels      harness/fin_kernels.py restricted to the Harvested modules (`check(modules=...)`):
               all six kernels of `lake comparator --paranoid` and leanchecker.

Measurement (no model calls), in `measure`: the open obligations of unresolved runs (`sorry`
in a final candidate whose judge verdict is not ACCEPT and whose executable passed; a theorem whose
proof fails to compile counts as one obligation) are replaced by one fixed battery of tactics
(default tactics, the library tactics and `exact?`), first with the library before the harvest
(the sources of the commit the harvest started from), then with the harvested library; the
report counts the obligations each closes. The proof size of every source lemma that has a
harvested counterpart is compared with a one-line proof by that lemma.

Lean runs one container at a time with 4 CPUs, LEAN_NUM_THREADS=4 and 3 GB (PF_HARVEST_CPUS,
PF_HARVEST_MEMORY), outside the judge's container slots, so measured runs sharing the host keep
their slots.

Usage: harvest.py sources | run [--keep-work] | kernels | measure | report
"""
import argparse, contextlib, fcntl, hashlib, json, os, pathlib, re, shutil, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import fin_lib, judge, task as taskmod  # noqa: E402

ROOT = fin_lib.ROOT
LIB = fin_lib.LIB
OUT = ROOT / "results/harvest-1"
HARVESTED = "ProofForgeFin/Harvested"
NAMESPACE = "ProofForgeFin.Harvested"
WORK = pathlib.Path(os.environ.get("PF_HARVEST_WORK") or fin_lib.CACHE / "harvest")
LIBRARY_SPLITS = ("dev", "val", "realworld")
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
CPUS = os.environ.get("PF_HARVEST_CPUS", "4")
MEMORY = os.environ.get("PF_HARVEST_MEMORY", "3g")
MODULES = ["Arith", "List", "Fin"]   # import order


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha256_file(p):
    return sha256_bytes(pathlib.Path(p).read_bytes())


def rel(p):
    p = pathlib.Path(p)
    try:
        return str(p.resolve().relative_to(ROOT))
    except ValueError:
        return str(p)


# ---------------------------------------------------------------------------------------------
# Lean in the pinned image, within this host's sharing limits

@contextlib.contextmanager
def _flock(path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def in_container(project, script, timeout=3600):
    """judge.in_container with 4 CPUs, LEAN_NUM_THREADS=4 and one harvest container at a time;
    it takes none of the judge's container slots."""
    script = f"export LEAN_NUM_THREADS=4; {script}"
    with _flock(fin_lib.CACHE / ".harvest-container.lock"):
        if judge.IN_IMAGE:
            return judge.run(["bash", "-lc", f"cd '{project}' && {script}"], timeout=timeout)
        name = f"pf-harvest-{os.getpid()}-{time.monotonic_ns()}"
        cmd = ["docker", "run", "--rm", "--name", name, "--network", "none",
               "--security-opt", "seccomp=unconfined", "--security-opt", "apparmor=unconfined",
               "--security-opt", "systempaths=unconfined", "--cap-add", "SYS_ADMIN",
               "--cpus", CPUS, "--memory", MEMORY, "--pids-limit", "512",
               "-v", f"{pathlib.Path(project).resolve()}:/work", "-w", "/work", judge.IMAGE, "bash", "-lc", script]
        return judge.run(cmd, timeout=timeout,
                         on_timeout=lambda: __import__("subprocess").run(["docker", "kill", name], capture_output=True))


@contextlib.contextmanager
def limited():
    """Route the containers of fin_lib, fin_kernels and the judge through `in_container`."""
    prev = judge.in_container
    judge.in_container = in_container
    try:
        yield
    finally:
        judge.in_container = prev


def probe_project(name, root=None):
    """A scratch project at WORK/<name> that requires the built library of `root` (default lib/)."""
    d = WORK / name
    if d.exists():
        shutil.rmtree(d)
    d.mkdir(parents=True)
    shutil.copy2(fin_lib.lib_root(root) / "lean-toolchain", d / "lean-toolchain")
    (d / "lakefile.toml").write_text('name = "pfHarvest"\n')
    (d / "lake-manifest.json").write_text(json.dumps(
        {"version": "1.3.0", "packagesDir": ".lake/packages", "packages": [], "name": "pfHarvest",
         "lakeDir": ".lake", "fixedToolchain": False}, indent=1) + "\n")
    with limited():
        fin_lib.vendor(d, root=root, force=True)
    return d


def lean_json(project, files, timeout=3600):
    """`lake env lean --json F` for each file, one container; returns {file: [message, ...]} and
    {file: output lines that are not messages, with the lines of `#eval` output}. Outputs are
    cached by the file's text and the vendored library's version."""
    pkg = project / fin_lib.VENDOR
    lib_sha = fin_lib.tree_sha256(pkg) if pkg.is_dir() else "none"
    cache = WORK / "lean-cache"
    cache.mkdir(parents=True, exist_ok=True)
    keys = {f: sha256_bytes(((project / f).read_text() + "\0" + lib_sha).encode()) for f in files}
    todo = []
    for f in files:
        hit = cache / f"{keys[f]}.out"
        if hit.is_file():
            shutil.copy2(hit, project / f"{f}.out")
        else:
            todo.append(f)
    script = "; ".join(f"lake env lean -DmaxErrors=1000000 --json {f} > {f}.out 2> {f}.err; echo {f}=$?" for f in todo)
    r = in_container(project, script, timeout=timeout) if todo else {"output_tail": ""}
    for f in todo:
        if re.search(rf"^{re.escape(f)}=\d+$", r["output_tail"], re.M) and judge.TIMEOUT_MARK not in r["output_tail"]:
            shutil.copy2(project / f"{f}.out", cache / f"{keys[f]}.out")
    msgs, other = {}, {}
    for f in files:
        msgs[f], other[f] = [], []
        out = project / f"{f}.out"
        for line in (out.read_text(errors="replace").splitlines() if out.is_file() else []):
            if line.startswith("{") and '"severity"' in line and '"pos"' in line:
                try:
                    m = json.loads(line)
                except ValueError:
                    other[f].append(line)
                    continue
                if "PFHJSON " in m["data"]:
                    other[f] += m["data"].splitlines()
                else:
                    msgs[f].append(m)
                continue
            other[f].append(line)
        if f in todo and (judge.TIMEOUT_MARK in r["output_tail"] or
                          not re.search(rf"^{re.escape(f)}=\d+$", r["output_tail"], re.M)):
            other[f].append("__TIMEOUT__")
    return msgs, other


# ---------------------------------------------------------------------------------------------
# Sources

def sources():
    """Every verified candidate with its evidence, and the ones held out or skipped."""
    import passport
    out, skipped = [], []

    def add(kind, task_id, f, evidence, **extra):
        try:
            t = taskmod.load(task_id)
        except FileNotFoundError:
            skipped.append({"file": rel(f), "reason": f"unknown task {task_id}"})
            return
        out.append({"kind": kind, "task": t.id, "split": t.split, "file": rel(f), "file_sha256": sha256_file(f),
                    "evidence": rel(evidence), **extra})

    for pp in sorted((ROOT / "results").rglob("passport.json")):
        final = pp.parent / "final.lean"
        if not final.is_file() or "harvest-1" in pp.parts:
            continue
        p = json.loads(pp.read_text())
        if p.get("status") != "VERIFIED":
            continue
        if p.get("passport_sha256") != passport.content_hash(p):
            skipped.append({"file": rel(final), "reason": "Passport content hash differs"})
        elif p["solution"]["files"].get("final.lean") != sha256_file(final):
            skipped.append({"file": rel(final), "reason": "final.lean is not the file the Passport binds"})
        else:
            add("passport", p["task"]["id"], final, pp, passport_sha256=p["passport_sha256"])
    for ev in sorted((ROOT / "results").rglob("eval.json")):
        final = ev.parent / "final.lean"
        if not final.is_file() or (ev.parent / "passport.json").is_file():
            continue
        e = json.loads(ev.read_text())
        if e.get("judge") == "ACCEPT" and e.get("binary") == "PASS":
            if e.get("final_sha256") != sha256_file(final):
                skipped.append({"file": rel(final), "reason": "final.lean is not the file eval.json records"})
            else:
                add("eval", e["task"], final, ev, eval_sha256=sha256_file(ev))
    for prov in sorted((ROOT / "formal/evidence").glob("*/provenance.json")):
        sol = prov.parent / "Solution.lean"
        d = json.loads(prov.read_text())
        v = d.get("verification") or {}
        if isinstance(v, dict) and v.get("status") == "VERIFIED" and sol.is_file():
            if d.get("solution_sha256") != sha256_file(sol):
                skipped.append({"file": rel(sol), "reason": "Solution.lean is not the file the record binds"})
            else:
                add("evidence", "payout-flagship", sol, prov, passport_sha256=v.get("passport_sha256"))
    for i, s in enumerate(out):
        s["id"] = f"s{i:03d}"
        s["harvest"] = s["split"] in LIBRARY_SPLITS
    return out, skipped


# ---------------------------------------------------------------------------------------------
# Reading Lean sources

KEYWORDS = ("theorem", "lemma", "def", "abbrev", "structure", "inductive", "class", "instance", "namespace",
            "section", "end", "open", "example", "set_option", "attribute", "variable", "universe", "mutual",
            "macro", "macro_rules", "syntax", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
            "elab", "elab_rules", "deriving", "import", "opaque", "axiom", "local", "scoped", "private",
            "protected", "noncomputable", "partial", "unsafe", "nonrec", "@[", "/--", "/-!", "#", "termination_by",
            "decreasing_by")
MODIFIERS = ("private", "protected", "noncomputable", "partial", "unsafe", "nonrec")
CMD_START = re.compile(r"(@\[|/--|/-!|#|(" + "|".join(k for k in KEYWORDS if k[0].isalpha()) + r")\b)")
IDENT = r"[A-Za-z_À-ɏͰ-Ͽἀ-῿][\w'À-ɏͰ-Ͽ₀-ₜ!?.]*"


def line_states(text):
    """For each line, whether it starts outside comments and strings."""
    states, depth, in_str, i, n = [True], 0, False, 0, len(text)
    while i < n:
        c = text[i]
        if in_str:
            if c == "\\" and i + 1 < n and text[i + 1] != "\n":
                i += 2
                continue
            if c == '"':
                in_str = False
        elif depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                continue
        else:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("--", i):
                j = text.find("\n", i)
                i = n if j < 0 else j
                continue
            if c == '"':
                in_str = True
            elif c == "'" and i + 2 < n and text[i + 2] == "'" and text[i + 1] not in "'\n" and \
                    not (i and (text[i - 1].isalnum() or text[i - 1] in "_'")):
                i += 3
                continue
        if c == "\n":
            states.append(depth == 0 and not in_str)
        i += 1
    return states


def chunks(text):
    """Top-level commands: (first line, text), with doc comments, attributes and `open ... in`
    attached to the command they precede."""
    lines = text.split("\n")
    states = line_states(text)
    starts = [i for i, l in enumerate(lines) if states[i] and l[:1].strip() and CMD_START.match(l)
              and not l.startswith(("termination_by", "decreasing_by"))]
    raw = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        raw.append([s, "\n".join(lines[s:e])])
    out, pending = [], None
    for s, t in raw:
        if pending is not None:
            s, t = pending[0], pending[1] + "\n" + t
            pending = None
        if not split_header(strip_prefix(t)[1])[3].strip():   # only a doc string, attributes or `open ... in`
            pending = [s, t]
            continue
        out.append((s, t))
    if pending:
        out.append(tuple(pending))
    return out


def strip_prefix(t):
    """(doc string, rest): the leading doc comment of a command and the text after it."""
    m = re.match(r"\s*(/--.*?-/)\s*", t, re.S)
    if m:
        return m.group(1), t[m.end():]
    m = re.match(r"\s*/-!.*?-/\s*", t, re.S)
    if m:
        return None, t[m.end():]
    return None, t


def split_header(t):
    """Attributes, modifiers, `open ... in` prefixes, keyword and the rest of a command."""
    attrs, mods, opens_in = [], [], []
    rest = t
    while True:
        rest = rest.lstrip()
        if rest.startswith("@["):
            j = matching(rest, 1)
            attrs.append(rest[2:j].strip())
            rest = rest[j + 1:]
            continue
        m = re.match(r"open\s+([^\n]*?)\s+in\b", rest)
        if m:
            opens_in.append(m.group(1))
            rest = rest[m.end():]
            continue
        m = re.match(r"(" + "|".join(MODIFIERS) + r")\b", rest)
        if m:
            mods.append(m.group(1))
            rest = rest[m.end():]
            continue
        break
    m = re.match(r"([A-Za-z_]+)\b", rest)
    kw = m.group(1) if m else rest[:1]
    return attrs, mods, opens_in, kw, rest[m.end():] if m else rest


PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}


def matching(s, i):
    """Index of the bracket closing the one at s[i] (comment and string aware); len(s) if none."""
    stack, j, n = [], i, len(s)
    while j < n:
        c = s[j]
        if s.startswith("/-", j):
            k = s.find("-/", j + 2)
            j = n if k < 0 else k + 2
            continue
        if s.startswith("--", j):
            k = s.find("\n", j)
            j = n if k < 0 else k
            continue
        if c == '"':
            k = j + 1
            while k < n and s[k] != '"':
                k += 2 if s[k] == "\\" else 1
            j = k + 1
            continue
        if c in PAIRS:
            stack.append(PAIRS[c])
        elif stack and c == stack[-1]:
            stack.pop()
            if not stack:
                return j
        j += 1
    return n


def top_level_assign(s):
    """Index of the first `:=` outside brackets, comments and strings, or -1."""
    depth, j, n = 0, 0, len(s)
    while j < n:
        c = s[j]
        if s.startswith("/-", j):
            k = s.find("-/", j + 2)
            j = n if k < 0 else k + 2
            continue
        if s.startswith("--", j):
            k = s.find("\n", j)
            j = n if k < 0 else k
            continue
        if c == '"':
            k = j + 1
            while k < n and s[k] != '"':
                k += 2 if s[k] == "\\" else 1
            j = k + 1
            continue
        if c in PAIRS:
            depth += 1
        elif c in PAIRS.values():
            depth = max(0, depth - 1)
        elif depth == 0 and s.startswith(":=", j):
            return j
        elif depth == 0 and s.startswith("\n|", j):
            return -1
        j += 1
    return -1


def strip_trailing(proof):
    """A proof without trailing blank and comment-only lines."""
    lines = proof.rstrip().split("\n")
    while lines and (not lines[-1].strip() or lines[-1].strip().startswith("--")):
        lines.pop()
    return "\n".join(lines)


def parse(text):
    """Declarations and scope of a Lean file: {"theorems": [...], "defs": {...}, "structures": {...}}."""
    scopes = [{"kind": "root", "name": "", "opens": []}]
    theorems, defs, structures = [], {}, {}
    for line, t in chunks(text):
        doc, body = strip_prefix(t)
        attrs, mods, opens_in, kw, rest = split_header(body)
        ns = ".".join(s["name"] for s in scopes if s["kind"] == "namespace" and s["name"])
        opens = [o for s in scopes for o in s["opens"]]
        if kw == "namespace":
            name = rest.strip().split()[0] if rest.strip() else ""
            for part in name.split("."):
                scopes.append({"kind": "namespace", "name": part, "opens": []})
        elif kw == "section":
            scopes.append({"kind": "section", "name": rest.strip().split()[0] if rest.strip() else "", "opens": []})
        elif kw == "end":
            name = rest.strip().split()[0] if rest.strip() else ""
            for _ in range(max(1, len(name.split(".")) if name else 1)):
                if len(scopes) > 1:
                    scopes.pop()
        elif kw == "open" and not opens_in:
            scopes[-1]["opens"].append(rest.strip().split("\n")[0].strip())
        elif kw in ("theorem", "lemma"):
            m = re.match(r"\s*(" + IDENT + r")", rest)
            if not m:
                continue
            name = m.group(1)
            after = rest[m.end():]
            i = top_level_assign(after)
            if i < 0:
                continue
            theorems.append({"name": name, "ns": ns, "line": line + 1, "attrs": attrs, "mods": mods,
                             "opens": opens + opens_in, "statement": after[:i].rstrip(),
                             "proof": strip_trailing(after[i + 2:]), "doc": doc})
        elif kw in ("def", "abbrev", "instance", "opaque", "inductive", "class"):
            m = re.match(r"\s*(" + IDENT + r")", rest)
            if m:
                defs[m.group(1)] = {"kw": kw, "ns": ns, "text": rest[m.end():].strip()}
                if kw == "inductive":
                    for c in re.findall(r"^\s*\|\s*(" + IDENT + r")", rest, re.M):
                        defs.setdefault(c, {"kw": "ctor", "ns": ns, "text": ""})
        elif kw == "structure":
            m = re.match(r"\s*(" + IDENT + r")", rest)
            if m:
                name = m.group(1)
                defs[name] = {"kw": kw, "ns": ns, "text": rest[m.end():].strip()}
                structures[name] = structure_fields(rest[m.end():])
    return {"theorems": theorems, "defs": defs, "structures": structures}


def structure_fields(text):
    """Fields of a `structure ... where` declaration: [(name, type)], or None when the
    declaration has parameters, `extends` or fields this reader does not handle."""
    head, _, body = text.partition("where")
    if head.strip() or not body:
        return None
    fields = []
    body = re.sub(r"/--.*?-/", "", body, flags=re.S)
    for line in body.split("\n"):
        s = re.sub(r"--.*", "", line).strip()
        if not s or s.startswith("deriving"):
            continue
        m = re.fullmatch(r"(" + IDENT + r"(?:\s+" + IDENT + r")*)\s*:\s*(.+?)(\s*:=.*)?", s)
        if not m or m.group(3):
            return None
        for n in m.group(1).split():
            fields.append((n, m.group(2).strip()))
    return fields or None


# ---------------------------------------------------------------------------------------------
# Restating over library definitions

CORE_TYPES = {"Nat", "Int", "String", "Bool", "Unit", "Prop", "Char", "List", "Option", "Array", "Fin", "Type",
              "Prod", "Sum", "UInt8", "UInt16", "UInt32", "UInt64"}


def norm_def(text):
    """A definition's text after its name, for comparison: no comments, universe levels or
    repeated whitespace."""
    t = re.sub(r"/-.*?-/", "", text, flags=re.S)
    t = re.sub(r"--[^\n]*", "", t)
    t = re.sub(r"\b(Type|Sort)\s+(?:[uvw]\w*|_)\b", r"\1", t)
    return re.sub(r"\s+", " ", t).strip()


def library_tables(root=None):
    """Definitions (normalized text -> full name) and theorem names (short -> full names) of the
    library sources at `root`, without the harvested modules."""
    root = fin_lib.lib_root(root)
    defs, thms = {}, {}
    for f in sorted((root / "ProofForgeFin").rglob("*.lean")):
        if HARVESTED in str(f.relative_to(root)):
            continue
        p = parse(f.read_text())
        for n, d in p["defs"].items():
            if d["kw"] in ("def", "abbrev"):
                full = ".".join(x for x in (d["ns"], n) if x)
                defs.setdefault(norm_def(d["text"]), full)
        for t in p["theorems"]:
            full = ".".join(x for x in (t["ns"], t["name"]) if x)
            thms.setdefault(t["name"].split(".")[-1], []).append(full)
    return defs, thms


def is_general_type(t, aliases):
    toks = re.findall(IDENT, t)
    return all(x in CORE_TYPES or x in aliases or re.fullmatch(r"[a-zα-ω]", x) for x in toks)


def task_context(t, lib_defs, lib_thms):
    """What the restatement of a task's lemmas uses: the task's type aliases, the task
    definitions equal to library definitions, the task lemmas the library states under the same
    name, and the task's structures."""
    defs, structs, lemmas = {}, {}, set()
    for f in sorted((t.root / "spec").rglob("*.lean")):
        if f.name == "Challenge.lean":
            continue
        p = parse(f.read_text())
        defs.update(p["defs"])
        structs.update(p["structures"])
        lemmas.update(x["name"] for x in p["theorems"])
    return context_from(defs, structs, lemmas, lib_defs, lib_thms, t.ns)


def context_from(defs, structs, lemmas, lib_defs, lib_thms, ns):
    aliases, mapped = {}, {}
    for _ in range(3):   # aliases of aliases
        for n, d in defs.items():
            m = re.fullmatch(r"(?::\s*Type\s*)?:=\s*(.+)", d["text"].strip(), re.S)
            if d["kw"] in ("def", "abbrev") and m and is_general_type(m.group(1), aliases):
                rhs = substitute(m.group(1).strip(), aliases, ns)
                aliases[n] = rhs if re.fullmatch(r"[\w.]+", rhs) else f"({rhs})"
    for n, d in defs.items():
        if d["kw"] in ("def", "abbrev") and n not in aliases:
            full = lib_defs.get(norm_def(substitute(d["text"], aliases, ns)))
            if full:
                mapped[n] = full
    lib_ns = {x.rsplit(".", 1)[0] for x in mapped.values()}
    lemma_map = {}
    for n in lemmas:
        cands = [x for x in lib_thms.get(n, []) if x.rsplit(".", 1)[0] in lib_ns]
        if len(cands) == 1:
            lemma_map[n] = cands[0]
    fields = {}
    for s, fl in structs.items():
        if fl and all(is_general_type(ty, aliases) for _, ty in fl):
            fields[s] = [(f, substitute(ty, aliases, ns)) for f, ty in fl]
    return {"ns": ns, "aliases": aliases, "defs": mapped, "lemmas": lemma_map, "structs": fields,
            "names": set(defs) | set(structs)}


def substitute(text, table, ns):
    """Replace every free occurrence of a name of `table` (also qualified by `ns`)."""
    if not table:
        return text
    names = sorted(table, key=len, reverse=True)
    pat = re.compile(r"(?<![\w.'])(?:" + (re.escape(ns) + r"\." if ns else "") + r")?(" +
                     "|".join(re.escape(n) for n in names) + r")(?![\w'])")
    return pat.sub(lambda m: table[m.group(1)], text)


FIELD = r"[A-Za-z_][\w']*"


def abstract_structures(stmt, proof, structs):
    """v2: binders `(s : S)` of a structure with general fields, used only through `s.f`,
    become one variable `s_f` per used field. None when nothing applies."""
    changed = False
    while True:
        done = True
        for m in re.finditer(r"([({])\s*(" + FIELD + r"(?:\s+" + FIELD + r")*)\s*:\s*(" + IDENT + r")\s*([)}])", stmt):
            sname = m.group(3).split(".")[-1]
            if sname not in structs:
                continue
            fields = dict(structs[sname])
            scope = stmt[m.end():] + "\n" + proof
            new_binders, ok = [], True
            for var in m.group(2).split():
                used = []
                for o in re.finditer(rf"(?<![\w.']){re.escape(var)}(?![\w'])", scope):
                    f = re.match(r"\.(" + FIELD + r")", scope[o.end():])
                    if not f or f.group(1) not in fields:
                        ok = False
                        break
                    if f.group(1) not in used:
                        used.append(f.group(1))
                if not ok:
                    break
                new_binders += [f"{m.group(1)}{var}_{f} : {fields[f]}{m.group(4)}"
                                for f, _ in structs[sname] if f in used]
            if not ok:
                continue
            tail_stmt, tail_proof = stmt[m.end():], proof
            for var in m.group(2).split():
                for f in fields:
                    pat = rf"(?<![\w.']){re.escape(var)}\.{re.escape(f)}(?![\w'])"
                    tail_stmt = re.sub(pat, f"{var}_{f}", tail_stmt)
                    tail_proof = re.sub(pat, f"{var}_{f}", tail_proof)
            stmt, proof = stmt[:m.start()] + " ".join(new_binders) + tail_stmt, tail_proof
            changed, done = True, False
            break
        if done:
            break
    return (stmt, proof) if changed else None


def variants(th, ctx):
    """[(variant, statement, proof)]: v1 restated over library definitions (the text as written
    when nothing applies), v0 as written when v1 differs, v2 with structures abstracted."""
    table = {**ctx["aliases"], **ctx["defs"], **ctx["lemmas"]}
    s1, p1 = substitute(th["statement"], table, ctx["ns"]), substitute(th["proof"], table, ctx["ns"])
    out = [("v1", s1, p1)]
    if s1 != th["statement"]:
        out.append(("v0", th["statement"], th["proof"]))
    a = abstract_structures(s1, p1, ctx["structs"])
    if a:
        out.append(("v2", a[0], a[1]))
    return out


# ---------------------------------------------------------------------------------------------
# Lean passes

HEADER = ("import ProofForgeFin\n"
          "set_option autoImplicit false\nset_option relaxedAutoImplicit false\n"
          "set_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\n")

META = """
open Lean Meta Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let lv (ps : List Name) : List Level := ps.map fun _ => Level.zero
  let mut index : Std.HashMap UInt64 (Array Name) := {{}}
  if {index} then
    for (n, ci) in env.constants.map₁.toList do
      if let .thmInfo t := ci then
        if !n.isInternalDetail then
          let h := (t.type.instantiateLevelParams t.levelParams (lv t.levelParams)).hash
          index := index.insert h ((index.getD h #[]).push n)
  for (n, ci) in env.constants.map₂.toList do
    if let .thmInfo t := ci then
      if (`{prefix}).isPrefixOf n then
        let ty := t.type.instantiateLevelParams t.levelParams (lv t.levelParams)
        let axs ← liftCoreM (collectAxioms n)
        let same := (index.getD ty.hash #[]).filter fun m => match env.find? m with
          | some (.thmInfo u) => u.type.instantiateLevelParams u.levelParams (lv u.levelParams) == ty
          | _ => false
        let deps := t.value.getUsedConstants.filter fun c => (`{prefix}).isPrefixOf c
        let pp ← liftTermElabM do pure ((← ppExpr t.type).pretty 100000)
        IO.println ("PFHJSON " ++ (Json.compress (Json.mkObj [("name", toString n),
          ("axioms", toJson (axs.map toString)), ("hash", toString ty.hash),
          ("type_sorry", toJson t.type.hasSorry), ("value_sorry", toJson t.value.hasSorry),
          ("same", toJson (same.map toString)), ("deps", toJson (deps.map toString)), ("type", pp)])))
"""


def meta(prefix, index=False):
    return META.format(prefix=prefix, index="true" if index else "false")


def meta_records(lines):
    out = {}
    for line in lines:
        if line.startswith("PFHJSON "):
            r = json.loads(line[len("PFHJSON "):])
            out[r["name"]] = r
    return out


class Doc:
    """A Lean file built line by line, remembering the line range of each named item."""

    def __init__(self, header=HEADER):
        self.lines = header.split("\n")[:-1] if header.endswith("\n") else header.split("\n")
        self.ranges = {}

    def add(self, text, key=None):
        start = len(self.lines) + 1
        self.lines += text.split("\n")
        if key is not None:
            self.ranges[key] = (start, len(self.lines))

    def text(self):
        return "\n".join(self.lines) + "\n"

    def errors_in(self, msgs, key):
        a, b = self.ranges[key]
        return [m for m in msgs if m["severity"] == "error" and a <= m["pos"]["line"] <= b]

    def messages_in(self, msgs, key):
        a, b = self.ranges[key]
        return [m for m in msgs if a <= m["pos"]["line"] <= b]


def batches(items, n):
    return [items[i:i + n] for i in range(0, len(items), n)]


def attrs_text(attrs):
    keep = ["local simp" for a in attrs if re.fullmatch(r"simp\b.*", a.strip())]
    return f"@[{', '.join(keep)}] " if keep else ""


def collect(srcs):
    """The helper theorems of the harvested sources with their variants."""
    lib_defs, lib_thms = library_tables()
    task_ctx, decls = {}, []
    for s in srcs:
        t = taskmod.load(s["task"])
        if t.id not in task_ctx:
            defs, structs, lemmas = {}, {}, set()
            for f in sorted((t.root / "spec").rglob("*.lean")):
                if f.name != "Challenge.lean":
                    p = parse(f.read_text())
                    defs.update(p["defs"])
                    structs.update(p["structures"])
                    lemmas.update(x["name"] for x in p["theorems"])
            task_ctx[t.id] = (defs, structs, lemmas)
        defs, structs, lemmas = task_ctx[t.id]
        p = parse((ROOT / s["file"]).read_text())
        ctx = context_from({**defs, **p["defs"]}, {**structs, **p["structures"]}, lemmas, lib_defs, lib_thms, t.ns)
        k = 0
        for th in p["theorems"]:
            if th["name"] in t.theorems or th["name"].split(".")[-1] in t.theorems:
                continue
            decls.append({"id": f"{s['id']}d{k:03d}", "src": s["id"], "task": s["task"], "file": s["file"],
                          **{x: th[x] for x in ("name", "ns", "line", "attrs", "opens", "statement", "proof")},
                          "variants": variants(th, ctx), "task_names": sorted(ctx["names"])})
            k += 1
    return decls


def opens_of(ds):
    out = []
    for d in ds:
        for o in d["opens"]:
            if o not in out:
                out.append(o)
    return out


def pass_statements(project, decls, log):
    """Pass 1: which variants elaborate without the task."""
    by_src = {}
    for d in decls:
        by_src.setdefault(d["src"], []).append(d)
    results = {}
    for bi, group in enumerate(batches(sorted(by_src), 60)):
        doc = Doc()
        for sid in group:
            ds = by_src[sid]
            doc.add(f"namespace PFH.{sid}")
            for o in opens_of(ds):
                doc.add(f"open {o}")
            for d in ds:
                for v, stmt, _ in d["variants"]:
                    doc.add(f"theorem {d['id']}.{v}{stmt} := sorry", key=(d["id"], v))
            doc.add(f"end PFH.{sid}\n")
        doc.add(meta("PFH"))
        f = f"Stmt{bi}.lean"
        (project / f).write_text(doc.text())
        msgs, other = lean_json(project, [f])
        recs = meta_records(other[f])
        log(f"pass 1 batch {bi}: {len(recs)} statements elaborated, {len(msgs[f])} messages")
        for (did, v), _ in doc.ranges.items():
            sid = did.split("d")[0]
            r = recs.get(f"PFH.{sid}.{did}.{v}")
            ok = bool(r) and not r["type_sorry"] and not doc.errors_in(msgs[f], (did, v))
            results[(did, v)] = {"ok": ok, "errors": [m["data"][:300] for m in doc.errors_in(msgs[f], (did, v))][:2]}
    return results


def pass_proofs(project, decls, log):
    """Pass 2: the general lemmas with their proofs, per source in source order."""
    by_src = {}
    for d in decls:
        by_src.setdefault(d["src"], []).append(d)
    results = {}
    for bi, group in enumerate(batches(sorted(by_src), 25)):
        doc = Doc()
        for sid in group:
            ds = by_src[sid]
            doc.add(f"namespace PFH.{sid}")
            for o in opens_of(ds):
                doc.add(f"open {o}")
            for d in ds:
                doc.add(f"{attrs_text(d['attrs'])}theorem {d['name']}{d['stmt']} :={d['prf']}", key=d["id"])
            doc.add(f"end PFH.{sid}\n")
        doc.add(meta("PFH", index=True))
        f = f"Proof{bi}.lean"
        (project / f).write_text(doc.text())
        msgs, other = lean_json(project, [f])
        recs = meta_records(other[f])
        timeout = "__TIMEOUT__" in other[f]
        log(f"pass 2 batch {bi}: {len(recs)} lemmas, {len(msgs[f])} messages{' (TIMEOUT)' if timeout else ''}")
        for d in (x for sid in group for x in by_src[sid]):
            r = recs.get(f"PFH.{d['src']}.{d['name']}")
            errs = doc.errors_in(msgs[f], d["id"])
            res = {"elaborated": bool(r), "errors": [m["data"][:300] for m in errs][:2], "timeout": timeout}
            if r:
                local = {f"PFH.{d['src']}.{x['name']}": x["id"] for x in by_src[d["src"]]}
                # Lemmas the proof uses, and earlier lemmas of the source its text names (a
                # simp argument that rewrote nothing is named but not used).
                named = {x["id"] for x in by_src[d["src"]] if x["line"] < d["line"] and
                         re.search(rf"(?<![\w.']){re.escape(x['name'])}(?![\w'])", d["prf"])}
                res.update(axioms=r["axioms"], hash=r["hash"], same=r["same"], type=r["type"],
                           deps=sorted(({local[x] for x in r["deps"] if x in local} | named) - {d["id"]}))
            res["ok"] = bool(r) and not errs and not r["value_sorry"] and not r["type_sorry"] and \
                set(r["axioms"]) <= PERMITTED
            results[d["id"]] = res
    return results


BATTERY = ["rfl", "decide", "omega", "(intros; omega)", "simp", "(intros; simp_all)", "fin_simp", "div_norm"]


def battery(tactics=BATTERY):
    return "first\n" + "".join(f"    | ({t}) <;> done\n" for t in tactics)


def pass_dedup(project, reps, log):
    """Pass 3: trivial (a default or library tactic closes it) or already provable (`exact?`),
    in a file without any harvested lemma."""
    results = {}
    for bi, group in enumerate(batches(reps, 150)):
        doc = Doc()
        for d in group:
            doc.add(f"namespace PFC.{d['id']}")
            for o in d["opens"]:
                doc.add(f"open {o}")
            doc.add(f"set_option maxHeartbeats 100000 in\nexample{d['stmt']} := by\n  {battery()}", key=(d["id"], "triv"))
            doc.add(f"set_option maxHeartbeats 200000 in\nexample{d['stmt']} := by exact?", key=(d["id"], "exact"))
            doc.add(f"end PFC.{d['id']}\n")
        f = f"Dedup{bi}.lean"
        (project / f).write_text(doc.text())
        msgs, other = lean_json(project, [f], timeout=7200)
        log(f"pass 3 batch {bi}: {len(group)} statements, {len(msgs[f])} messages")
        timeout = "__TIMEOUT__" in other[f]
        for d in group:
            triv = not doc.errors_in(msgs[f], (d["id"], "triv"))
            found = [m["data"] for m in doc.messages_in(msgs[f], (d["id"], "exact")) if "Try this" in m["data"]]
            ex_err = doc.errors_in(msgs[f], (d["id"], "exact"))
            results[d["id"]] = {"trivial": triv and not timeout, "exact": (suggestion(found[0]) if found and not ex_err else None),
                                "timeout": timeout}
    return results


def suggestion(msg):
    """The term of an `exact?` suggestion."""
    m = re.search(r"exact\s+(.*)", msg, re.S)
    return re.sub(r"\s+", " ", m.group(1)).strip() if m else msg.strip()


# ---------------------------------------------------------------------------------------------
# Base library, decisions and modules

def base_imports(root=None):
    """The imports of ProofForgeFin.lean other than the harvested modules."""
    text = (fin_lib.lib_root(root) / "ProofForgeFin.lean").read_text()
    return [m for m in fin_lib.imports_of(text) if not m.startswith(NAMESPACE)]


HARVEST_IMPORT = f"import {NAMESPACE}\n"


def base_root(root=None):
    """The library sources without the harvested modules (WORK/base-lib): ProofForgeFin.lean
    without its harvested import. Before the first harvest this is lib/ itself, byte for byte."""
    root = fin_lib.lib_root(root)
    dst = WORK / "base-lib"
    shutil.rmtree(dst, ignore_errors=True)
    for r in fin_lib.source_files(root):
        if r.startswith(HARVESTED):
            continue
        (dst / r).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(root / r, dst / r)
    top = dst / "ProofForgeFin.lean"
    top.write_text(top.read_text().replace(HARVEST_IMPORT, ""))
    return dst


def choose_variant(d, p1):
    for v in ("v1", "v0", "v2"):
        for vv, stmt, prf in d["variants"]:
            if vv == v and p1.get((d["id"], v), {}).get("ok"):
                method = {"v1": "as written" if stmt == d["statement"] else "restated over library definitions",
                          "v0": "as written", "v2": "task structure abstracted into its fields"}[v]
                return v, stmt, prf, method
    return None


def size(proof):
    """Proof size: characters other than whitespace, and lines."""
    return {"chars": len(re.sub(r"\s", "", proof)), "lines": len([l for l in proof.strip().split("\n") if l.strip()])}


PREFIXES = r"(?:my_?|plan\d+_|px\d+_|p\d+_|tmp_?|aux_|helper_?|probe_?|test_?|check_?|harvest_?|h_)"


def clean_name(name):
    n = name.replace(".", "_").replace("'", "_")
    while True:
        m = re.match(PREFIXES, n)
        if not m or len(n) == m.end():
            break
        n = n[m.end():]
    n = re.sub(r"(_?(aux|test|check|proof|helper|v)\d*|\d+|_+)$", "", n) or n
    n = n.strip("_")
    return n if re.match(r"[A-Za-z]", n or "") else "lemma_" + re.sub(r"\W", "_", name)


def topic(stmt):
    if "ProofForgeFin." in stmt:
        return 2
    if re.search(r"\bList\b|\bArray\b|\bOption\b|∈|\[|\.sum\b|\.length\b|foldr|foldl|\.map\b|\.filter\b", stmt):
        return 1
    return 0


def provenance_doc(d, srcs, others, support_of=None, reason=None):
    s = srcs[d["src"]]
    ev = (f"Passport sha256 `{s['passport_sha256']}`" if s.get("passport_sha256") else
          f"eval.json sha256 `{s['eval_sha256']}` (judge ACCEPT, binary PASS)")
    lines = [f"Harvested from task `{d['task']}`: `{d['name']}` in `{d['file']}` (file sha256 `{s['file_sha256']}`; {ev})."]
    if d["method"] != "as written":
        lines.append(f"Statement {d['method']}.")
    if support_of:
        lines.append(f"Kept as a support lemma of {', '.join(f'`{x}`' for x in support_of)}; on its own it was not "
                     f"accepted ({reason}).")
    if others:
        tasks = sorted({o["task"] for o in others})
        lines.append(f"The same statement is proved in {len(others)} other verified candidate"
                     f"{'s' if len(others) != 1 else ''} (tasks {', '.join(f'`{t}`' for t in tasks)}).")
    return "/-- " + "\n".join(lines) + " -/"


def decide(classes, p2, p3):
    """Classes of equal statements and a verdict for each."""
    verdicts = {}
    for h, ds in classes.items():
        rep = ds[0]
        r2, r3 = p2[rep["id"]], p3.get(rep["id"], {})
        same = sorted(r2["same"], key=lambda x: (not x.startswith("ProofForgeFin."), len(x)))
        if same:
            where = "library" if same[0].startswith("ProofForgeFin.") else "core library"
            verdicts[h] = ("duplicate", f"same statement as {where} `{same[0]}`")
        elif r3.get("trivial"):
            verdicts[h] = ("trivial", "closed by a default tactic or a library tactic")
        elif r3.get("exact"):
            where = "library" if "ProofForgeFin." in r3["exact"] else "core library"
            verdicts[h] = ("duplicate", f"provable by `exact {r3['exact'][:120]}` ({where})")
        elif r3.get("timeout"):
            verdicts[h] = ("unchecked", "the duplicate check did not finish")
        else:
            verdicts[h] = ("accepted", "")
    return classes, verdicts


def final_names(decls):
    """A distinct final name for every lemma that may be written, in source order."""
    used, names = set(), {}
    for d in sorted(decls, key=lambda x: (x["src"], x["line"])):
        base = clean_name(d["name"])
        n, k = base, 2
        while n in used:
            n, k = f"{base}_{k}", k + 1
        used.add(n)
        names[d["id"]] = n
    return names


def plan_modules(classes, verdicts, p2, by_id, all_names):
    """The lemmas to write: accepted representatives and their support lemmas. A lemma cited by
    a written lemma is not written again when the representative of its statement is accepted and
    prints the same (same binders): the citation is redirected to it (`alias`). Returns
    (names, module index, support_of, alias, order), `order` listing every lemma after the lemmas
    its proof cites."""
    rep = {d["id"]: ds[0]["id"] for ds in classes.values() for d in ds}
    accepted = {ds[0]["id"] for h, ds in classes.items() if verdicts[h][0] == "accepted"}
    emit, support_of, alias, no_alias = dict.fromkeys(sorted(accepted)), {}, {}, set()
    todo = list(emit)
    while todo:
        i = todo.pop()
        for dep in p2[i].get("deps", []):
            if not p2[dep].get("ok"):
                continue
            r = rep.get(dep)
            if dep not in accepted and r in accepted and r not in (dep, i) and dep not in no_alias and \
                    p2[r]["type"] == p2[dep]["type"]:
                alias[dep] = r
                continue
            if r == i:   # the citing lemma states the same: the cited one stays a support lemma
                no_alias.add(dep)
                alias.pop(dep, None)
            support_of.setdefault(dep, []).append(i)
            if dep not in emit:
                emit[dep] = None
                todo.append(dep)
    # A lemma both cited through an alias and kept as a support lemma is cited as itself.
    for dep in list(alias):
        if dep in emit:
            alias.pop(dep)

    def cites(i):
        return [alias.get(x, x) for x in p2[i].get("deps", []) if p2[x].get("ok")]
    order, seen = [], set()

    def visit(i):
        if i in seen:
            return
        seen.add(i)
        for x in cites(i):
            if x in emit:
                visit(x)
        order.append(i)
    for i in sorted(emit, key=lambda x: (by_id[x]["src"], by_id[x]["line"])):
        visit(i)
    mod = {}
    for i in order:
        mod[i] = max([topic(by_id[i]["stmt"])] + [mod[x] for x in cites(i) if x in mod])
    names = {i: all_names[i] for i in emit}
    return names, mod, support_of, alias, order


def lemma_text(d, name, names_in_src, doc):
    """(head, body) of a lemma: `open ... in` and the doc string; the declaration, with
    references to lemmas of its source renamed."""
    stmt, prf = d["stmt"], d["prf"]
    table = dict(names_in_src)
    if table:
        prf = substitute(prf, table, d["ns"] or None)
        stmt = substitute(stmt, table, d["ns"] or None)
    opens = " ".join(d["opens"])
    head = f"open {opens} in\n" if opens else ""
    return f"{head}{doc}", f"theorem {name}{stmt} :={prf}\n"


MODULE_DOC = {
    0: "arithmetic on `Nat` and `Int`",
    1: "lists, options and sums over lists",
    2: "facts about ProofForgeFin definitions",
}


def module_text(k, lemmas, base_mods):
    imports = [f"import {m}" for m in base_mods] + [f"import {NAMESPACE}.{MODULES[j]}" for j in range(k)]
    return ("\n".join(imports) + "\n/-!\n" +
            f"# Harvested lemmas: {MODULE_DOC[k]}\n\n"
            "Helper lemmas of verified candidates (Passport VERIFIED, or judge ACCEPT with the executable\n"
            "passing the property cases), restated without the task where needed and kept when no default\n"
            "tactic, library tactic or `exact?` proves them from the library and the core library. Each\n"
            "doc string records the source. Generated by `harness/harvest.py`; regenerate rather than edit.\n"
            "-/\n\n" + f"namespace {NAMESPACE}\n\n" + "\n".join(lemmas) + f"\nend {NAMESPACE}\n")


def render(plan, by_id, srcs, classes, verdicts, p2, overrides):
    """{module index: [(lemma id, text)]} for the planned lemmas; `overrides` holds declaration
    texts corrected at an earlier final check."""
    names, mod, support_of, alias, order = plan
    per_mod = {k: [] for k in range(len(MODULES))}
    for i in order:
        d = by_id[i]
        h = p2[i]["hash"]
        accepted = classes[h][0]["id"] == i and verdicts[h][0] == "accepted"
        others = [x for x in classes[h] if x["id"] != i] if accepted else []
        doc = provenance_doc(d, srcs, others, None if accepted else
                             sorted(names[x] for x in support_of.get(i, []) if x in names),
                             None if accepted else verdicts[h][1] if classes[h][0]["id"] == i else
                             f"its statement is the one of `{classes[h][0]['name']}` of `{classes[h][0]['task']}`, "
                             f"{verdicts[h][0]}: {verdicts[h][1]}")
        in_src = {by_id[x]["name"]: names[x] for x in names if by_id[x]["src"] == d["src"]}
        in_src.update({by_id[x]["name"]: names[a] for x, a in alias.items() if by_id[x]["src"] == d["src"]})
        head, body = lemma_text(d, names[i], in_src, doc)
        per_mod[mod[i]].append((i, head, overrides.get(i, body)))
    return per_mod


def redundancy_example(head, body):
    """`exact?` on the statement of a written lemma, to be placed before it."""
    m = re.match(r"theorem \S+", body)
    i = top_level_assign(body[m.end():])
    opens = re.match(r"(open [^\n]* in\n)", head)
    return f"{opens.group(1) if opens else ''}set_option maxHeartbeats 200000 in\nexample{body[m.end():m.end() + i]}:= by exact?"


FINAL_HEADER = "import ProofForgeFin\nset_option linter.missingDocs true\n\n"


def fix_of(m, body, first_line):
    """A correction of `body` for a warning Lean can name the fix of: an unused simp argument
    (removed) or a deprecated name with its replacement. None otherwise."""
    lines = body.split("\n")
    offs = [0]
    for l in lines:
        offs.append(offs[-1] + len(l) + 1)

    def at(p):
        ln = p["line"] - first_line
        return offs[ln] + p["column"] if 0 <= ln < len(lines) else None
    if not m.get("endPos"):
        return None
    a, b = at(m["pos"]), at(m["endPos"])
    if a is None or b is None or b <= a:
        return None
    if "This simp argument is unused" in m["data"]:
        after = re.match(r"\s*,\s*", body[b:])
        before = re.search(r",\s*$", body[:a])
        if after:
            out = body[:a] + body[b + after.end():]
        elif before:
            out = body[:before.start()] + body[b:]
        else:
            out = body[:a] + body[b:]
        return re.sub(r"\b(simp_all|simpa|simp|dsimp)(\s+only)?\s*\[\s*\]", r"\1\2", out)
    dep = re.search(r"has been deprecated[:,]? [Uu]se `([^`]+)` instead", m["data"])
    if dep:
        return body[:a] + dep.group(1) + body[b:]
    unused = re.match(r"(?:unused variable `([^`]+)`|Variable name `([^`]+)` is not explicitly referenced)", m["data"])
    if unused:
        name = unused.group(1) or unused.group(2)
        if body[a:b] == name and re.fullmatch(r"[A-Za-z][\w']*", name):
            return body[:a] + "_" + name + body[b:]
    return None


def final_check(project, per_mod, p2, log, tag="Final", probe=()):
    """Compile the planned modules as one file over the base library, as the library build
    would (default options, missing-docs linter on). Returns ({lemma id: problem} for every lemma
    with an error or warning that has no fix, a statement that changed, or an axiom outside the
    permitted ones; {lemma id: corrected declaration} for warnings with a fix; errors outside
    every lemma; {lemma id: `exact?` term} for the lemmas of `probe` that `exact?` proves from the
    library and the harvested lemmas written before them)."""
    doc = Doc(FINAL_HEADER)
    first = {}
    for k in range(len(MODULES)):
        if not per_mod[k]:
            continue
        doc.add(f"namespace {NAMESPACE}\n")
        for i, head, body in per_mod[k]:
            if i in probe:
                doc.add(redundancy_example(head, body), key=(i, "ex"))
            doc.add(f"{head}\n{body}", key=i)
            first[i] = doc.ranges[i][0] + head.count("\n") + 1
        doc.add(f"end {NAMESPACE}\n")
    doc.add(meta(NAMESPACE))
    (project / f"{tag}.lean").write_text(doc.text())
    msgs, other = lean_json(project, [f"{tag}.lean"])
    recs = meta_records(other[f"{tag}.lean"])
    bad, fixes = {}, {}
    for k in range(len(MODULES)):
        for i, head, body in per_mod[k]:
            name = re.search(r"^theorem (\S+)", body, re.M).group(1)
            r = recs.get(f"{NAMESPACE}.{name}")
            probs = [m for m in doc.messages_in(msgs[f"{tag}.lean"], i) if m["severity"] in ("error", "warning")]
            errors = [m for m in probs if m["severity"] == "error"]
            if probs and not errors:
                fixed = body
                for m in sorted(probs, key=lambda m: (m["pos"]["line"], m["pos"]["column"]), reverse=True):
                    fixed = fix_of(m, fixed, first[i]) if fixed is not None else None
                if fixed is not None and fixed != body:
                    fixes[i] = fixed
                    continue
            if probs:
                p = errors[0] if errors else probs[0]
                bad[i] = f"{p['severity']}: {p['data'][:300]}"
            elif not r:
                bad[i] = "not declared"
            elif r["hash"] != p2[i]["hash"]:
                bad[i] = "statement differs from the checked one"
            elif not set(r["axioms"]) <= PERMITTED:
                bad[i] = f"axioms {r['axioms']}"
    stray = [m for m in msgs[f"{tag}.lean"] if m["severity"] == "error" and not any(
        a <= m["pos"]["line"] <= b for a, b in doc.ranges.values())]
    redundant = {}
    for i in probe:
        if (i, "ex") in doc.ranges and not doc.errors_in(msgs[f"{tag}.lean"], (i, "ex")):
            found = [m["data"] for m in doc.messages_in(msgs[f"{tag}.lean"], (i, "ex")) if "Try this" in m["data"]]
            if found:
                redundant[i] = suggestion(found[0])
    log(f"final check: {sum(len(v) for v in per_mod.values())} lemmas, {len(bad)} with problems, "
        f"{len(fixes)} corrected, {len(stray)} other errors, {len(redundant)} provable from earlier lemmas")
    return bad, fixes, stray, redundant


def root_text(mods):
    return ("\n".join(f"import {NAMESPACE}.{m}" for m in mods) + "\n/-!\n# Harvested lemmas\n\n"
            "Lemmas harvested from the helper lemmas of verified candidates by `harness/harvest.py`, with\n"
            "their provenance in each doc string; see `docs/HARVEST.md`.\n\n" +
            "".join(f"* `{NAMESPACE}.{MODULES[i]}`: {MODULE_DOC[i]}.\n" for i in range(len(MODULES)) if MODULES[i] in mods) +
            "-/\n")


def dependents_of(ids, p2, names):
    """`ids` and every planned lemma whose proof uses one of them, transitively."""
    out, todo = set(), list(ids)
    while todo:
        i = todo.pop()
        if i in out:
            continue
        out.add(i)
        todo += [j for j in names if i in p2[j].get("deps", [])]
    return out


def write_modules(per_mod, root=None):
    """Write lib/ProofForgeFin/Harvested/*.lean, ProofForgeFin/Harvested.lean and the import in
    ProofForgeFin.lean."""
    root = fin_lib.lib_root(root)
    d = root / HARVESTED
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir(parents=True)
    base_mods = base_imports(root)
    mods = []
    for k in range(len(MODULES)):
        if per_mod[k]:
            (d / f"{MODULES[k]}.lean").write_text(module_text(k, [f"{h}\n{b}" for _, h, b in per_mod[k]], base_mods))
            mods.append(MODULES[k])
        elif any(per_mod[j] for j in range(k + 1, len(MODULES))):
            (d / f"{MODULES[k]}.lean").write_text(module_text(k, [], base_mods))
            mods.append(MODULES[k])
    (root / f"{HARVESTED}.lean").write_text(root_text(mods))
    top = root / "ProofForgeFin.lean"
    text = top.read_text().replace(HARVEST_IMPORT, "")
    lines = text.split("\n")
    last = max(i for i, l in enumerate(lines) if l.startswith("import "))
    lines.insert(last + 1, HARVEST_IMPORT.rstrip("\n"))
    top.write_text("\n".join(lines))
    return mods


def run(log=print, write=True):
    """The whole harvest; returns the record written to results/harvest-1/harvest.json."""
    t0 = time.monotonic()
    WORK.mkdir(parents=True, exist_ok=True)
    srcs, skipped = sources()
    harvest_srcs = [s for s in srcs if s["harvest"]]
    by_src = {s["id"]: s for s in srcs}
    base = base_root()
    base_sha = fin_lib.tree_sha256(base)
    log(f"{len(srcs)} verified sources, {len(harvest_srcs)} harvested ({len(srcs) - len(harvest_srcs)} of the test split "
        f"held out); base library {base_sha[:16]}")
    decls = collect(harvest_srcs)
    by_id = {d["id"]: d for d in decls}
    log(f"{len(decls)} helper theorems")
    project = probe_project("probe", base)

    p1 = pass_statements(project, decls, log)
    for d in decls:
        c = choose_variant(d, p1)
        if c:
            d["variant"], d["stmt"], d["prf"], d["method"] = c
    general = [d for d in decls if d.get("stmt") is not None]
    log(f"pass 1: {len(general)} general statements, {len(decls) - len(general)} task-specific")

    p2 = pass_proofs(project, general, log)
    passed = [d for d in general if p2[d["id"]]["ok"]]
    log(f"pass 2: {len(passed)} proofs accepted without the task")

    classes0 = {}
    for d in passed:
        classes0.setdefault(p2[d["id"]]["hash"], []).append(d)
    # Representative: a Passport-backed source first, then the shortest proof.
    rank = {"passport": 0, "evidence": 1, "eval": 2}
    for h, ds in classes0.items():
        ds.sort(key=lambda d: (rank[by_src[d["src"]]["kind"]], size(d["prf"])["chars"], d["id"]))
    reps = [ds[0] for ds in classes0.values() if not p2[ds[0]["id"]]["same"]]
    p3 = pass_dedup(project, reps, log)
    classes, verdicts = decide(classes0, p2, p3)

    dropped, overrides, last_fixes = {}, {}, {}
    all_names = final_names(passed)
    for rnd in range(12):
        live = {h: (("dropped", f"at the final check: {dropped[ds[0]['id']]}") if ds[0]["id"] in dropped else verdicts[h])
                for h, ds in classes.items()}
        plan = plan_modules(classes, live, p2, by_id, all_names)
        per_mod = render(plan, by_id, by_src, classes, live, p2, overrides)
        # First round: is an accepted lemma provable by `exact?` from the lemmas written before it?
        probe = {ds[0]["id"] for h, ds in classes.items() if live[h][0] == "accepted"} if rnd == 0 else set()
        bad, fixes, stray, redundant = final_check(project, per_mod, p2, log, tag=f"Final{rnd}", probe=probe)
        for i, term in redundant.items():
            if i not in bad:
                verdicts[p2[i]["hash"]] = ("duplicate", f"provable by `exact {term[:120]}` from the library and the "
                                                        "harvested lemmas written before it")
        if redundant:
            continue
        if not bad and not fixes and not stray:
            break
        if stray:
            # A correction that broke the file: undo the last corrections and drop those lemmas.
            if not last_fixes:
                raise RuntimeError(f"final check: errors outside every lemma: {stray[:3]}")
            for i in last_fixes:
                overrides.pop(i, None)
            bad = {i: "a warning whose correction did not compile" for i in last_fixes}
            fixes = {}
        overrides.update(fixes)
        last_fixes = fixes
        for i in dependents_of(bad, p2, plan[0]):
            dropped[i] = bad.get(i) or "uses a lemma dropped at the final check"
    else:
        raise RuntimeError("final check did not converge")
    verdicts = live
    names, mod, support_of, alias, _ = plan

    rec_decls = []
    for d in decls:
        r = {k: d[k] for k in ("id", "src", "task", "file", "name", "line")}
        if d["id"] in dropped:
            r["dropped"] = dropped[d["id"]]
        if d["id"] in overrides and d["id"] in names:
            r["corrected"] = "a warning fixed at the final check (unused simp argument or deprecated name)"
        if d.get("stmt") is None:
            r["class"] = "task-specific"
            errs = [e for v, _, _ in d["variants"] for e in p1.get((d["id"], v), {}).get("errors", [])]
            r["reason"] = (errs[0] if errs else "statement does not elaborate without the task")[:200]
        else:
            r.update({"class": "general", "method": d["method"], "variant": d["variant"]})
            r2 = p2[d["id"]]
            if not r2["ok"]:
                r["verdict"] = "rejected"
                r["reason"] = ("proof does not check without the task: " + (r2["errors"][0] if r2["errors"] else
                               f"axioms {r2.get('axioms')}" if r2.get("axioms") else "not elaborated"))[:240]
            else:
                h = r2["hash"]
                r["statement_hash"] = h
                r["type"] = r2["type"]
                r["size"] = size(d["prf"])
                rep = classes[h][0]["id"]
                v, why = verdicts[h]
                if d["id"] == rep:
                    r["verdict"], r["reason"] = v, why
                else:
                    r["verdict"] = "duplicate"
                    r["reason"] = f"same statement as harvested `{classes[h][0]['name']}` ({classes[h][0]['id']})" \
                        if v == "accepted" else f"same statement as `{classes[h][0]['name']}` ({classes[h][0]['id']}), {v}: {why}"
                    r["representative"] = rep
                if d["id"] in alias:
                    r["cited_as"] = f"{NAMESPACE}.{names[alias[d['id']]]}"
                if d["id"] in names:
                    r["final_name"] = f"{NAMESPACE}.{names[d['id']]}"
                    r["module"] = f"{NAMESPACE}.{MODULES[mod[d['id']]]}"
                    if not (d["id"] == rep and v == "accepted"):
                        r["support_of"] = sorted(names[x] for x in support_of.get(d["id"], []) if x in names)
        rec_decls.append(r)

    if write:
        mods = write_modules(per_mod)
    counts = summarize(rec_decls)
    out = {"schema_version": 1, "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
           "base_library_sha256": base_sha, "library_sha256": fin_lib.tree_sha256() if write else None,
           "library_splits": list(LIBRARY_SPLITS), "sources": srcs, "skipped_sources": skipped,
           "counts": counts, "decls": rec_decls, "elapsed_s": round(time.monotonic() - t0, 1)}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "harvest.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    log(json.dumps(counts, indent=1))
    return out


def summarize(rec_decls):
    c = {"helper_theorems": len(rec_decls),
         "task_specific": sum(r["class"] == "task-specific" for r in rec_decls),
         "general_statements": sum(r["class"] == "general" for r in rec_decls)}
    g = [r for r in rec_decls if r["class"] == "general"]
    c["general_by_method"] = {m: sum(r.get("method") == m for r in g) for m in sorted({r.get("method") for r in g})}
    c["general_proof_rejected"] = sum(r.get("verdict") == "rejected" for r in g)
    c["general_checked"] = sum("statement_hash" in r for r in g)
    c["distinct_statements"] = len({r["statement_hash"] for r in g if "statement_hash" in r})
    reps = [r for r in g if "statement_hash" in r and "representative" not in r]
    c["by_verdict"] = {v: sum(r["verdict"] == v for r in reps) for v in sorted({r["verdict"] for r in reps})}
    c["duplicate_occurrences_of_checked_statements"] = sum("representative" in r for r in g)
    c["written"] = {"accepted": sum(r.get("verdict") == "accepted" and "final_name" in r for r in g),
                    "support": sum("support_of" in r for r in g)}
    return c


# ---------------------------------------------------------------------------------------------
# Measurement

SITE_TACTICS = ["rfl", "decide", "omega", "(intros; omega)", "simp", "simp_all", "fin_simp", "div_norm"]


def site_battery(k):
    """One line of tactics for obligation k: the fixed battery, then `exact?`; the trace
    messages say whether it closed the goal."""
    alts = " | ".join(f"(({t}) <;> done)" for t in SITE_TACTICS) + " | (exact?)"
    return f'(first | ((first | {alts}); trace "PFH_CLOSED_{k}") | (trace "PFH_OPEN_{k}"; sorry))'


def code_mask(text):
    """For each character, whether it is code (outside comments and strings)."""
    mask = [True] * len(text)
    depth, in_str, i, n = 0, False, 0, len(text)
    while i < n:
        if in_str:
            mask[i] = False
            if text[i] == "\\":
                if i + 1 < n:
                    mask[i + 1] = False
                i += 2
                continue
            if text[i] == '"':
                in_str = False
            i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            mask[i] = mask[i + 1] = False
            i += 2
            continue
        if depth:
            if text.startswith("-/", i):
                depth -= 1
                mask[i] = mask[i + 1] = False
                i += 2
                continue
            mask[i] = False
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for x in range(i, j):
                mask[x] = False
            i = j
            continue
        if text[i] == '"':
            in_str = True
            mask[i] = False
        i += 1
    return mask


def sorry_sites(text):
    mask = code_mask(text)
    return [m.start() for m in re.finditer(r"(?<![\w.'])sorry(?![\w'])", text) if mask[m.start()]]


def site_kind(text, pos):
    """'tactic' or 'term' for the `sorry` at `pos` (heuristic on the preceding code)."""
    before = text[:pos].rstrip()
    line_start = text.rfind("\n", 0, pos) + 1
    on_line = text[line_start:pos].strip()
    if re.search(r"(:=|\(|⟨|,|\bexact|\bfrom|\brefine|\buse|\bapply|\bshow .*\bfrom)$", before):
        return "term"
    if re.search(r"\bfun\b[^\n]*=>$", before) and not re.search(r"\bby\b[^\n]*$", text[line_start:pos]):
        return "term"
    if before.endswith("=>"):
        # An alternative: a tactic unless it belongs to a term-mode `match`.
        w = before.rfind(" with")
        if w < 0:
            return "term"
        ls = before.rfind("\n", 0, w) + 1
        head = before[ls:w]
        if re.search(r"(:=|\bexact|\(|\bfrom|=>)\s*match\b", head):
            return "term"
        if re.match(r"\s*match\b", head) and before[:ls].rstrip().endswith(":="):
            return "term"
        return "tactic"
    if re.search(r"(\bby|·|<;>|;|\bthen|\belse|\bnext)$", before) or on_line in ("", "·"):
        return "tactic"
    return "term"


def unresolved_candidates():
    """Final candidates of unresolved runs: Passport UNRESOLVED, or judge not ACCEPT with the
    executable passing (eval.json); refuted and non-building candidates are left out."""
    import passport
    out = []
    for pp in sorted((ROOT / "results").rglob("passport.json")):
        final = pp.parent / "final.lean"
        if not final.is_file() or "harvest-1" in pp.parts:
            continue
        p = json.loads(pp.read_text())
        if p.get("status") == "UNRESOLVED" and p.get("passport_sha256") == passport.content_hash(p) and \
                p["solution"]["files"].get("final.lean") == sha256_file(final):
            out.append({"kind": "passport", "task": p["task"]["id"], "file": rel(final), "passport_sha256": p["passport_sha256"]})
    for ev in sorted((ROOT / "results").rglob("eval.json")):
        final = ev.parent / "final.lean"
        if not final.is_file() or (ev.parent / "passport.json").is_file():
            continue
        e = json.loads(ev.read_text())
        if e.get("judge") != "ACCEPT" and e.get("binary") == "PASS" and e.get("final_sha256") == sha256_file(final):
            out.append({"kind": "eval", "task": e["task"], "file": rel(final), "eval_sha256": sha256_file(ev)})
    for i, c in enumerate(out):
        c["id"] = f"u{i:03d}"
        c["split"] = taskmod.load(c["task"]).split
    return out


def theorem_spans(text):
    """[(name, offset after the top-level `:=`, end offset, first line, last line)] of the
    theorems of a file."""
    lines = text.split("\n")
    offs = [0]
    for l in lines:
        offs.append(offs[-1] + len(l) + 1)
    out = []
    cs = chunks(text)
    for k, (line, t) in enumerate(cs):
        _, body = strip_prefix(t)
        attrs, mods, opens_in, kw, rest = split_header(body)
        if kw != "theorem":
            continue
        m = re.match(r"\s*(" + IDENT + r")", rest)
        if not m:
            continue
        start = offs[line] + t.find(rest) + m.end()
        i = top_level_assign(text[start: offs[line] + len(t)])
        if i < 0:
            continue
        end_line = cs[k + 1][0] if k + 1 < len(cs) else len(lines)
        out.append((m.group(1), start + i + 2, offs[line] + len(strip_trailing(t)), line + 1, end_line))
    return out


def add_import(text, mod="ProofForgeFin"):
    lines = text.split("\n")
    last = max([i for i, l in enumerate(lines) if l.startswith("import ")] or [-1])
    lines.insert(last + 1, f"import {mod}")
    return "\n".join(lines)


def measure_project(parent, c):
    """The task project of candidate `c` at parent/<id>, with the candidate as judged."""
    t = taskmod.load(c["task"])
    d = parent / c["id"]
    shutil.rmtree(d, ignore_errors=True)
    for r in taskmod.PROJECT_FILES:
        src = t.root / r
        if src.is_dir():
            shutil.copytree(src, d / r)
        else:
            d.mkdir(parents=True, exist_ok=True)
            shutil.copy(src, d / r)
    (d / "candidate").mkdir(parents=True, exist_ok=True)
    (d / "candidate/Solution.lean").write_text((ROOT / c["file"]).read_text())
    return d


def read_messages(f):
    msgs = []
    for line in (f.read_text(errors="replace").splitlines() if f.is_file() else []):
        if line.startswith("{"):
            try:
                msgs.append(json.loads(line))
            except ValueError:
                pass
    return msgs


def compile_all(parent, cands, script_of, timeout, log, chunk=8):
    """Run `script_of(c)` in parent/<id> for every candidate, `chunk` candidates per container
    with `parent` mounted; a candidate whose script did not finish has no `.done` file."""
    for group in batches(cands, chunk):
        script = "; ".join(f"(cd {c['id']} && {script_of(c)}; touch .done)" for c in group)
        r = in_container(parent, script, timeout=timeout)
        log(f"  {', '.join(c['id'] for c in group)}: {r['elapsed_ms'] // 1000} s")


def failing_theorems(text, messages):
    """The theorems of `text` with an error, and the errors outside every theorem."""
    spans = theorem_spans(text)
    failing, outside = [], []
    for m in messages:
        if m["severity"] != "error":
            continue
        sp = [s for s in spans if s[3] <= m["pos"]["line"] < s[4]]
        if sp:
            if sp[0] not in failing:
                failing.append(sp[0])
        else:
            outside.append(m["data"][:200])
    return failing, outside


def battery_text(text, failing, only=None):
    """The candidate with every open obligation replaced by the battery, importing the library;
    returns (text, [obligation records]). With `only`, only those obligations get the battery
    (the others keep their text)."""
    edits, obs = [], []
    fail_ranges = [(s[1], s[2]) for s in failing]
    k = 0
    for name, a, b, l0, l1 in failing:
        obs.append({"k": k, "kind": "failing theorem", "theorem": name, "line": l0})
        if only is None or k in only:
            edits.append((a, b, " by\n  " + site_battery(k)))
        k += 1
    for pos in sorry_sites(text):
        if any(a <= pos < b for a, b in fail_ranges):
            continue
        kind = site_kind(text, pos)
        line = text.count("\n", 0, pos) + 1
        th = [s[0] for s in theorem_spans(text) if s[3] <= line < s[4]]
        obs.append({"k": k, "kind": f"sorry ({kind})", "theorem": th[0] if th else None, "line": line})
        rep = site_battery(k) if kind == "tactic" else f"(by {site_battery(k)})"
        if only is None or k in only:
            edits.append((pos, pos + len("sorry"), rep))
        k += 1
    out = text
    for a, b, rep in sorted(edits, reverse=True):
        out = out[:a] + rep + out[b:]
    return add_import(out), obs


def read_sites(messages, obs):
    res = {}
    for o in obs:
        k = o["k"]
        closed = any(m["data"].strip() == f"PFH_CLOSED_{k}" for m in messages)
        opened = any(m["data"].strip() == f"PFH_OPEN_{k}" for m in messages)
        res[k] = "closed" if closed and not opened else "open" if opened else "not reached"
    return res


def try_this(messages, line):
    return [suggestion(m["data"]) for m in messages if "Try this" in m["data"] and m["pos"]["line"] == line]


def link_tree(src, dst):
    """A copy of `src` at `dst` made of hard links (the vendored packages are only read)."""
    shutil.copytree(src, dst, copy_function=os.link, symlinks=True)


LEAN_BATTERY = "lake env lean -DmaxErrors=1000000 -DmaxHeartbeats=4000000 --json candidate/Solution.lean"
GROUP = 6


def measure_unresolved(base, new, log, only=None):
    """Open obligations of unresolved runs, closed by the battery with the library before and
    after the harvest."""
    parent = WORK / "measure"
    shutil.rmtree(parent, ignore_errors=True)
    parent.mkdir(parents=True)
    cands = [c for c in unresolved_candidates() if only is None or c["id"] in only]
    log(f"{len(cands)} unresolved candidates")
    for c in cands:
        measure_project(parent, c)
    with limited():
        base_pkg = fin_lib.ensure_built(base) / fin_lib.VENDOR
        new_pkg = fin_lib.ensure_built(new) / fin_lib.VENDOR
    compile_all(parent, cands, lambda c: (
        f"lake build {taskmod.load(c['task']).lib} > build.log 2>&1; "
        "lake env lean -DmaxErrors=1000000 --json candidate/Solution.lean > judged.jsonl 2> judged.err"), 3600, log)
    ready = []
    for c in cands:
        d = parent / c["id"]
        text = (ROOT / c["file"]).read_text()
        if not (d / ".done").is_file():
            c["skipped"] = "the candidate did not compile within the time limit"
            continue
        failing, outside = failing_theorems(text, read_messages(d / "judged.jsonl"))
        if outside:
            c["skipped"] = f"errors outside every theorem: {outside[0][:160]}"
            continue
        obs = battery_text(text, failing)[1]
        c["obligations"] = obs
        if not obs:
            continue
        # At most GROUP obligations per file: a file with many `exact?` calls can exhaust the
        # container's memory, and Lean then stops before printing its messages.
        c["groups"] = batches([o["k"] for o in obs], GROUP)
        for j, ks in enumerate(c["groups"]):
            (d / f"Battery{j}.lean").write_text(battery_text(text, failing, set(ks))[0])
        link_tree(base_pkg, d / fin_lib.VENDOR)
        fin_lib.add_require(d)
        link_tree(new_pkg, d / ".pfnew")
        (d / ".done").unlink()
        ready.append(c)
    log(f"{len(ready)} candidates with open obligations, {sum(len(c['obligations']) for c in ready)} obligations")

    def runs(c, tag):
        return "; ".join(f"{LEAN_BATTERY.replace('candidate/Solution.lean', f'Battery{j}.lean')} > {tag}{j}.jsonl "
                         f"2> {tag}{j}.err; echo $? > {tag}{j}.rc" for j in range(len(c["groups"])))
    compile_all(parent, ready, lambda c: (
        f"{runs(c, 'base')}; rm -rf {fin_lib.VENDOR} && mv .pfnew {fin_lib.VENDOR} && {runs(c, 'harvest')}"),
        4 * 3600, log, chunk=4)
    for c in ready:
        d = parent / c["id"]
        for j, ks in enumerate(c["groups"]):
            btext = (d / f"Battery{j}.lean").read_text()
            mb, mh = read_messages(d / f"base{j}.jsonl"), read_messages(d / f"harvest{j}.jsonl")
            group = [o for o in c["obligations"] if o["k"] in ks]
            rb, rh = read_sites(mb, group), read_sites(mh, group)
            for o in group:
                k = o["k"]
                line = next((i + 1 for i, l in enumerate(btext.split("\n")) if f'"PFH_CLOSED_{k}"' in l), o["line"])
                o["base"], o["harvest"] = rb[k], rh[k]
                for tag in ("base", "harvest"):
                    rc = d / f"{tag}{j}.rc"
                    o[f"{tag}_exit"] = int(rc.read_text().strip()) if rc.is_file() and rc.read_text().strip() else None
                if rb[k] == "closed":
                    o["base_by"] = (try_this(mb, line) or ["a default tactic"])[0]
                if rh[k] == "closed":
                    o["harvest_by"] = (try_this(mh, line) or ["a default tactic"])[0]
        c["finished"] = (d / ".done").is_file()
        c.pop("groups")
    for c in cands:
        shutil.rmtree(parent / c["id"], ignore_errors=True)
    return cands


def reprove(project, occ, log, tag):
    """`exact?` on the statement of every occurrence, in the library of `project`; returns
    {id: suggestion or None}."""
    out = {}
    for bi, group in enumerate(batches(occ, 150)):
        doc = Doc()
        for d in group:
            doc.add(f"namespace PFR.{d['id']}")
            for o in d["opens"]:
                doc.add(f"open {o}")
            doc.add(f"set_option maxHeartbeats 200000 in\nexample{d['stmt']} := by exact?", key=d["id"])
            doc.add(f"end PFR.{d['id']}\n")
        f = f"Reprove{tag}{bi}.lean"
        (project / f).write_text(doc.text())
        msgs, _ = lean_json(project, [f], timeout=4 * 3600)
        for d in group:
            found = [m["data"] for m in doc.messages_in(msgs[f], d["id"]) if "Try this" in m["data"]]
            out[d["id"]] = suggestion(found[0]) if found and not doc.errors_in(msgs[f], d["id"]) else None
        log(f"re-prove {tag} batch {bi}: {sum(out[d['id']] is not None for d in group)} of {len(group)} closed")
    return out


def measure_reprove(rec, base, new, log):
    """Re-proving the general helper lemmas of verified candidates with one `exact?`: the
    harvested sources (a closure by a harvested lemma whose only source is the lemma's own
    candidate is counted as circular) and the held-out test-split sources."""
    srcs, _ = sources()
    by_id = {r["id"]: r for r in rec["decls"]}
    # Harvested lemma -> the sources of every occurrence of its statement.
    lemma_srcs = {}
    for r in rec["decls"]:
        if r.get("final_name"):
            h = r["statement_hash"]
            lemma_srcs[r["final_name"]] = {x["src"] for x in rec["decls"] if x.get("statement_hash") == h}
    occ_in = []
    for d in collect([s for s in srcs if s["harvest"]]):
        r = by_id.get(d["id"])
        if r and "statement_hash" in r:
            v = next(x for x in d["variants"] if x[0] == r["variant"])
            d["stmt"], d["prf"] = v[1], v[2]
            occ_in.append(d)
    held = collect([s for s in srcs if not s["harvest"]])
    pb = probe_project("reprove-base", base)
    p1 = pass_statements(pb, held, log)
    for d in held:
        c = choose_variant(d, p1)
        if c:
            d["variant"], d["stmt"], d["prf"], d["method"] = c
    general = [d for d in held if d.get("stmt") is not None]
    p2 = pass_proofs(pb, general, log)
    occ_out = [d for d in general if p2[d["id"]]["ok"]]
    log(f"held out: {len(held)} helper theorems, {len(general)} general, {len(occ_out)} checked")
    pn = probe_project("reprove-new", new)
    res = {}
    hashes = {d["id"]: by_id[d["id"]]["statement_hash"] for d in occ_in}
    hashes.update({d["id"]: p2[d["id"]]["hash"] for d in occ_out})
    for name, occ in (("harvested sources", occ_in), ("held-out test split", occ_out)):
        # One `exact?` per distinct statement.
        uniq = {}
        for d in occ:
            uniq.setdefault(hashes[d["id"]], d)
        b = reprove(pb, list(uniq.values()), log, "B")
        n = reprove(pn, list(uniq.values()), log, "N")
        rows = []
        for d in occ:
            u = uniq[hashes[d["id"]]]["id"]
            hb, hn = b[u], n[u]
            used = re.findall(rf"{re.escape(NAMESPACE)}\.([\w']+)", hn or "")
            circular = bool(used) and all(lemma_srcs.get(f"{NAMESPACE}.{u}", set()) <= {d["src"]} for u in used)
            rows.append({"id": d["id"], "task": d["task"], "name": d["name"], "proof_chars": size(d["prf"])["chars"],
                         "base": hb, "harvest": hn, "uses_harvested": bool(used), "circular": circular})
        closed_b = [r for r in rows if r["base"]]
        closed_n = [r for r in rows if r["harvest"] and not r["circular"]]
        gained = [r for r in closed_n if not r["base"]]
        byh = {}
        for r, d in zip(rows, occ):
            byh.setdefault(hashes[d["id"]], []).append(r)
        after = {h for h, v in byh.items() if any(r["harvest"] and not r["circular"] for r in v)}
        before = {h for h, v in byh.items() if any(r["base"] for r in v)}
        res[name] = {
            "lemmas": len(rows), "distinct_statements": len(uniq),
            "distinct_closed_before": len(before), "distinct_closed_after": len(after),
            "distinct_closed_only_after": len(after - before), "closed_before": len(closed_b), "closed_after": len(closed_n),
            "closed_only_after": len(gained), "closed_by_harvested_lemma": sum(r["uses_harvested"] and not r["circular"] for r in rows),
            "circular_excluded": sum(r["circular"] for r in rows),
            "proof_chars_of_gained": sum(r["proof_chars"] for r in gained),
            "replacement_chars_of_gained": sum(len("exact " + r["harvest"]) for r in gained),
            "rows": rows}
        log(f"{name}: {json.dumps({k: v for k, v in res[name].items() if k != 'rows'})}")
    return res


def cross_task(meas, rec):
    """Mark each re-proving row closed by a harvested lemma with whether that lemma was proved in
    a candidate of another task (`cross_task`), and count those rows per set."""
    tasks_of = {}
    for r in rec["decls"]:
        if r.get("final_name"):
            h = r["statement_hash"]
            tasks_of[r["final_name"]] = {x["task"] for x in rec["decls"] if x.get("statement_hash") == h}
    for res in meas["reprove"].values():
        for row in res["rows"]:
            used = re.findall(rf"{re.escape(NAMESPACE)}\.([\w']+)", row["harvest"] or "")
            row["cross_task"] = bool(used) and not row["circular"] and \
                any(tasks_of.get(f"{NAMESPACE}.{u}", set()) - {row["task"]} for u in used)
        gained = [r for r in res["rows"] if r["harvest"] and not r["circular"] and not r["base"]]
        res["closed_only_after_cross_task"] = sum(r["cross_task"] for r in gained)
    return meas


AUDIT_LINE = re.compile(r"audit: (\d+) constants, (\d+) theorems, (\d+) violations")


def kernels(log=print, full=False):
    """The harvested modules (or, with `full`, the whole library and its demonstrations) through
    the judge's six kernels and leanchecker (harness/fin_kernels.py), and the library's axiom
    audit (lib/Audit.lean); writes results/harvest-1/kernels.json."""
    import fin_kernels
    with limited():
        rep = fin_kernels.check(log=log, modules=None if full else [NAMESPACE])
        work = fin_kernels.ensure_built()
        r = in_container(work, "lake env lean Audit.lean > .lake/audit.log 2>&1; echo audit=$?")
    audit = (work / ".lake/audit.log").read_text(errors="replace")
    m = AUDIT_LINE.search(audit)
    used = re.search(r"axioms used: \[([^\]]*)\]", audit)
    rep["axiom_audit"] = {"exit": r["exit_code"], "line": m.group(0) if m else None,
                          "violations": int(m.group(3)) if m else None,
                          "axioms_used": [x.strip() for x in used.group(1).split(",")] if used else None}
    rep["passed"] = rep["passed"] and rep["axiom_audit"]["violations"] == 0 and \
        set(rep["axiom_audit"]["axioms_used"] or []) <= PERMITTED
    log(fin_kernels.summary(rep))
    log(f"axiom audit: {rep['axiom_audit']}")
    OUT.mkdir(parents=True, exist_ok=True)
    keep = {k: v for k, v in rep.items() if k not in ("rounds",)}
    keep["rounds"] = rep["rounds"]
    (OUT / ("kernels-full.json" if full else "kernels.json")).write_text(json.dumps(keep, indent=1) + "\n")
    return rep


def measure(log=print, only=None):
    """Both measurements; writes results/harvest-1/measure.json."""
    t0 = time.monotonic()
    rec = json.loads((OUT / "harvest.json").read_text())
    base = base_root()
    new = fin_lib.lib_root()
    if fin_lib.tree_sha256(base) == fin_lib.tree_sha256(new):
        raise RuntimeError("lib/ has no harvested modules; run `harvest.py run` first")
    out = {"schema_version": 1, "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
           "library_before_sha256": fin_lib.tree_sha256(base), "library_after_sha256": fin_lib.tree_sha256(new),
           "battery": SITE_TACTICS + ["exact?"]}
    out["reprove"] = measure_reprove(rec, base, new, log)
    cross_task(out, rec)
    cands = measure_unresolved(base, new, log, only)
    obs = [(c, o) for c in cands for o in c.get("obligations", [])]
    out["unresolved"] = {
        "candidates": len(cands), "skipped": sum("skipped" in c for c in cands),
        "obligations": len(obs),
        "closed_before": sum(o.get("base") == "closed" for _, o in obs),
        "closed_after": sum(o.get("harvest") == "closed" for _, o in obs),
        "closed_only_after": sum(o.get("harvest") == "closed" and o.get("base") != "closed" for _, o in obs),
        "closed_only_before": sum(o.get("base") == "closed" and o.get("harvest") != "closed" for _, o in obs),
        "not_reached": sum(o.get("base") == "not reached" or o.get("harvest") == "not reached" for _, o in obs),
        "lean_stopped": sum(any(o.get(f"{t}_exit") not in (0, 1) for t in ("base", "harvest")) for _, o in obs),
        "candidates_detail": cands}
    out["elapsed_s"] = round(time.monotonic() - t0, 1)
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "measure.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    log(json.dumps({k: v for k, v in out["unresolved"].items() if k != "candidates_detail"}, indent=1))
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("sources")
    r = sub.add_parser("run")
    r.add_argument("--no-write", action="store_true", help="do not write lib/ProofForgeFin/Harvested")
    k = sub.add_parser("kernels")
    k.add_argument("--all", action="store_true", help="check every library declaration, not only the harvested ones")
    m = sub.add_parser("measure")
    m.add_argument("--only", nargs="*", help="unresolved candidate ids (default: all)")
    a = ap.parse_args()
    if a.cmd == "sources":
        s, sk = sources()
        print(json.dumps({"sources": len(s), "harvested": sum(x["harvest"] for x in s), "skipped": sk}, indent=1))
    elif a.cmd == "run":
        run(write=not a.no_write)
    elif a.cmd == "kernels":
        sys.exit(0 if kernels(full=a.all)["passed"] else 1)
    elif a.cmd == "measure":
        measure(only=a.only)
