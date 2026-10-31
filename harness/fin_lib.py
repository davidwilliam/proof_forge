#!/usr/bin/env python3
"""ProofForgeFin in judged projects: version, vendoring, library scan and declaration index.

The library (Lake package `proofforge-fin`, library `ProofForgeFin`) is vendored into a fresh
project from the sources committed in lib/, never fetched:

  version     `source_tree_sha256`: SHA-256 over the relative path and SHA-256 of every file
              the package is built from (lakefile.toml, lake-manifest.json, lean-toolchain,
              ProofForgeFin.lean, ProofForgeFin/**/*.lean). The demonstrations
              (ProofForgeFinDemo), Audit.lean and the docs are not part of the package copy, so
              a candidate cannot import them.
  build       built once per version in the pinned Lean image (no network) from those sources,
              into a cache directory keyed by the version (PF_FIN_CACHE, default
              <tmp>/proofforge-fin). Lake's traces are content hashes, so a copy of the built
              package is up to date in any project directory.
  vendoring   when a candidate file imports a `ProofForgeFin` module, the fresh project gets the
              built package at .lake/packages/proofforge-fin (inside `.lake`, the only directory
              Comparator's sandbox lets a build write), a `[[require]]` with that path appended
              to its lakefile.toml and the matching entry in lake-manifest.json. A candidate that
              imports no library module gets a fresh project identical to one without the library.
  library     every library module the candidate imports, transitively, is scanned for the
  scan        constructs that make compiled code differ from checked code, add axioms or run
              code at build time (LIB_FORBIDDEN). Tactic and syntax definitions (`syntax`,
              `macro`, `elab_rules`, simprocs, `register_simp_attr`, `import Lean`) are allowed in
              library code only: they change how a proof is found, never what the kernel checks.
  index       `harness/FinIndex.lean`, run against the built library, lists every module doc and
              declaration (name, kind, module, signature as Lean prints it, doc string); the
              repair agent's library search reads it.

Usage: fin_lib.py [build | version | index QUERY... | scan MODULE...]
"""
import contextlib, fcntl, hashlib, json, math, os, pathlib, re, shutil, subprocess, sys, tempfile, threading, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import judge  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIB = ROOT / "lib"
PACKAGE = "proofforge-fin"
LIBRARY = "ProofForgeFin"
VENDOR = f".lake/packages/{PACKAGE}"
INDEX_SOURCE = pathlib.Path(__file__).resolve().parent / "FinIndex.lean"
CACHE = pathlib.Path(os.environ.get("PF_FIN_CACHE") or pathlib.Path(tempfile.gettempdir()) / "proofforge-fin")
IMPORT_RE = re.compile(rf"^({LIBRARY}(\..+)?)$")

# Library code: forbidden constructs (comments stripped). Code overrides and compiler hooks make
# the executable differ from the checked definitions; axioms, `sorry` and `native_decide`
# weaken what is proved; build-time commands run code when a candidate's project is built.
LIB_FORBIDDEN = [
    r"implemented_by", r"\bextern\b", r"\bunsafe\b", r"@\[\s*export", r"\binitialize\b",
    r"\bbuiltin_initialize\b", r"#eval", r"\brun_cmd\b", r"\brun_elab\b", r"\brun_meta\b",
    r"\bnative_decide\b", r"\bbv_decide\b", r"\bset_option\b", r"\bopaque\b", r"\baxiom\b",
    r"@\[\s*csimp", r"\bsorry\b", r"\bdebug\.", r"\bpartial\b",
]
LIB_IMPORTS = re.compile(rf"^({LIBRARY}(\..+)?|Init(\..+)?|Std(\..+)?|Lean(\..+)?)$")


_override = threading.local()


def lib_root(root=None):
    """The library source directory in use: `root` if given, else the one set by `using`, else lib/."""
    return pathlib.Path(root or getattr(_override, "root", None) or LIB)


@contextlib.contextmanager
def using(root):
    """Judge with the library sources at `root` (for example a past version recorded in a
    Passport) in the calling thread."""
    prev = getattr(_override, "root", None)
    _override.root = pathlib.Path(root)
    try:
        yield
    finally:
        _override.root = prev


def materialize(commit, sha):
    """The library sources of `commit`, extracted from git into the cache, if their tree hash is
    `sha`; None otherwise."""
    dst = CACHE / f"src-{sha}"
    if dst.is_dir() and tree_sha256(dst) == sha:
        return dst
    tmp = CACHE / f".src-{sha}-{os.getpid()}"
    shutil.rmtree(tmp, ignore_errors=True)
    tmp.mkdir(parents=True)
    try:
        arch = subprocess.run(["git", "archive", "--format=tar", commit, "lib"], cwd=ROOT, capture_output=True, timeout=120)
        if arch.returncode:
            return None
        subprocess.run(["tar", "-x", "-C", str(tmp)], input=arch.stdout, check=True, capture_output=True, timeout=120)
    except (OSError, subprocess.SubprocessError):
        shutil.rmtree(tmp, ignore_errors=True)
        return None
    if tree_sha256(tmp / "lib") != sha:
        shutil.rmtree(tmp, ignore_errors=True)
        return None
    shutil.rmtree(dst, ignore_errors=True)
    (tmp / "lib").rename(dst)
    shutil.rmtree(tmp, ignore_errors=True)
    return dst


def tree_sha256_at(commit):
    """`tree_sha256` of the library sources of `commit`, read from `git archive` without
    extracting it; None when the commit has no library. Cached by commit."""
    import io, tarfile
    cache = CACHE / "commit-trees.json"
    try:
        known = json.loads(cache.read_text())
    except (OSError, ValueError):
        known = {}
    if commit in known:
        return known[commit]
    try:
        arch = subprocess.run(["git", "archive", "--format=tar", commit, "lib"], cwd=ROOT, capture_output=True, timeout=120)
    except (OSError, subprocess.SubprocessError):
        return None
    if arch.returncode:
        sha = None
    else:
        files = {}
        with tarfile.open(fileobj=io.BytesIO(arch.stdout)) as tar:
            for m in tar.getmembers():
                if m.isfile() and m.name.startswith("lib/"):
                    files[m.name[4:]] = tar.extractfile(m).read()
        top = [n for n in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", f"{LIBRARY}.lean") if n in files]
        mods = sorted(n for n in files if n.startswith(f"{LIBRARY}/") and n.endswith(".lean") and ".lake" not in n.split("/"))
        sha = hashlib.sha256("".join(f"{r}\0{hashlib.sha256(files[r]).hexdigest()}\n" for r in top + mods).encode()).hexdigest() \
            if top else None
    known[commit] = sha
    try:
        CACHE.mkdir(parents=True, exist_ok=True)
        tmp = cache.with_suffix(f".{os.getpid()}.tmp")
        tmp.write_text(json.dumps(known, indent=0) + "\n")
        tmp.replace(cache)
    except OSError:
        pass
    return sha


def find_commit(sha, limit=200):
    """A commit whose library sources have tree hash `sha`: HEAD, then the last `limit` commits
    that changed lib/, newest first; None when none has it. For a Passport whose record names no
    commit (issued from library sources that were not committed yet and were committed as they
    were)."""
    try:
        log = subprocess.run(["git", "log", f"-{limit}", "--format=%H", "HEAD", "--", "lib"], cwd=ROOT,
                             capture_output=True, text=True, timeout=60)
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return None
    seen = []
    for c in [head.stdout.strip()] + log.stdout.split():
        if c and c not in seen:
            seen.append(c)
    for c in seen:
        if tree_sha256_at(c) == sha:
            return c
    return None


def root_for(rec):
    """The library sources a Passport's `library` record was judged with: None when that is
    this checkout's library (or the record vendored nothing); else the sources of the recorded
    commit, or of a commit found by `find_commit`, extracted into the cache. Returns
    (root, commit, note)."""
    rec = rec or {"vendored": False}
    sha = rec.get("source_tree_sha256")
    if not rec.get("vendored") or sha == tree_sha256():
        return None, None, None
    commit = rec.get("git_commit")
    root = materialize(commit, sha) if commit else None
    if root is None:
        commit = find_commit(sha)
        root = materialize(commit, sha) if commit else None
    if root is None:
        return None, None, (f"the Passport's library version {sha[:16]} is not this checkout's and no commit "
                            "provides it; check out the commit that has it")
    return root, commit, (f"the Passport's library version {sha[:16]} is not this checkout's; using the library "
                          f"sources of commit {commit[:12]}")


def strip_comments(text):
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", code)


def imports_of(text):
    return re.findall(r"^\s*import\s+(\S+)", strip_comments(text), flags=re.M)


def source_files(root=None):
    """Relative paths of the files the package is built from, sorted."""
    root = lib_root(root)
    out = [n for n in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", f"{LIBRARY}.lean")
           if (root / n).is_file()]
    out += sorted(str(p.relative_to(root)) for p in (root / LIBRARY).rglob("*.lean")
                  if ".lake" not in p.relative_to(root).parts)
    return out


def tree_sha256(root=None):
    root = lib_root(root)
    lines = "".join(f"{rel}\0{hashlib.sha256((root / rel).read_bytes()).hexdigest()}\n" for rel in source_files(root))
    return hashlib.sha256(lines.encode()).hexdigest()


def git_commit(root=None):
    """The commit whose library sources are exactly the ones vendored, or None when the
    sources have uncommitted changes or git is unavailable."""
    root = lib_root(root)
    try:
        files = [str((pathlib.Path(root) / rel).relative_to(ROOT)) for rel in source_files(root)]
        dirty = subprocess.run(["git", "status", "--porcelain", "--", *files], cwd=ROOT,
                               capture_output=True, text=True, timeout=30)
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, timeout=30)
    except (OSError, ValueError, subprocess.SubprocessError):
        return None
    if dirty.returncode or head.returncode or dirty.stdout.strip():
        return None
    return head.stdout.strip() or None


def module_file(mod, root=None):
    root = lib_root(root)
    return pathlib.Path(root) / (mod.replace(".", "/") + ".lean")


def library_imports(files):
    """The `ProofForgeFin` modules imported by the candidate files."""
    mods = set()
    for f in files:
        mods.update(m for m in imports_of(pathlib.Path(f).read_text()) if IMPORT_RE.match(m))
    return sorted(mods)


def closure(mods, root=None):
    """Library modules reachable from `mods` through imports; a module without a source file
    is kept (the build then fails on it) and not followed."""
    root = lib_root(root)
    seen, todo = set(), list(mods)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        f = module_file(m, root)
        if f.is_file():
            todo += [x for x in imports_of(f.read_text()) if IMPORT_RE.match(x)]
    return sorted(seen)


def scan(mods, root=None):
    """Library policy scan of the given modules."""
    root = lib_root(root)
    problems = []
    for m in mods:
        f = module_file(m, root)
        if not f.is_file():
            problems.append(f"no library module {m}")
            continue
        code = strip_comments(f.read_text())
        rel = f.relative_to(root)
        for pat in LIB_FORBIDDEN:
            for x in re.finditer(pat, code):
                problems.append(f"{rel}:{code[:x.start()].count(chr(10)) + 1}: forbidden in library code `{x.group(0)}`")
        for x in imports_of(f.read_text()):
            if not LIB_IMPORTS.match(x):
                problems.append(f"{rel}: library import not allowed: {x}")
    return {"passed": not problems, "problems": problems}


def record(files, root=None):
    """What the Passport binds about the library for these candidate files."""
    root = lib_root(root)
    mods = library_imports(files)
    rec = {"package": PACKAGE, "library": LIBRARY, "source_tree_sha256": tree_sha256(root),
           "imported": mods, "vendored": bool(mods)}
    if mods:
        mods_all = closure(mods, root)
        rec.update(modules=len(mods_all), scan=scan(mods_all, root), git_commit=git_commit(root))
    return rec


# ---------------------------------------------------------------------------------------------
# Build cache

MANIFEST_ENTRY = {"type": "path", "scope": "", "name": f"«{PACKAGE}»", "manifestFile": "lake-manifest.json",
                  "inherited": False, "dir": VENDOR, "copy": False, "configFile": "lakefile.toml"}
REQUIRE = (f'\n# Added by harness/fin_lib.py: ProofForgeFin, vendored from the committed library sources.\n'
           f'[[require]]\nname = "{PACKAGE}"\npath = "{VENDOR}"\n')


@contextlib.contextmanager
def _lock(path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def _copy_sources(root, dst):
    for rel in source_files(root):
        (dst / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(pathlib.Path(root) / rel, dst / rel)


def add_require(project):
    """Make `project` require the package vendored at VENDOR."""
    with open(project / "lakefile.toml", "a") as f:
        f.write(REQUIRE)
    mf = project / "lake-manifest.json"
    m = json.loads(mf.read_text())
    m["packages"] = [p for p in m.get("packages", []) if p.get("name") not in (PACKAGE, f"«{PACKAGE}»")] + [MANIFEST_ENTRY]
    mf.write_text(json.dumps(m, indent=1) + "\n")


def cache_dir(sha):
    return CACHE / sha


def ensure_built(root=None, timeout=3600):
    """The cache directory of this library version, building it first if needed. The build is a
    project at the cache directory that requires the package at VENDOR; it builds the library's
    `.olean` files and its static library objects (needed when an executable imports it) and
    writes the declaration index. Raises RuntimeError when the build fails."""
    root = lib_root(root)
    sha = tree_sha256(root)
    dst = cache_dir(sha)
    if (dst / "built.json").is_file():
        return dst
    with _lock(CACHE / f".lock-{sha}"):
        if (dst / "built.json").is_file():
            return dst
        stage = CACHE / f".stage-{sha}-{os.getpid()}"
        shutil.rmtree(stage, ignore_errors=True)
        pkg = stage / VENDOR
        pkg.mkdir(parents=True)
        _copy_sources(root, pkg)
        if tree_sha256(pkg) != sha:
            raise RuntimeError("library sources changed while they were copied")
        shutil.copy2(root / "lean-toolchain", stage / "lean-toolchain")
        (stage / "lakefile.toml").write_text('name = "pfFinBuild"\n')
        (stage / "lake-manifest.json").write_text(json.dumps(
            {"version": "1.3.0", "packagesDir": ".lake/packages", "packages": [], "name": "pfFinBuild",
             "lakeDir": ".lake", "fixedToolchain": False}, indent=1) + "\n")
        add_require(stage)
        shutil.copy2(INDEX_SOURCE, stage / "FinIndex.lean")
        t0 = time.monotonic()
        r = judge.in_container(stage, f"lake build {LIBRARY} {LIBRARY}:static > build.log 2>&1; rc=$?; "
                                      "tail -c 3000 build.log; [ $rc -eq 0 ] || exit $rc; "
                                      "lake env lean FinIndex.lean > index.jsonl 2> index.err; rc=$?; "
                                      "tail -c 2000 index.err; exit $rc", timeout=timeout)
        if r["exit_code"] != 0:
            shutil.rmtree(stage, ignore_errors=True)
            raise RuntimeError(f"ProofForgeFin build failed (exit {r['exit_code']}):\n{r['output_tail'][-2500:]}")
        (stage / "built.json").write_text(json.dumps({
            "source_tree_sha256": sha, "judge_image": judge.image_id(), "platform": judge.image_platform(),
            "lean": (root / "lean-toolchain").read_text().strip(), "elapsed_ms": int((time.monotonic() - t0) * 1000),
            "index_sha256": hashlib.sha256((stage / "index.jsonl").read_bytes()).hexdigest(),
            "built": time.strftime("%Y-%m-%dT%H:%M:%S%z")}, indent=2) + "\n")
        shutil.rmtree(dst, ignore_errors=True)
        stage.rename(dst)
    return dst


def vendor(project, files=None, root=None, force=False):
    """Vendor the built library into `project` when `files` import it (or when `force`).
    Returns the library record of `files`, or None when nothing was vendored."""
    root = lib_root(root)
    project = pathlib.Path(project)
    rec = record(files or [], root)
    if not (rec["vendored"] or force):
        return None
    built = ensure_built(root)
    pkg = built / VENDOR
    if tree_sha256(pkg) != rec["source_tree_sha256"]:
        raise RuntimeError(f"cached library at {built} does not match the library sources")
    shutil.copytree(pkg, project / VENDOR, symlinks=False)
    add_require(project)
    return rec


# ---------------------------------------------------------------------------------------------
# Declaration index and retrieval

def load_index(root=None):
    root = lib_root(root)
    path = ensure_built(root) / "index.jsonl"
    out = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            e = json.loads(line)
        except ValueError:
            continue
        if e["kind"] == "syntax":
            e = syntax_entry(e)
            if e is None:
                continue
        out.append(e)
    return out


def syntax_entry(e):
    """A syntax declaration as the index shows it: the simp set an attribute parser registers
    (its simplification-procedure twin is dropped), or the tactic, named by its keyword (the
    first code span of its doc string, else the syntax kind name without `tactic`)."""
    name, doc = e["name"], e.get("doc") or ""
    if name.startswith("Parser.Attr."):
        attr = name[len("Parser.Attr."):]
        if attr.endswith("_proc"):
            return None
        return {**e, "kind": "simp_set", "name": attr, "decl": name}
    m = re.match(r"\s*`([a-z_][\w]*)", doc)
    last = name.split(".")[-1]
    kw = m.group(1) if m else (last[len("tactic"):][:1].lower() + last[len("tactic") + 1:] if last.startswith("tactic") else last)
    return {**e, "kind": "tactic", "name": kw, "decl": name}


SYNONYMS = {
    "ceil": ["ceildiv", "up"], "ceiling": ["ceildiv", "up"], "floor": ["div", "down"], "round": ["rounding", "div"],
    "rounding": ["round", "div"], "share": ["shares", "vault"], "shares": ["share", "vault"], "vault": ["shares"],
    "sequence": ["run", "seq", "trace"], "sequences": ["run", "seq"], "operations": ["run", "ops"],
    "invariant": ["preserves", "run_invariant"], "induction": ["run_induction", "invariant"],
    "sum": ["sumover", "sum"], "total": ["sum", "sumover"], "conservation": ["sumover", "transfer"],
    "transfer": ["transfer", "move"], "balance": ["ledger", "adjust"], "reward": ["rewards", "accrue"],
    "rewards": ["reward", "credit"], "interest": ["index", "accrue"], "overflow": ["word", "bitvec", "lt"],
    "fixed": ["fixedpoint", "muldown", "mulup"], "point": ["fixedpoint"], "product": ["mul"],
    "multiply": ["mul"], "divide": ["div"], "division": ["div"], "quotient": ["div"],
    "potential": ["run_bound_via_potential", "accum"], "emitted": ["accum"], "reachable": ["reachable"],
    "record": ["struct_simp", "structure"], "projection": ["struct_simp"], "case": ["step_cases"],
}


def tokens(text):
    """Lower-case word tokens of identifiers and prose: split at dots, underscores, camel case
    and non-word characters, with a plural `s` removed."""
    out = []
    for w in re.findall(r"[A-Za-z][A-Za-z0-9']*", text or ""):
        parts = re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z0-9']+", w) or [w]
        out += [p.lower() for p in parts]
        if len(parts) > 1:
            out.append(w.lower())
    return [t[:-1] if len(t) > 3 and t.endswith("s") and not t.endswith("ss") else t for t in out]


class Index:
    """BM25 over each declaration's name (weighted 3), signature (1.5), doc string (1) and module
    (0.5); module docs and syntax (tactics) are entries too. With a goal (`search(..., goal=...)`),
    the ranking is goal-aware: BM25 combined with how well each theorem's conclusion matches the
    goal's (`conclusion_score`) and a usage prior from verified proofs (`USAGE`)."""
    WEIGHTS = {"name": 3.0, "signature": 1.5, "doc": 1.0, "module": 0.5}
    # Goal-aware combination: normalized BM25, normalized conclusion match, usage prior. Fixed on
    # the library's own proofs (results/feedback-library-1/retrieval.json, `tuning`), evaluated
    # on the demonstrations and on run candidates.
    MIX = {"bm25": 1.0, "shape": 1.0, "prior": 0.15}

    def __init__(self, entries, usage=None):
        self.entries = entries
        self.docs = []
        for e in entries:
            tf = {}
            for field, w in self.WEIGHTS.items():
                for t in tokens(e.get(field, "")):
                    tf[t] = tf.get(t, 0.0) + w
            self.docs.append(tf)
        self.avg = sum(sum(d.values()) for d in self.docs) / max(1, len(self.docs))
        df = {}
        for d in self.docs:
            for t in d:
                df[t] = df.get(t, 0) + 1
        n = len(self.docs)
        self.idf = {t: math.log(1 + (n - c + 0.5) / (c + 0.5)) for t, c in df.items()}
        # Conclusion shapes of the theorems and the inverse document frequency of their symbols.
        self.shapes = [entry_shape(e) for e in entries]
        cdf = {}
        for sh in self.shapes:
            for t in (sh["consts"] if sh else ()):
                cdf[t] = cdf.get(t, 0) + 1
        m = max(1, sum(1 for sh in self.shapes if sh))
        self.cidf = {t: math.log(1 + m / c) for t, c in cdf.items()}
        self.usage = usage if usage is not None else {}
        self.max_use = max(self.usage.values(), default=0)

    @classmethod
    def load(cls, root=None):
        root = lib_root(root)
        return cls(load_index(root), load_usage())

    def search(self, query, limit=10, kinds=None, goal=None):
        """The best matches, best first. A query that reads as a statement (`looks_like_goal`) is
        its own goal unless a goal is given; `goal=""` forces the BM25 ranking."""
        if goal is None and looks_like_goal(query):
            goal = query
        return [e for _, e in self.scored(query, limit, kinds, goal)]

    def bm25(self, query, kinds=None):
        """BM25 scores {entry index: score} of the entries that match `query`."""
        q = tokens(query)
        q += [s for t in list(q) for s in SYNONYMS.get(t, [])]
        exact = {w for w in re.findall(r"[\w.']+", query or "") if "." in w or "_" in w}
        out = {}
        k1, b = 1.2, 0.75
        for i, (e, d) in enumerate(zip(self.entries, self.docs)):
            if kinds and e["kind"] not in kinds:
                continue
            length = sum(d.values())
            s = 0.0
            for t in set(q):
                f = d.get(t)
                if f:
                    s += self.idf[t] * f * (k1 + 1) / (f + k1 * (1 - b + b * length / self.avg))
            if any(e["name"] == x or e["name"].endswith("." + x) for x in exact):
                s += 20.0
            if e["kind"] in ("instance", "def") and s:
                s *= 0.9
            if s > 0:
                out[i] = s
        return out

    def scored(self, query, limit=10, kinds=None, goal=None):
        """The best matches as (score, entry), best first. Without a goal the score is BM25 over
        `query` (as before the goal-aware ranking); with one it is the goal-aware combination."""
        bm = self.bm25(query, kinds)
        if not goal:
            scored = [(s, self.entries[i]) for i, s in bm.items()]
            scored.sort(key=lambda x: (-x[0], x[1]["name"]))
            return scored[:limit]
        g = text_shape(goal)
        shape = {}
        if g:
            for i, sh in enumerate(self.shapes):
                if sh and (not kinds or self.entries[i]["kind"] in kinds):
                    v = conclusion_score(g, sh, self.cidf)
                    if v > 0:
                        shape[i] = v
        top_bm, top_sh = max(bm.values(), default=0.0), max(shape.values(), default=0.0)
        lmax = math.log1p(self.max_use) if self.max_use else 0.0
        scored = []
        for i in set(bm) | set(shape):
            e = self.entries[i]
            v = (self.MIX["bm25"] * (bm.get(i, 0.0) / top_bm if top_bm else 0.0)
                 + self.MIX["shape"] * (shape.get(i, 0.0) / top_sh if top_sh else 0.0))
            if lmax:
                v += self.MIX["prior"] * math.log1p(self.usage.get(e["name"], 0)) / lmax
            scored.append((v, e))
        scored.sort(key=lambda x: (-x[0], x[1]["name"]))
        return scored[:limit]


# ---------------------------------------------------------------------------------------------
# Goal shapes: the conclusion of a goal or statement against the conclusions of the theorems

USAGE = pathlib.Path(__file__).resolve().parent / "fin_usage.json"

# Lean constants as the symbols a printed goal shows; other constants by their last component.
SYMBOL = {
    "HAdd.hAdd": "+", "HSub.hSub": "-", "HMul.hMul": "*", "HDiv.hDiv": "/", "HMod.hMod": "%",
    "HPow.hPow": "^", "HAppend.hAppend": "++", "Neg.neg": "neg", "Eq": "=", "Ne": "≠", "LE.le": "≤",
    "GE.ge": "≤", "LT.lt": "<", "GT.gt": "<", "Iff": "↔", "And": "∧", "Or": "∨", "Not": "¬",
    "Exists": "∃", "ite": "if", "dite": "if", "Membership.mem": "∈", "Nat.cast": "↑", "Int.cast": "↑",
    "NatCast.natCast": "↑", "IntCast.intCast": "↑", "Int.ofNat": "↑", "Min.min": "min", "Max.max": "max",
    "Dvd.dvd": "∣", "List.cons": "::", "HEq": "=", "Function.comp": "∘",
}
# Symbols that carry no shape information (types and literals).
NOISE = {"Nat", "Int", "Bool", "Prop", "OfNat.ofNat", "ofNat", "True", "False", "List", "Option", "Unit", "Type",
         "Sort", "Decidable", "instDecidableEqNat", "decide", "", "fun", "then", "else", "let", "have", "match",
         "with", "by", "do", "at", "show", "from"}
REL_SYMBOLS = [("↔", "↔"), ("≠", "≠"), ("≤", "≤"), ("≥", "≤"), ("<", "<"), (">", "<"), ("=", "=")]
SIDE_OPS = [("+", "-"), ("*", "/", "%"), ("^",)]


def symbol(name):
    """The symbol of a Lean constant for shape comparison."""
    if name in SYMBOL:
        return SYMBOL[name]
    return name.split(".")[-1] if name else ""


def load_usage(path=USAGE):
    """{declaration name: number of verified proofs that use it} (harness/fin_usage.json); empty
    when the file is absent."""
    try:
        return json.loads(pathlib.Path(path).read_text())["uses"]
    except (OSError, ValueError, KeyError):
        return {}


def entry_shape(e):
    """The conclusion shape of a theorem entry, {rel, lhs, rhs, consts}, from the index's `concl`
    record, else read from its signature; None for other entries."""
    if e.get("kind") != "theorem":
        return None
    c = e.get("concl")
    if isinstance(c, dict):
        consts = {symbol(x) for x in c.get("consts", [])} - NOISE
        return {"rel": symbol(c.get("rel", "")), "lhs": symbol(c.get("lhs", "")), "rhs": symbol(c.get("rhs", "")),
                "consts": consts}
    sig = e.get("signature") or ""
    name = e.get("name", "")
    if sig.startswith(name):
        sig = sig[len(name):]
    return text_shape(sig)


def _depth0(s):
    """For each index of `s`, whether it is outside brackets."""
    out, depth = [], 0
    for ch in s:
        if ch in "([{⟨⦃":
            depth += 1
        elif ch in ")]}⟩⦄":
            depth = max(0, depth - 1)
        out.append(depth == 0 and ch not in ")]}⟩⦄")
    return out


def _split_top(s, sep):
    """`s` split at the occurrences of `sep` outside brackets."""
    top, out, last, i = _depth0(s), [], 0, 0
    while i < len(s):
        if top[i] and s.startswith(sep, i):
            out.append(s[last:i])
            last = i + len(sep)
            i = last
            continue
        i += 1
    return out + [s[last:]]


def conclusion_text(text):
    """The conclusion of a goal (`⊢ ...`) or statement (`theorem n (x : T) : P → Q`): the text
    after the binders, the leading `∀ ...,` and the hypotheses."""
    t = text or ""
    if "⊢" in t:
        t = t.split("⊢")[-1]
        t = re.split(r"\n\s*\n|\ncase ", t)[0]
    else:
        t = re.sub(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma|example)\s*[^\s:({\[⦃]*", "", t)
        t = t.split(":=")[0]
        i = 0
        while True:
            while i < len(t) and t[i].isspace():
                i += 1
            if i < len(t) and t[i] in "([{⦃":
                depth = 0
                for j in range(i, len(t)):
                    if t[j] in "([{⦃⟨":
                        depth += 1
                    elif t[j] in ")]}⦄⟩":
                        depth -= 1
                        if depth == 0:
                            break
                i = j + 1
                continue
            break
        rest = t[i:]
        if rest.lstrip().startswith(":") and not rest.lstrip().startswith(":="):
            t = rest.lstrip()[1:]
        else:
            # No binders before a colon: a bare proposition, or `name : type` pairs.
            parts = _split_top(t, " : ")
            t = parts[-1] if len(parts) > 1 else t
    t = re.sub(r"\s+", " ", t).strip()
    while True:
        m = re.match(r"(∀|∃)\s*[^,]*?,\s*", t)
        if m and m.group(1) == "∀":
            t = t[m.end():]
            continue
        break
    parts = _split_top(t, "→")
    return parts[-1].strip()


IDENT_RE = re.compile(r"[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*")


def _side_head(s):
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        top = _depth0(s[1:-1])
        if all(top) or not top:
            break
        inner, depth, ok = s[1:-1], 0, True
        for ch in inner:
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
                if depth < 0:
                    ok = False
                    break
        if not ok:
            break
        s = inner.strip()
    for ops in SIDE_OPS:
        top = _depth0(s)
        for i in range(len(s) - 1, 0, -1):
            if top[i] and s[i] in ops and s[i - 1] == " " and i + 1 < len(s) and s[i + 1] == " ":
                return s[i] if s[i] != "%" else "%"
    if s.startswith("↑"):
        return "↑"
    if s.startswith("if "):
        return "if"
    if s.startswith("-"):
        return "neg"
    if s.startswith("("):
        # A projection or method of an application, `(xs.map f).sum`, `(step s r).snd.balance a`:
        # the last name of the chain after the closing bracket is the head.
        depth = 0
        for j, ch in enumerate(s):
            depth += ch in "([{⟨"
            depth -= ch in ")]}⟩"
            if depth == 0:
                m = re.match(r"\.(" + IDENT_RE.pattern + r")", s[j + 1:])
                if m:
                    return m.group(1).split(".")[-1]
                break
    m = re.match(r"\(?\s*(" + IDENT_RE.pattern + r")", s)
    head = m.group(1).split(".")[-1] if m else ""
    # A local variable is no head constant.
    return "" if re.fullmatch(r"[a-zα-ω][a-z0-9_'₀-₉]?", head) else head


def text_shape(text):
    """The conclusion shape of a goal or statement text: {rel, lhs, rhs, consts}, or None when it
    has no conclusion."""
    c = conclusion_text(text)
    if not c:
        return None
    rel, lhs, rhs = "", "", ""
    for sym, name in REL_SYMBOLS:
        parts = _split_top(c, f" {sym} ")
        if len(parts) >= 2:
            rel, lhs, rhs = name, _side_head(parts[0]), _side_head(f" {sym} ".join(parts[1:]))
            break
    if not rel:
        for sym in ("∧", "∨"):
            if len(_split_top(c, f" {sym} ")) >= 2:
                rel = sym
                break
    if not rel:
        rel = "¬" if c.startswith("¬") else _side_head(c)
    consts = {w.split(".")[-1] for w in IDENT_RE.findall(c)}
    consts |= {sym for sym in ("+", "-", "*", "/", "%", "^", "↑", "≤", "<", "=", "≠", "↔", "∧", "∨", "¬", "∃", "∈",
                               "min", "max", "∘", "++", "::")
               if sym in c}
    consts |= {"if"} if re.search(r"\bif\b", c) else set()
    consts |= {"≤"} if "≥" in c else set()
    consts |= {"<"} if ">" in re.sub(r"=>|->", "", c) else set()
    # Bound variables and short local names carry no shape.
    consts = {x for x in consts if not re.fullmatch(r"[a-z][a-z0-9_']?|h\w*|x\w*", x)} - NOISE
    return {"rel": rel, "lhs": lhs, "rhs": rhs, "consts": consts}


def conclusion_score(g, sh, idf):
    """How well a theorem's conclusion shape `sh` matches the goal shape `g`: the head relation,
    the heads of the two sides (either order for a symmetric relation) and the IDF-weighted
    overlap of the symbols (coverage of the theorem's and of the goal's)."""
    s = 0.0
    if g["rel"] and g["rel"] == sh["rel"]:
        s += 2.0
    elif {g["rel"], sh["rel"]} == {"≤", "<"}:
        s += 1.0
    if g["lhs"] or g["rhs"]:
        direct = 1.5 * bool(g["lhs"] and g["lhs"] == sh["lhs"]) + 1.5 * bool(g["rhs"] and g["rhs"] == sh["rhs"])
        swapped = 0.0
        if sh["rel"] in ("=", "↔", "≠"):
            swapped = 1.2 * bool(g["lhs"] and g["lhs"] == sh["rhs"]) + 1.2 * bool(g["rhs"] and g["rhs"] == sh["lhs"])
        s += max(direct, swapped)
    common = g["consts"] & sh["consts"]
    if common:
        w = sum(idf.get(t, 1.0) for t in common)
        s += 3.0 * w / max(1e-9, sum(idf.get(t, 1.0) for t in sh["consts"]))
        s += 2.0 * w / max(1e-9, sum(idf.get(t, 1.0) for t in g["consts"]))
    return s


def looks_like_goal(text):
    """Whether a search text reads as a statement or goal (it has a turnstile or a relation
    between terms) rather than keywords."""
    t = text or ""
    return "⊢" in t or bool(re.search(r"\S\s(=|≤|<|≠|↔|≥|>)\s\S", t))


def short_doc(doc, n=220):
    d = re.sub(r"\s+", " ", doc or "").strip()
    m = re.match(r"(.+?\.)(\s|$)", d)
    d = m.group(1) if m and len(m.group(1)) <= n else d
    return d if len(d) <= n else d[: n - 3] + "..."


def render(entries, sig_chars=400):
    lines = []
    for e in entries:
        sig = e.get("signature") or ""
        sig = sig if len(sig) <= sig_chars else sig[: sig_chars - 3] + "..."
        head = f"[{e['kind']}] {e['name']}" if e["kind"] != "module" else f"[module] {e['name']}"
        lines.append(f"{head}  (import {e['module']})" + (f"\n    {sig}" if sig and e["kind"] not in ("tactic", "simp_set", "module") else "")
                     + (f"\n    -- {short_doc(e.get('doc'))}" if e.get("doc") else ""))
    return "\n".join(lines)


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "version"
    if cmd == "version":
        print(json.dumps({"source_tree_sha256": tree_sha256(), "git_commit": git_commit(),
                          "files": len(source_files())}, indent=2))
    elif cmd == "build":
        d = ensure_built()
        print(d)
        print((d / "built.json").read_text())
    elif cmd == "index":
        print(render(Index.load().search(" ".join(sys.argv[2:]), limit=12)))
    elif cmd == "scan":
        mods = closure(sys.argv[2:] or [LIBRARY])
        print(json.dumps({"modules": len(mods), **scan(mods)}, indent=2))
    else:
        sys.exit(__doc__)
