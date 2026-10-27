"""Task loader shared by the judge, the lock tool, the binary checker and the agents.

A task directory holds one locked Lean project plus its trusted test code:

  task.json                 metadata (below)
  lean-toolchain, lakefile.toml, lake-manifest.json
  spec/<Lib>/Spec.lean      protected requirement definitions
  spec/<Lib>/Lemmas.lean    protected helper lemmas visible to agents (optional)
  spec/<Lib>/Challenge.lean locked challenge: definition hole + required theorems
  spec/comparator.json      Comparator configuration
  spec/locked.json          hashes of every protected file (written by lock.py)
  app/Main.lean             JSON-lines executable wrapper (TESTED_ONLY)
  oracle.py                 independent Python model: gen_case, check, optional followup
  candidate/Solution.lean   starting candidate (buggy implementation, proofs `sorry`)
  reference/*.lean          build-team reference solutions (never shown to agents)
  attacks/*.lean            seeded attack candidates (optional)

task.json keys: id, family, split (dev | val | test), lib, namespace, definitions,
requirements ([[REQ-ID, theorem_name], ...] in the order agents attempt them),
exe, issue (the bug report given to agents).
"""
import hashlib, importlib.util, json, pathlib, sys, threading

ROOT = pathlib.Path(__file__).resolve().parent.parent
FLAGSHIP = ROOT / "formal"
TASKS = ROOT / "tasks"
PROJECT_FILES = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "spec", "app"]
_ORACLE_LOCK = threading.Lock()


def sha256(p: pathlib.Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


class Task:
    def __init__(self, root):
        self.root = pathlib.Path(root).resolve()
        self.meta = json.loads((self.root / "task.json").read_text())
        m = self.meta
        self.id, self.family, self.split = m["id"], m["family"], m["split"]
        self.lib, self.ns = m["lib"], m["namespace"]
        self.definitions = m["definitions"]
        self.requirements = [tuple(r) for r in m["requirements"]]
        self.theorems = [t for _, t in self.requirements]
        self.exe, self.issue = m["exe"], m["issue"]
        self.spec_dir = f"spec/{self.lib}"
        self.readable = [f"{self.spec_dir}/{n}.lean" for n in ("Spec", "Lemmas", "Challenge")
                         if (self.root / self.spec_dir / f"{n}.lean").exists()] + ["candidate/Solution.lean"]
        self._oracle = None

    def protected(self):
        """Relative paths of every Lean project file whose bytes are fixed by spec/locked.json.
        task.json and oracle.py are trusted harness inputs read only from the repository."""
        out = ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]
        for d in ("spec", "app"):
            out += sorted(str(p.relative_to(self.root)) for p in (self.root / d).rglob("*")
                          if p.is_file() and p.name != "locked.json" and ".lake" not in p.parts)
        return out

    def locked(self):
        return json.loads((self.root / "spec" / "locked.json").read_text())

    @property
    def oracle(self):
        if self._oracle is None:
            spec = importlib.util.spec_from_file_location(f"oracle_{self.id.replace('-', '_')}",
                                                          self.root / "oracle.py")
            with _ORACLE_LOCK:
                if self._oracle is None:
                    mod = importlib.util.module_from_spec(spec)
                    flag, sys.dont_write_bytecode = sys.dont_write_bytecode, True   # keep task dirs clean
                    try:
                        spec.loader.exec_module(mod)
                    finally:
                        sys.dont_write_bytecode = flag
                    self._oracle = mod   # published only once fully executed
        return self._oracle

    @property
    def start(self):
        return self.root / "candidate" / "Solution.lean"

    def __repr__(self):
        return f"Task({self.id}, {self.family}, {self.split})"


def load(arg=None) -> Task:
    """Load a task by directory path or by id under tasks/; default is the flagship."""
    if arg is None:
        return Task(FLAGSHIP)
    p = pathlib.Path(arg)
    if (p / "task.json").exists():
        return Task(p)
    if (TASKS / arg / "task.json").exists():
        return Task(TASKS / arg)
    if arg in ("flagship", "payout-flagship"):
        return Task(FLAGSHIP)
    raise FileNotFoundError(f"no task {arg}")


def all_tasks(split=None):
    out = [Task(FLAGSHIP)] + [Task(d) for d in sorted(TASKS.glob("*")) if (d / "task.json").exists()]
    return [t for t in out if split is None or t.split == split]
