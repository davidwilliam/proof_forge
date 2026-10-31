#!/usr/bin/env python3
"""ProofForgeFin through the judge's kernels: every declaration of the library and of its
demonstrations, checked by the six kernels of `lake comparator --paranoid` and by leanchecker.

Everything runs in the pinned Lean image through the judge's container slots, one container at a
time (judge.in_container):

  build        lib/ (the package sources, the demonstrations and Audit.lean) is copied to a cache
               directory keyed by the hash of every file copied and built with `lake build`
               (targets ProofForgeFin and ProofForgeFinDemo). harness/FinDecls.lean then lists
               every constant declared in a `ProofForgeFin` or `ProofForgeFinDemo` module: name,
               module, kind, the library constants it uses, and whether it is or reaches an
               `unsafe` or `partial` constant.
  export       the toolchain's `leanexport`, the exporter Comparator runs, exports the named
               constants with everything they depend on, plus the targets Comparator adds to
               every export (the kernel's primitive constants, `Quot` and the permitted axioms).
               The safe part is every constant that reaches no `unsafe` or `partial` constant:
               the theorems, definitions, structures, instances and tactic code. Constants whose
               names the exporter cannot be given (private names, the environment extensions
               `register_simp_attr` declares) are in the export through the constants that use
               them, or are tactic state that no proof term can mention.
  comparator   `lake comparator --paranoid --challenge-from-export E --solution-from-export E
               --config C`: the judge's command (harness/judge.py) with the sandboxed build and
               export replaced by the export E, and C naming every theorem in E with the judge's
               permitted axioms. Comparator compares the statements (identical here), checks the
               axioms of every named theorem and runs its six kernels on E exactly as for a
               candidate, with its own command lines, kernel configuration and bubblewrap
               sandbox: Lean paranoid, lean4lean, nanoda, con-leche, con-ron, Lean default.
  attribution  a kernel stops at the first declaration it rejects. The checker reads the
               declaration from the kernel's output (con-leche and con-ron are run again directly
               with one worker for this: with one worker per hardware thread a declaration that
               exhausts their fuel can exhaust the container's memory first, and the kernel is
               killed before it names it), removes the declaration and every library constant
               that depends on it from the export, and runs Comparator again, until every kernel
               accepts. Each rejected declaration is then exported alone (with its
               dependencies) and run through Comparator again, which records every kernel that
               rejects it and why. A constant that depends on a rejected one is reported as not
               checked; it is checked once the rejected one is fixed.
  unsafe part  the constants that are or reach `unsafe` or `partial` code (here the
               `_unsafe_rec` definitions Lean generates to compile recursive definitions) are
               exported separately and run through the same kernels with `lake check --paranoid
               --from-export` (the same kernel runner as `lake comparator`; it needs no theorem
               names). nanoda, con-leche and con-ron decline `unsafe` and `partial` definitions by
               design; no safe constant mentions one, so no candidate's export contains one. Lean
               default, Lean paranoid and lean4lean must accept them.
  leanchecker  `lake env leanchecker M` for every module M that declares constants, one module
               at a time: the judge's replay, over the library and the demonstrations.

Fidelity. A judged candidate's export is the closure of its theorems in the same exporter
format, over a library built from the same sources by the same toolchain, so it contains the same
library constants with the same terms, and Comparator runs the same kernels with the same command
lines on it. Every kernel checks a declaration against the declarations it depends on (con-leche
and con-ron check each record from a fresh memo state, independent of the other records), so a
library declaration rejected here is rejected in the export of every candidate that depends on
it, and one accepted here is accepted there. The export checked here holds every library
declaration at once (about 21,600 records with their dependencies), more than any candidate's;
it runs within the judge's container limits (4 GB, one kernel worker per hardware thread).

Usage: fin_kernels.py [--json out.json] [--modules M ...]     exit 0 when every check passes
"""
import argparse, hashlib, json, pathlib, re, shutil, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import fin_lib, judge  # noqa: E402

ROOT = fin_lib.ROOT
DECLS_SOURCE = pathlib.Path(__file__).resolve().parent / "FinDecls.lean"
KERNELS = ["Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default"]
# Declining `unsafe` and `partial` definitions is the design of these three (harness/fin_kernels.py
# docstring); the unsafe part is held to the other three.
DECLINE_UNSAFE = {"nanoda", "con-leche", "con-ron"}
PERMITTED = ["propext", "Quot.sound", "Classical.choice"]   # as in every task's comparator.json
# Comparator's export targets besides the theorem and definition names (Lake.Check:
# builtinTargets with Quot.sound permitted, primitiveTargets).
COMPARATOR_TARGETS = [
    "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble",
    "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat",
    "List", "eagerReduce", "Nat", "String", "String.mk", "Char", "optParam", "autoParam",
    "semiOutParam", "outParam",
]
LEANEXPORT = "$(lean --print-prefix)/bin/leanexport"


def staged_files(root=None):
    """Relative paths of the lib/ files the checker builds: the package sources, the
    demonstrations and Audit.lean (the docs are left out)."""
    root = fin_lib.lib_root(root)
    out = list(fin_lib.source_files(root))
    out += [n for n in ("ProofForgeFinDemo.lean", "Audit.lean") if (root / n).is_file()]
    out += sorted(str(p.relative_to(root)) for p in (root / "ProofForgeFinDemo").rglob("*.lean")
                  if ".lake" not in p.relative_to(root).parts)
    return out


def tree_sha256(root=None):
    """Hash of every staged file and of FinDecls.lean."""
    root = fin_lib.lib_root(root)
    lines = "".join(f"{rel}\0{hashlib.sha256((root / rel).read_bytes()).hexdigest()}\n" for rel in staged_files(root))
    lines += f"FinDecls.lean\0{hashlib.sha256(DECLS_SOURCE.read_bytes()).hexdigest()}\n"
    return hashlib.sha256(lines.encode()).hexdigest()


def ensure_built(root=None, timeout=3600):
    """The cache directory with lib/ built and the declaration list written; built once per
    tree hash. Raises RuntimeError when the build or the listing fails."""
    root = fin_lib.lib_root(root)
    sha = tree_sha256(root)
    dst = fin_lib.CACHE / f"kernels-{sha}"
    if (dst / ".lake/decls.jsonl").is_file() and (dst / ".lake/built.json").is_file():
        return dst
    shutil.rmtree(dst, ignore_errors=True)
    dst.mkdir(parents=True)
    for rel in staged_files(root):
        (dst / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(root / rel, dst / rel)
    shutil.copy2(DECLS_SOURCE, dst / "FinDecls.lean")
    t0 = time.monotonic()
    r = judge.in_container(dst, "mkdir -p .lake; lake build > .lake/build.log 2>&1; rc=$?; tail -c 3000 .lake/build.log; "
                                "[ $rc -eq 0 ] || exit $rc; lake env lean FinDecls.lean > .lake/decls.tmp 2> .lake/decls.err; "
                                "rc=$?; tail -c 2000 .lake/decls.err; [ $rc -eq 0 ] && mv .lake/decls.tmp .lake/decls.jsonl; exit $rc",
                           timeout=timeout)
    if r["exit_code"] != 0:
        raise RuntimeError(f"library build for the kernel check failed (exit {r['exit_code']}):\n{r['output_tail'][-2500:]}")
    (dst / ".lake/built.json").write_text(json.dumps({"tree_sha256": sha, "judge_image": judge.image_id(),
                                                      "elapsed_ms": int((time.monotonic() - t0) * 1000)}) + "\n")
    return dst


def load_decls(work):
    out = {}
    for line in (work / ".lake/decls.jsonl").read_text().splitlines():
        if line.startswith("{"):
            d = json.loads(line)
            out[d["name"]] = d
    return out


def dependents(decls, names):
    """`names` and every library constant that depends on one of them, transitively."""
    users = {}
    for d in decls.values():
        for u in d["uses"]:
            users.setdefault(u, set()).add(d["name"])
    seen, todo = set(), list(names)
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        todo += users.get(n, ())
    return seen


def export(work, names, tag):
    """Export `names` and the Comparator targets with everything they depend on; returns the
    export's path relative to `work`."""
    rel = f".lake/kernels/{tag}.ndjson"
    (work / ".lake/kernels").mkdir(parents=True, exist_ok=True)
    (work / f".lake/kernels/{tag}.names").write_text("\n".join(list(names) + COMPARATOR_TARGETS + PERMITTED) + "\n")
    r = judge.in_container(work, f"lake env {LEANEXPORT} ProofForgeFin ProofForgeFinDemo -- "
                                 f"$(cat .lake/kernels/{tag}.names) > {rel} 2> .lake/kernels/{tag}.export.err; rc=$?; "
                                 f"tail -c 2000 .lake/kernels/{tag}.export.err; exit $rc", timeout=3600)
    if r["exit_code"] != 0:
        raise RuntimeError(f"export {tag} failed (exit {r['exit_code']}):\n{r['output_tail'][-2500:]}")
    return rel


SEGMENT = re.compile(r"^Running (.+?) kernel on solution$", re.M)


def kernel_verdicts(output):
    """Per kernel: {"accepted": bool, "output": the kernel's own lines}, from Comparator's
    report (`Running K kernel on solution` ... `K kernel accepts the solution`)."""
    out = {}
    marks = list(SEGMENT.finditer(output))
    for i, m in enumerate(marks):
        k = m.group(1)
        seg = output[m.end(): marks[i + 1].start() if i + 1 < len(marks) else len(output)]
        accepted = f"{k} kernel accepts the solution" in seg
        lines = [l for l in seg.strip().splitlines()
                 if not l.startswith((f"{k} kernel ", "Error while interacting", "error: ", "Your solution"))]
        out[k] = {"accepted": accepted, "output": "\n".join(lines)[-3000:]}
    return out


# The declaration a kernel names when it rejects one: con-leche and con-ron
# `... [at theorem <name>, fold position <n>]`; the others name it in their error message.
NAME_PATTERNS = [
    r"\[at \w+ ([^\s,\]]+), fold position",
    r"\bat (?:declaration |record \d+ )?[`'\"]?([^\s`'\":,()\]]+)",
    r"\b(?:declaration|theorem|definition) [`'\"]?([^\s`'\":,()\]]+)",
]
# Run directly (outside Comparator, for attribution only) when Comparator's report of a rejection
# names no declaration: one worker, so that the kernel reaches its own error (with many workers a
# declaration that exhausts the kernel's fuel can exhaust the container's memory first) and names
# the declaration.
DIRECT = {"con-leche": "con-leche --jobs=1 --progress=1", "con-ron": "con-ron --jobs=1 --progress=1"}


def named_declarations(text, decls):
    """Library constants named in a kernel's output, in order of appearance."""
    out = []
    for pat in NAME_PATTERNS:
        for m in re.finditer(pat, text):
            n = m.group(1).rstrip(".")
            if n in decls and n not in out:
                out.append(n)
    if not out:   # any library name the output mentions
        for tok in re.findall(r"[\w.'«»@]+", text):
            if tok in decls and tok not in out:
                out.append(tok)
    return out


def comparator(work, export_rel, theorems, tag):
    """`lake comparator --paranoid` on one export, as the judge runs it."""
    cfg = {"challenge_module": "ProofForgeFin", "solution_module": "ProofForgeFin",
           "theorem_names": list(theorems), "definition_names": [], "permitted_axioms": PERMITTED}
    (work / f".lake/kernels/{tag}.json").write_text(json.dumps(cfg) + "\n")
    r = judge.in_container(work, f"lake comparator --paranoid --config .lake/kernels/{tag}.json "
                                 f"--challenge-from-export {export_rel} --solution-from-export {export_rel} "
                                 f"> .lake/kernels/{tag}.log 2>&1; rc=$?; echo comparator=$rc; exit $rc", timeout=7200)
    log = (work / f".lake/kernels/{tag}.log").read_text(errors="replace")
    return {"exit_code": r["exit_code"], "elapsed_ms": r["elapsed_ms"], "kernels": kernel_verdicts(log),
            "log_tail": log[-6000:]}


def lake_check(work, export_rel, tag):
    """`lake check --paranoid --from-export`: the same kernel runner without a challenge."""
    r = judge.in_container(work, f"lake check --paranoid --from-export {export_rel} > .lake/kernels/{tag}.log 2>&1; "
                                 f"rc=$?; echo check=$rc; exit $rc", timeout=7200)
    log = (work / f".lake/kernels/{tag}.log").read_text(errors="replace")
    return {"exit_code": r["exit_code"], "elapsed_ms": r["elapsed_ms"], "kernels": kernel_verdicts(log),
            "log_tail": log[-6000:]}


def direct(work, kernel, export_rel):
    """The kernel's own report on an export, run directly with one worker (attribution only)."""
    r = judge.in_container(work, f"$(lean --print-prefix)/bin/{DIRECT[kernel]} {export_rel} > .lake/kernels/direct.log 2>&1; "
                                 "echo exit=$?; grep -E 'error|failed|declined|rejected|fuel' .lake/kernels/direct.log | tail -n 5",
                           timeout=7200)
    return r["output_tail"]


def leaf_modules(decls):
    """The modules that declare constants (no module whose name is a prefix of another declares
    any, so leanchecker, which checks every module under the name it is given, checks each once)."""
    return sorted({d["module"] for d in decls.values()})


def leanchecker(work, modules):
    """`lake env leanchecker M` for each module, one at a time (leanchecker replays the modules it
    is given in parallel, and all of them at once exceed the judge's container memory)."""
    (work / ".lake/kernels").mkdir(parents=True, exist_ok=True)
    (work / ".lake/kernels/modules.txt").write_text("\n".join(modules) + "\n")
    r = judge.in_container(work, "fail=0; for m in $(cat .lake/kernels/modules.txt); do "
                                 "out=$(lake env leanchecker $m 2>&1); rc=$?; "
                                 "if [ $rc -ne 0 ]; then fail=1; echo \"FAIL $m exit $rc: $(echo \"$out\" | tail -c 600)\"; fi; "
                                 "done; echo checked $(wc -l < .lake/kernels/modules.txt) modules; exit $fail", timeout=7200)
    failed = re.findall(r"^FAIL (\S+) exit (\d+)", r["output_tail"], re.M)
    return {"exit_code": r["exit_code"], "elapsed_ms": r["elapsed_ms"], "modules": len(modules),
            "failed": [m for m, _ in failed], "output_tail": r["output_tail"][-3000:]}


def theorems_of(decls, names):
    return [n for n in names if decls[n]["kind"] == "theorem"]


def select(decls, modules=None):
    """The declarations of the given modules and their submodules (every declaration when
    `modules` is None)."""
    if not modules:
        return dict(decls)
    return {n: d for n, d in decls.items()
            if any(d["module"] == m or d["module"].startswith(m + ".") for m in modules)}


def check(root=None, log=print, max_rounds=40, modules=None):
    """Run every check; returns the report (report["passed"] is the verdict). With `modules`,
    only the declarations of those modules (and their submodules) are exported and named to
    Comparator, with everything they depend on, and leanchecker replays only those modules."""
    t0 = time.monotonic()
    work = ensure_built(root)
    decls = load_decls(work)
    lib = select(decls, modules)
    if modules and not lib:
        raise RuntimeError(f"no declarations in modules {modules}")
    safe = sorted(n for n, d in lib.items() if d["exportable"] and not d["unsafe"])
    unsafe = sorted(n for n, d in lib.items() if d["exportable"] and d["unsafe"])
    report = {"modules": list(modules) if modules else None,
              "tree_sha256": tree_sha256(root), "library_source_tree_sha256": fin_lib.tree_sha256(root),
              "judge_image": judge.image_id(), "constants": len(lib),
              "theorems": sum(d["kind"] == "theorem" for d in lib.values()),
              "safe_exported": len(safe), "unsafe_exported": len(unsafe),
              "not_exportable": sorted(n for n, d in lib.items() if not d["exportable"]),
              "rounds": [], "failures": {}, "skipped_dependents": [], "unattributed": []}
    log(f"{len(lib)} library constants: {len(safe)} safe and {len(unsafe)} unsafe constants exported")

    # Safe part: Comparator rounds until every kernel accepts.
    excluded = set()
    for rnd in range(max_rounds):
        names = [n for n in safe if n not in excluded]
        rel = export(work, names, f"safe-{rnd}")
        res = comparator(work, rel, theorems_of(decls, names), f"safe-{rnd}")
        rejected = {k: v for k, v in res["kernels"].items() if not v["accepted"]}
        report["rounds"].append({"round": rnd, "exported": len(names), "exit_code": res["exit_code"],
                                 "elapsed_ms": res["elapsed_ms"],
                                 "kernels": {k: v["accepted"] for k, v in res["kernels"].items()}})
        log(f"round {rnd}: {len(names)} constants, comparator exit {res['exit_code']}, "
            f"rejected by {sorted(rejected) or 'none'} ({res['elapsed_ms'] // 1000} s)")
        missing = [k for k in KERNELS if k not in res["kernels"]]
        if res["exit_code"] == 0 and not rejected and not missing:
            break
        new = set()
        for k, v in rejected.items():
            named = named_declarations(v["output"], lib)
            why = v["output"]
            if not named and k in DIRECT:
                why = direct(work, k, rel)
                named = named_declarations(why, lib)
            if not named:
                report["unattributed"].append({"round": rnd, "kernel": k, "output": v["output"]})
                continue
            n = named[0]
            report["failures"].setdefault(n, {"module": lib[n]["module"], "kind": lib[n]["kind"], "first_round": {}})
            report["failures"][n]["first_round"][k] = why[-1500:]
            new.add(n)
        if not rejected or missing:
            report["unattributed"].append({"round": rnd, "kernel": None, "missing_kernels": missing,
                                           "output": res["log_tail"][-3000:]})
        if not new - excluded:
            break
        excluded |= dependents(lib, new)
    report["skipped_dependents"] = sorted(excluded - set(report["failures"]))

    # Every rejected declaration alone, through every kernel.
    for i, n in enumerate(sorted(report["failures"])):
        f = report["failures"][n]
        if not lib[n]["exportable"]:
            continue
        rel = export(work, [n], f"alone-{i}")
        res = comparator(work, rel, theorems_of(decls, [n]) or [], f"alone-{i}") if lib[n]["kind"] == "theorem" \
            else lake_check(work, rel, f"alone-{i}")
        f["alone"] = {}
        for k, v in res["kernels"].items():
            why = v["output"]
            if not v["accepted"] and k in DIRECT and not named_declarations(why, lib):
                why = direct(work, k, rel)
            f["alone"][k] = "accepts" if v["accepted"] else why[-1500:]
        log(f"alone {n}: rejected by {sorted(k for k, v in res['kernels'].items() if not v['accepted'])}")

    # Unsafe part: the kernels that check unsafe and partial definitions must accept it.
    if unsafe:
        rel = export(work, unsafe, "unsafe")
        res = lake_check(work, rel, "unsafe")
        report["unsafe"] = {"exit_code": res["exit_code"], "elapsed_ms": res["elapsed_ms"],
                          "kernels": {k: ("accepts" if v["accepted"] else v["output"][-800:]) for k, v in res["kernels"].items()}}
        bad = [k for k, v in res["kernels"].items() if not v["accepted"] and k not in DECLINE_UNSAFE]
        report["unsafe"]["passed"] = not bad and all(k in res["kernels"] for k in KERNELS)
        log(f"unsafe part: rejected by {sorted(k for k, v in res['kernels'].items() if not v['accepted']) or 'none'}"
            f" (declining unsafe and partial code is by design for {sorted(DECLINE_UNSAFE)})")

    report["leanchecker"] = leanchecker(work, leaf_modules(lib))
    log(f"leanchecker: exit {report['leanchecker']['exit_code']}")
    report["passed"] = (not report["failures"] and not report["unattributed"]
                        and report.get("unsafe", {}).get("passed", True)
                        and report["leanchecker"]["exit_code"] == 0)
    report["elapsed_ms"] = int((time.monotonic() - t0) * 1000)
    return report


def summary(report):
    lines = [f"library constants {report['constants']} (theorems {report['theorems']}); exported: safe "
             f"{report['safe_exported']}, unsafe {report['unsafe_exported']}; "
             f"not exportable by name {len(report['not_exportable'])}"]
    for n, f in sorted(report["failures"].items()):
        ks = sorted(k for k, v in f.get("alone", {}).items() if v != "accepts") or sorted(f["first_round"])
        lines.append(f"FAIL {n} ({f['kind']}, {f['module']}): rejected by {', '.join(ks)}")
        for k in ks:
            why = f.get("alone", {}).get(k) or f["first_round"].get(k, "")
            lines.append(f"     {k}: {why.strip().splitlines()[-1] if why.strip() else '(no output)'}")
    if report["skipped_dependents"]:
        lines.append(f"not checked separately (depend on a rejected declaration): {len(report['skipped_dependents'])}")
    for u in report["unattributed"]:
        lines.append(f"UNATTRIBUTED round {u['round']} kernel {u['kernel']}: {u['output'][-400:]}")
    if "unsafe" in report:
        lines.append(f"unsafe part (nanoda, con-leche, con-ron decline it by design): "
                     f"{json.dumps({k: v == 'accepts' for k, v in report['unsafe']['kernels'].items()})}")
    lines.append(f"leanchecker exit {report['leanchecker']['exit_code']}")
    lines.append("PASSED" if report["passed"] else "FAILED")
    return "\n".join(lines)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--json")
    ap.add_argument("--modules", nargs="*", help="check only these modules and their submodules (default: all)")
    a = ap.parse_args()
    rep = check(modules=a.modules or None)
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(rep, indent=2) + "\n")
    print(summary(rep))
    sys.exit(0 if rep["passed"] else 1)
