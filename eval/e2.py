#!/usr/bin/env python3
"""E2: with the requirements held fixed, does protected enforcement reject bad artifacts
that ordinary checking accepts, without rejecting good ones?

Arms, on the same candidate artifacts:
  ordinary    the candidate's own project builds (candidate-supplied files override the
              task's, as in an unprotected repository), every required theorem name exists,
              and `#print axioms` shows no sorry and only permitted axioms
  proofforge  harness/judge.py (tree check, implementation scan, Comparator in a fresh
              sandbox, leanchecker) and harness/binary_check.py

Cases per task: seeded attacks (attacks/attacks.json, label bad), reference solutions,
accepted model repairs under formal/evidence, and generated harmless refactors of the
references (label good).

Usage: e2.py --label NAME [--split dev] [--tasks id,id] [--no-refactors] [--report-only]
"""
import argparse, json, pathlib, re, shutil, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import binary_check, judge, ordinary as ordinary_check, task as taskmod  # noqa: E402

CASES, SEED = 1000, 2


def proofforge(t, path):
    j = judge.judge(str(path), task=t)
    b = binary_check.check_binary(str(path), n_cases=CASES, seed=SEED, task=t)
    reasons = j["checks"]["tree"]["problems"] + j["checks"]["impl_scan"]["problems"]
    cmp_ = j["checks"].get("comparator")
    if cmp_ and cmp_["exit_code"] != 0:
        tail = [l.strip() for l in cmp_["output_tail"].splitlines() if "error" in l.lower()]
        reasons.append(tail[0][:160] if tail else f"comparator exit {cmp_['exit_code']}")
    if b["status"] != "PASS":
        reasons.append(f"binary {b['status']} {b['violations']}")
    return {"accepted": j["accepted"] and b["status"] == "PASS", "judge": j["accepted"],
            "binary": b["status"], "reason": "; ".join(reasons)}


# Names that also occur as tactics or keywords; renaming them would rewrite proof scripts.
RESERVED = {"apply", "exact", "intro", "intros", "cases", "simp", "rw", "omega", "decide", "show", "have",
            "induction", "rfl", "constructor", "split", "refine", "calc", "use", "ext", "trivial", "contradiction",
            "exists", "left", "right", "subst", "unfold", "assumption", "rcases", "obtain", "rintro", "by", "fun",
            "match", "let", "if", "then", "else", "do", "return", "at", "with", "from", "this", "step", "id"}


def refactor(t, src: str):
    """Harmless refactor: rename every helper declaration and add documentation comments."""
    protected = set(t.theorems) | set(t.definitions) | RESERVED
    names = [n for n in re.findall(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][\w']*)", src, re.M)
             if n not in protected]
    out = src
    for n in sorted(set(names), key=len, reverse=True):
        out = re.sub(rf"(?<![\w.']){re.escape(n)}(?![\w'?!])", f"aux_{n}", out)
    out = re.sub(r"^(theorem req_)", r"/-- Required theorem. -/\n\1", out, flags=re.M)
    return out if out != src else None


def collect(t, refactors=True):
    cases = []
    am = t.root / "attacks" / "attacks.json"
    if am.exists():
        for name, spec in json.loads(am.read_text()).items():
            if spec.get("judge", "REJECT") == "REJECT":
                cases.append({"case": f"attack:{name}", "path": t.root / "attacks" / name, "label": "bad",
                              "note": spec.get("note", ""), "complete": spec.get("ordinary") == "ACCEPT"})
    for r in sorted((t.root / "reference").glob("*.lean")):
        cases.append({"case": f"reference:{r.name}", "path": r, "label": "good", "note": "reference solution"})
        if refactors:
            new = refactor(t, r.read_text())
            if new:
                d = pathlib.Path(tempfile.mkdtemp(prefix="pf-refactor-")) / f"refactor_{r.name}"
                d.write_text(new)
                cases.append({"case": f"refactor:{r.name}", "path": d, "label": "good",
                              "note": "helpers renamed, comments added"})
    ev = t.root / "evidence"
    if ev.exists():
        for s in sorted(ev.glob("*/Solution.lean")):
            cases.append({"case": f"model-repair:{s.parent.name}", "path": s, "label": "good",
                          "note": "accepted model-authored repair"})
    return cases


def kind(r):
    """What a case is, from its records (for the composition table)."""
    c, pf, od = r["case"], r["proofforge"]["reason"], r["ordinary"]["reason"]
    if c.startswith("reference:"):
        return "reference solution"
    if c.startswith("refactor:"):
        return "generated refactor (helpers renamed, comments added)"
    if c.startswith("model-repair:"):
        return "accepted model repair"
    if "uses sorry" in od:
        return "attack with sorry"
    if "protected file modified" in pf:
        return "tampered workspace (modified spec or challenge)"
    if "implemented_by" in pf or "forbidden construct" in pf:
        return "code swap (implemented_by and similar)"
    if "has already been declared" in pf:
        return "redefines a protected definition"
    if "statement do not match" in pf:
        return "restated (weaker) theorem"
    return "other (" + (pf[:40] or od[:40]) + ")"


def binary_ok(r):
    return r["proofforge"].get("binary") == "PASS"


def render(out, rows):
    bad = [r for r in rows if r["label"] == "bad"]
    good = [r for r in rows if r["label"] == "good"]
    excluded = [r for r in rows if r["label"] == "excluded"]
    lines = ["# E2 results", "",
             "Same candidate artifacts in every arm. All bad cases are seeded tests written by the build team; the results describe this suite, not repairs in general.", "",
             "- Ordinary checking: the candidate's own project builds (its own spec files included), every required theorem name exists, and the axiom audit shows no `sorry` and only permitted axioms. It does not compare statements with the locked requirements, so an attack can prove a weaker statement under a required name.",
             "- Rebuild and tests: the executable rebuilt in a fresh container from the locked project plus the candidate passes the task's property tests (1,000 generated cases plus follow-ups).",
             "- ProofForge: tree check, implementation scan, Comparator against the locked challenge in a fresh sandbox, leanchecker, and the rebuild and tests.", "",
             "| Arm | Bad cases accepted | Good cases rejected |", "|---|---|---|"]
    arms = [("Ordinary checking", lambda r: r["ordinary"]["accepted"]),
            ("Rebuild and tests", binary_ok),
            ("ProofForge", lambda r: r["proofforge"]["accepted"])]
    for name, acc in arms:
        lines.append(f"| {name} | {sum(acc(r) for r in bad)}/{len(bad)} | {sum(not acc(r) for r in good)}/{len(good)} |")
    tests_miss = [r for r in bad if binary_ok(r)]
    lines += ["", f"Bad cases that pass the rebuild and tests: {len(tests_miss)}"
              + (" (" + ", ".join(f"{r['task']} {r['case']}" for r in tests_miss) + "); ProofForge rejects "
                 f"{sum(not r['proofforge']['accepted'] for r in tests_miss)} of them through proof checking." if tests_miss else ".")]
    if excluded:
        lines += ["", f"Excluded: {len(excluded)} generated refactors that do not compile (generator defects, not test cases)."]
    lines += ["", "## Composition", "", "| Label | Kind | Cases | Distinct source files | Ordinary accepts | Rebuild and tests accept | ProofForge accepts |",
              "|---|---|---|---|---|---|---|"]
    groups = {}
    for r in bad + good:
        groups.setdefault((r["label"], kind(r)), []).append(r)
    for (label, k), rs in sorted(groups.items()):
        lines.append(f"| {label} | {k} | {len(rs)} | {len({r['sha256'] or r['case'] for r in rs})} | "
                     f"{sum(r['ordinary']['accepted'] for r in rs)} | {sum(binary_ok(r) for r in rs)} | {sum(r['proofforge']['accepted'] for r in rs)} |")
    lines += ["", "Tasks that share a base specification reuse artifacts (references and attacks are often identical across variants), so cases are not independent examples; the distinct-source column counts unique files."]
    lines += ["", "## Per family", "", "| Family | Bad cases | Ordinary accepts bad | Rebuild and tests accept bad | ProofForge accepts bad | Good cases | ProofForge rejects good |",
              "|---|---|---|---|---|---|---|"]
    for fam in sorted({r["family"] for r in rows}):
        fb = [r for r in bad if r["family"] == fam]
        fg = [r for r in good if r["family"] == fam]
        lines.append(f"| {fam} | {len(fb)} | {sum(r['ordinary']['accepted'] for r in fb)} | {sum(binary_ok(r) for r in fb)} | "
                     f"{sum(r['proofforge']['accepted'] for r in fb)} | {len(fg)} | {sum(not r['proofforge']['accepted'] for r in fg)} |")
    lines += ["", "## Cases", "", "| Task | Case | Label | Ordinary | Rebuild and tests | ProofForge | ProofForge reason |", "|---|---|---|---|---|---|---|"]
    for r in rows:
        lines.append(f"| {r['task']} | {r['case']} | {r['label']} | {'accept' if r['ordinary']['accepted'] else 'reject'} | "
                     f"{r['proofforge'].get('binary', 'not run').lower()} | "
                     f"{'accept' if r['proofforge']['accepted'] else 'reject'} | {r['proofforge']['reason'][:140] or 'none'} |")
    (out / "e2.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines[:16]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--label", required=True)
    ap.add_argument("--split")
    ap.add_argument("--tasks")
    ap.add_argument("--no-refactors", action="store_true")
    ap.add_argument("--report-only", action="store_true")
    ap.add_argument("--parallel", type=int, default=2)
    ap.add_argument("--merge", action="store_true", help="replace only the given tasks' rows in an existing run")
    a = ap.parse_args()
    out = ROOT / "results" / f"e2-{a.label}"
    out.mkdir(parents=True, exist_ok=True)
    if a.report_only:
        render(out, json.loads((out / "e2.json").read_text())["rows"])
        return
    tasks = [taskmod.load(x) for x in a.tasks.split(",")] if a.tasks else taskmod.all_tasks(a.split)
    cases = [(t, c) for t in tasks for c in collect(t, not a.no_refactors)]
    rows, lock = [], threading.Lock()
    kept = []
    if a.merge and (out / "e2.json").exists():
        # Re-run only the given tasks; keep every other task's rows.
        ids = {t.id for t in tasks}
        kept = [r for r in json.loads((out / "e2.json").read_text())["rows"] if r["task"] not in ids]
    rows.extend(kept)

    def run_case(tc):
        t, c = tc
        row = {"task": t.id, "family": t.family, "split": t.split, "case": c["case"], "label": c["label"],
               "note": c["note"], "complete": c.get("complete", False), "sha256": taskmod.sha256(c["path"]) if c["path"].is_file() else None,
               "ordinary": ordinary_check.check(t, c["path"])}
        if c["case"].startswith("refactor:") and row["ordinary"]["reason"] == "build failed":
            # A generated refactor that does not compile is a generator defect, not a test case.
            row["label"] = "excluded"
            row["note"] = "generated refactor does not compile; excluded"
            row["proofforge"] = {"accepted": False, "reason": "not run"}
        else:
            row["proofforge"] = proofforge(t, c["path"])
        with lock:
            rows.append(row)
            print(f"[{t.id}] {c['case']} ({c['label']}): ordinary={row['ordinary']['accepted']} "
                  f"proofforge={row['proofforge']['accepted']}", flush=True)
            (out / "e2.json").write_text(json.dumps({"generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
                                                    "rows": rows}, indent=2) + "\n")

    with ThreadPoolExecutor(a.parallel) as ex:
        list(ex.map(run_case, cases))
    if not kept:
        order = {(t.id, c["case"]): i for i, (t, c) in enumerate(cases)}
        rows.sort(key=lambda r: order[(r["task"], r["case"])])
    (out / "e2.json").write_text(json.dumps({"generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "rows": rows}, indent=2) + "\n")
    render(out, rows)


if __name__ == "__main__":
    main()
