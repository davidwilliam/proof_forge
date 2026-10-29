#!/usr/bin/env python3
"""Proof Passport: the evidence record for one candidate of one task.

Statuses come only from the judge and binary-check records assembled here:
  VERIFIED    judge accepted (tree check, implementation scan, Comparator, leanchecker)
              and the binary rebuilt from the same source passed every property case
  REFUTED     the rebuilt binary violated the requirement on a concrete input (witness)
  UNRESOLVED  neither; for example the proof was rejected and no witness was found
The component is VERIFIED only when every requirement is.

Usage: passport.py <candidate.lean | workspace> [--task T] [--cases N] [--seed S]
                   [--provenance prov.json] [--out passport.json] [--markdown comment.md]
"""
import argparse, hashlib, json, pathlib, re, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import binary_check, judge, task as taskmod  # noqa: E402

SCHEMA = 1
TRUST = [
    "Lean v4.35.0 kernel, compiler and runtime",
    "the protected spec and locked challenge as reviewed by the owner",
    "Comparator and its bubblewrap sandbox",
    "the judge image (digest recorded below)",
    "the executable wrapper (app/Main.lean) is TESTED_ONLY, not proved",
]


def reconstruction(task):
    """The note a task reconstructed from published findings (because the original code is not
    public) puts on every Passport, from task.json `source.passport_note`; None otherwise."""
    src = task.meta.get("source") or {}
    return src.get("passport_note") if src.get("reconstructed") else None


def statement(task, theorem):
    text = (task.root / task.spec_dir / "Challenge.lean").read_text()
    m = re.search(rf"^theorem\s+{re.escape(theorem)}\s*:\s*(.*?)\s*:= sorry$", text, re.M)
    return m.group(1) if m else None


def docstring(task, theorem_stmt):
    """The protected predicate's docstring, for the plain-language requirement text."""
    if not theorem_stmt:
        return None
    pred = theorem_stmt.split()[0]
    text = (task.root / task.spec_dir / "Spec.lean").read_text()
    m = re.search(rf"/--((?:(?!-/).)*)-/\s*\ndef {re.escape(pred)}\b", text, re.S)
    return re.sub(r"\s+", " ", m.group(1)).strip() if m else None


def check_record(r):
    if r is None:
        return None
    return {k: r[k] for k in ("command", "exit_code", "elapsed_ms", "stdout_sha256", "stderr_sha256") if k in r}


def content_hash(p):
    """Digest all Passport content, excluding the digest field itself."""
    body = {k: v for k, v in p.items() if k != "passport_sha256"}
    return hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest()


def build(task, candidate, j, b, provenance=None):
    locked = task.locked()
    files = [pathlib.Path(p) for p in [candidate]] if pathlib.Path(candidate).is_file() else \
        judge.candidate_files(pathlib.Path(candidate))
    by_req = {}
    for w in b.get("witnesses", []):
        by_req.setdefault(w["requirement"], w)
    reqs = []
    for rid, th in task.requirements:
        stmt = statement(task, th)
        if j["accepted"] and b["status"] == "PASS":
            status = "VERIFIED"
        elif b.get("violations", {}).get(rid):
            status = "REFUTED"
        else:
            status = "UNRESOLVED"
        reqs.append({
            "id": rid, "theorem": f"{task.ns}.{th}", "statement": stmt,
            "statement_sha256": hashlib.sha256((stmt or "").encode()).hexdigest(),
            "text": docstring(task, stmt), "status": status,
            "axioms_used": (j.get("axioms_used") or {}).get(th),
            "witness": by_req.get(rid), "binary_violations": b.get("violations", {}).get(rid, 0)})
    component = "VERIFIED" if all(r["status"] == "VERIFIED" for r in reqs) else \
        "REFUTED" if any(r["status"] == "REFUTED" for r in reqs) else "UNRESOLVED"
    c = j["checks"]
    reasons = c["tree"]["problems"] + c["impl_scan"]["problems"]
    if c.get("comparator") and c["comparator"]["exit_code"] != 0:
        errs = [l.strip() for l in c["comparator"]["output_tail"].splitlines() if "error" in l.lower()]
        reasons.append(errs[0][:300] if errs else f"comparator exit {c['comparator']['exit_code']}")
    if c.get("leanchecker") and c["leanchecker"]["exit_code"] != 0:
        reasons.append(f"leanchecker exit {c['leanchecker']['exit_code']}")
    runs = [r for r in c.values() if isinstance(r, dict)] + [b.get("build") or {}]
    if any(judge.TIMEOUT_MARK in (r.get("output_tail") or "") for r in runs):
        reasons.append("time limit reached before checking finished; the result is UNRESOLVED, not a refutation")
    p = {
        "schema_version": SCHEMA,
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "task": {"id": task.id, "family": task.family, "namespace": task.ns,
                 "definitions": [f"{task.ns}.{d}" for d in task.definitions]},
        "status": component,
        "proof_check": {"accepted": j["accepted"], "reasons": reasons},
        "requirements": reqs,
        "locked": {"manifest_sha256": locked["manifest_sha256"], "files": locked["files"]},
        "toolchain": {"lean": (task.root / "lean-toolchain").read_text().strip(),
                      "judge_image": judge.image_id()},
        "solution": {"files": {str(f.name): taskmod.sha256(f) for f in files},
                     "solution_tree_sha256": j["solution_tree_sha256"]},
        "executable": {"target": task.exe, "sha256": b.get("binary_sha256"), "platform": judge.image_platform(),
                       "status": b["status"],
                       "wrapper": "TESTED_ONLY"},
        "checks": {
            "tree": c["tree"], "impl_scan": c["impl_scan"],
            "comparator": check_record(c.get("comparator")),
            "comparator_kernels": re.findall(r"^(.+?) kernel accepts the solution$",
                                             c.get("comparator", {}).get("output_tail", ""), re.M),
            "leanchecker": check_record(c.get("leanchecker")),
            "axiom_audit": check_record(c.get("axioms")),
            "property_tests": {"cases": b.get("cases"), "followup_cases": b.get("followup_cases"),
                               "seed": b.get("seed"), "violations": b.get("violations"),
                               "build": check_record(b.get("build"))},
        },
        "permitted_axioms": permitted_axioms(task),
        "trust_assumptions": TRUST,
        "scope": (f"Properties are proved about the pure definitions {', '.join(task.definitions)} in namespace "
                  f"{task.ns} for all inputs; the executable {task.exe} is built from the same source and "
                  "tested, and its JSON wrapper is not proved."),
        "provenance": provenance,
        "reproduce": f"bin/proofforge verify passport.json --candidate {candidate}",
        "timings_ms": {"judge": j["elapsed_ms"], "binary": b.get("elapsed_ms")},
    }
    note = reconstruction(task)
    if note:
        p["reconstruction"] = note
        p["trust_assumptions"] = TRUST + [note]
    p["passport_sha256"] = content_hash(p)
    return p


def markdown(p):
    """PR comment / terminal summary."""
    lines = [f"**ProofForge: {p['task']['id']} {p['status']}**", ""]
    if p.get("reconstruction"):
        lines += [p["reconstruction"], ""]
    lines += ["```"]
    w = max(len(r["id"]) for r in p["requirements"])
    for r in p["requirements"]:
        extra = ""
        if r["status"] == "VERIFIED":
            extra = f"statement sha256:{r['statement_sha256'][:12]}"
        elif r["witness"]:
            extra = f"witness: {r['witness']['message']}"
        lines.append(f"{r['id']:<{w}}  {r['status']:<10}  {extra}")
    ex = p["executable"]
    lines += [f"Executable {ex['target']} ({ex.get('platform', 'platform not recorded')}): sha256:{(ex['sha256'] or 'none')[:16]}  {ex['status']} "
              f"({p['checks']['property_tests']['cases']} cases + {p['checks']['property_tests']['followup_cases']} follow-ups); wrapper TESTED_ONLY",
              f"Locked manifest sha256:{p['locked']['manifest_sha256'][:16]}  Lean {p['toolchain']['lean'].split(':')[-1]}  "
              f"kernels: {', '.join(p['checks']['comparator_kernels']) or 'none'}",
              f"Solution tree sha256:{p['solution']['solution_tree_sha256'][:16]}  Passport sha256:{p['passport_sha256'][:16]}",
              "```", "", f"Reproduce: `{p['reproduce']}`"]
    if not p["proof_check"]["accepted"]:
        lines += ["", "Proof check rejected:"] + [f"- {x}" for x in p["proof_check"]["reasons"]]
    return "\n".join(lines) + "\n"


def permitted_axioms(task):
    """The configured axioms; empty when the configuration is missing or unreadable, which the
    tree check has already rejected."""
    try:
        return sorted(json.loads((task.root / "spec/comparator.json").read_text())["permitted_axioms"])
    except (OSError, ValueError, KeyError, TypeError):
        return []


def run(candidate, task, cases=2000, seed=0, provenance=None):
    j = judge.judge(str(candidate), task=task)
    b = binary_check.check_binary(str(candidate), n_cases=cases, seed=seed, task=task)
    b["seed"] = seed
    return build(task, str(candidate), j, b, provenance)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("candidate")
    ap.add_argument("--task")
    ap.add_argument("--cases", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--provenance")
    ap.add_argument("--out")
    ap.add_argument("--markdown")
    a = ap.parse_args()
    t = taskmod.load(a.task)
    prov = json.loads(pathlib.Path(a.provenance).read_text()) if a.provenance else None
    p = run(a.candidate, t, a.cases, a.seed, prov)
    if a.out:
        pathlib.Path(a.out).write_text(json.dumps(p, indent=2) + "\n")
    md = markdown(p)
    if a.markdown:
        pathlib.Path(a.markdown).write_text(md)
    print(md)
    sys.exit(0 if p["status"] == "VERIFIED" else 1)
