#!/usr/bin/env python3
"""Validate a task directory against the task contract (harness/task.py).

Checks, in order:
  1. metadata    task.json keys; Challenge, comparator.json, lakefile.toml and task.json agree
  2. lock        spec/locked.json covers exactly the protected files, with matching hashes
  3. hygiene     text rules over every task file
  4. references  every reference/*.lean is ACCEPTED by the judge and its binary PASSes
  5. start       candidate/Solution.lean compiles, is rejected, and its binary is REFUTED
  6. attacks     every candidate in attacks/attacks.json gets the expected verdicts from the
                 judge, the binary check and ordinary checking (harness/ordinary.py)

Usage: validate_task.py TASK [--cases N] [--json]   (writes TASK/validation.json)
"""
import argparse, json, pathlib, re, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import binary_check, judge, lock, ordinary, task as taskmod  # noqa: E402

KEYS = {"schema_version", "id", "family", "split", "lib", "namespace", "definitions",
        "requirements", "exe", "issue"}
FAMILIES = {"payouts", "transfers", "ledgers", "rate-limiters", "permissions", "queues"}
BANNED = [("\u2014", "em dash"), ("\u2013", "en dash")]


def metadata(t):
    p = []
    missing = KEYS - set(t.meta)
    if missing:
        p.append(f"task.json missing keys: {sorted(missing)}")
    if t.split not in ("dev", "val", "test"):
        p.append(f"split must be dev, val or test: {t.split}")
    if t.family not in FAMILIES:
        p.append(f"unknown family {t.family}")
    if t.root.name != t.id and t.root.name != "formal":
        p.append(f"directory name {t.root.name} differs from id {t.id}")
    ch = (t.root / t.spec_dir / "Challenge.lean")
    if not ch.exists():
        return p + [f"missing {t.spec_dir}/Challenge.lean"]
    text = re.sub(r"/-.*?-/", "", ch.read_text(), flags=re.S)
    if not re.search(rf"^namespace {re.escape(t.ns)}$", text, re.M):
        p.append(f"Challenge.lean has no `namespace {t.ns}`")
    for d in t.definitions:
        if not re.search(rf"^def {re.escape(d)}\b[^\n]*:= sorry$", text, re.M):
            p.append(f"Challenge.lean has no definition hole `def {d} ... := sorry`")
    stated = re.findall(r"^theorem\s+(\S+)", text, re.M)
    if sorted(stated) != sorted(t.theorems):
        p.append(f"Challenge theorems {stated} differ from task.json requirements {t.theorems}")
    for th in t.theorems:
        if not re.search(rf"^theorem\s+{re.escape(th)}\b[^\n]*:= sorry$", text, re.M):
            p.append(f"theorem {th} must be one line ending in `:= sorry`")
    cfg = json.loads((t.root / "spec/comparator.json").read_text())
    want = {"challenge_module": f"{t.lib}.Challenge", "solution_module": "Solution",
            "theorem_names": sorted(f"{t.ns}.{x}" for x in t.theorems),
            "definition_names": sorted(f"{t.ns}.{d}" for d in t.definitions),
            "permitted_axioms": sorted(["propext", "Quot.sound", "Classical.choice"])}
    for k, v in want.items():
        got = cfg.get(k)
        if (sorted(got) if isinstance(got, list) else got) != v:
            p.append(f"comparator.json {k} = {got}, expected {v}")
    lf = (t.root / "lakefile.toml").read_text()
    for needle in (f'name = "{t.lib}"', 'name = "Solution"', f'name = "{t.exe}"'):
        if needle not in lf:
            p.append(f"lakefile.toml lacks {needle}")
    if (t.root / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.35.0":
        p.append("lean-toolchain must be leanprover/lean4:v4.35.0")
    if not t.issue.strip():
        p.append("empty issue text")
    return p


def lock_check(t):
    p = []
    try:
        locked = t.locked()
    except FileNotFoundError:
        return ["spec/locked.json missing (run harness/lock.py)"]
    if locked["files"] != lock.manifest(t):
        p.append("spec/locked.json is stale (run harness/lock.py)")
    return p


def hygiene(t):
    p = []
    for f in sorted(t.root.rglob("*")):
        if not f.is_file() or ".lake" in f.parts or "__pycache__" in f.parts or f.name in ("validation.json",) or f.suffix in (".olean",):
            continue
        try:
            text = f.read_text()
        except UnicodeDecodeError:
            p.append(f"{f.relative_to(t.root)}: not UTF-8 text")
            continue
        rel = f.relative_to(t.root)
        for ch, name in BANNED:
            if ch in text:
                p.append(f"{rel}: contains {name}")
        if any(0x1F000 <= ord(c) <= 0x1FAFF or 0x2600 <= ord(c) <= 0x27BF for c in text):
            p.append(f"{rel}: contains emoji or pictograph")
        if re.search(r"^\s*(-{3,}|\*{3,}|_{3,})\s*$", text, re.M):
            p.append(f"{rel}: contains a horizontal divider line")
    return p


def verdicts(t, path, cases, seed=0):
    j = judge.judge(str(path), task=t)
    b = binary_check.check_binary(str(path), n_cases=cases, seed=seed, task=t)
    reasons = j["checks"]["tree"]["problems"] + j["checks"]["impl_scan"]["problems"]
    cmp_ = j["checks"].get("comparator")
    if cmp_ and cmp_["exit_code"] != 0:
        tail = [l.strip() for l in cmp_["output_tail"].splitlines() if "error" in l.lower()]
        reasons.append(tail[0] if tail else f"comparator exit {cmp_['exit_code']}")
    return {"judge": "ACCEPT" if j["accepted"] else "REJECT", "judge_reasons": reasons[:3],
            "judge_ms": j["elapsed_ms"], "binary": b["status"], "violations": b["violations"],
            "witness": b["witnesses"][0] if b["witnesses"] else None,
            "build_tail": b["build"].get("output_tail", "")[-1500:] if b["status"] == "BUILD_FAILED" else None}


def compiles_with_sorry(t, path):
    ws = judge.load_workspace(str(path))
    project = judge.fresh_project(ws, judge.candidate_files(ws), t)
    r = judge.in_container(project, "lake build Solution 2>&1 | tail -c 3000")
    return "error:" not in r["output_tail"], r["output_tail"][-1500:]


def validate(t, cases):
    rep = {"task": t.id, "split": t.split, "family": t.family, "checks": {}, "problems": []}
    P = rep["problems"]
    for name, fn in (("metadata", metadata), ("lock", lock_check), ("hygiene", hygiene)):
        probs = fn(t)
        rep["checks"][name] = {"passed": not probs, "problems": probs}
        P += probs
    if P:
        return rep
    refs = sorted((t.root / "reference").glob("*.lean"))
    if not refs:
        P.append("no reference/*.lean")
    rep["checks"]["references"] = {}
    for r in refs:
        v = verdicts(t, r, cases)
        rep["checks"]["references"][r.name] = v
        if v["judge"] != "ACCEPT":
            P.append(f"reference {r.name} rejected: {v['judge_reasons']}")
        if v["binary"] != "PASS":
            P.append(f"reference {r.name} binary {v['binary']}: {v['violations']} {v['build_tail'] or ''}")
    ok, tail = compiles_with_sorry(t, t.start)
    v = verdicts(t, t.start, cases)
    v["compiles"] = ok
    rep["checks"]["start"] = v
    if not ok:
        P.append(f"start candidate does not compile: {tail}")
    if v["judge"] != "REJECT":
        P.append("start candidate is accepted by the judge")
    if v["binary"] != "REFUTED":
        P.append(f"start candidate binary is {v['binary']}, expected REFUTED (the bug must be observable)")
    am = t.root / "attacks" / "attacks.json"
    rep["checks"]["attacks"] = {}
    if am.exists():
        for name, spec in json.loads(am.read_text()).items():
            v = verdicts(t, t.root / "attacks" / name, cases)
            o = ordinary.check(t, t.root / "attacks" / name)
            v["ordinary"] = "ACCEPT" if o["accepted"] else "REJECT"
            v["ordinary_reason"] = o["reason"]
            rep["checks"]["attacks"][name] = {**v, "expected": spec}
            if spec.get("ordinary", "any") != "any" and v["ordinary"] != spec["ordinary"]:
                P.append(f"attack {name}: ordinary checking {v['ordinary']} ({o['reason']}), expected {spec['ordinary']}")
            if v["judge"] != spec.get("judge", "REJECT"):
                P.append(f"attack {name}: judge {v['judge']}, expected {spec.get('judge', 'REJECT')}")
            if spec.get("binary", "any") != "any" and v["binary"] != spec["binary"]:
                P.append(f"attack {name}: binary {v['binary']}, expected {spec['binary']}")
    return rep


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("task")
    ap.add_argument("--cases", type=int, default=1000)
    ap.add_argument("--json", action="store_true", help="print the full report")
    a = ap.parse_args()
    t0 = time.monotonic()
    t = taskmod.load(a.task)
    rep = validate(t, a.cases)
    rep["passed"] = not rep["problems"]
    rep["elapsed_s"] = round(time.monotonic() - t0, 1)
    (t.root / "validation.json").write_text(json.dumps(rep, indent=2) + "\n")
    if a.json:
        print(json.dumps(rep, indent=2))
    print(("VALID" if rep["passed"] else "INVALID") + f"  {t.id}  ({rep['elapsed_s']} s)")
    for p in rep["problems"]:
        print(f"  - {p}")
    sys.exit(0 if rep["passed"] else 1)
