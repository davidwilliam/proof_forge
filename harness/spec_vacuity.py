#!/usr/bin/env python3
"""Vacuity probe for a specification strength report (harness/spec_strength.py).

A report shows a requirement not trivially true when some mutant's executable violates it, or
better, when the kernel accepts a refutation of it for some mutant. The property tests charge each
violation to one requirement (the oracle's choice), so a requirement can be broken by a killed
mutant without being named in its test results; `REQ-AUTHORIZATION` of transfers-overdraft is
charged to `REQ-INVALID-NOOP`, for example. This probe closes that gap where the task has a
counterexample adapter: for every requirement without a kernel-checked refutation in the report,
it instantiates that requirement on the recorded failing cases of the killed mutants (the inputs
and outputs of their counterexample attempts) and checks each generated refutation with the same
kernel checks as the report (Comparator with six kernels, leanchecker, axiom audit), stopping at
the first accepted one or after `--attempts` checked attempts.

The report is not modified. The probe writes `vacuity-probe.json` next to it, bound to the report
by `report_sha256` and hashed itself (`probe_sha256`). Mutant sources are regenerated from the
reference; the report must verify first (`spec_strength.verify_report`).

Usage: spec_vacuity.py REPORT [--attempts N]
"""
import argparse, hashlib, json, pathlib, shutil, sys, tempfile, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import counterexample as cexmod, judge, spec_strength as ss, task as taskmod  # noqa: E402

SYNC_ERROR = "candidate/Solution.lean"   # a parse error in the mutant itself: the file was read stale


def cases_of(m):
    """Distinct failing cases recorded for a mutant: (input, output, origin)."""
    out, seen = [], set()
    for a in m.get("counterexamples") or []:
        if a.get("input") is None:
            continue
        key = json.dumps([a.get("input"), a.get("output")], sort_keys=True)
        if key not in seen:
            seen.add(key)
            out.append((a.get("input"), a.get("output"), a.get("origin")))
    return out


def probe(report_path, attempts=60, log=print):
    report_path = pathlib.Path(report_path)
    rep = json.loads(report_path.read_text())
    task = taskmod.load(rep["task"]["id"])
    problems = ss.verify_report(rep, task)
    if problems:
        raise RuntimeError(f"report does not verify: {problems}")
    adapter_mod, _ = cexmod.adapter(task)
    targets = [v["requirement"] for v in rep["vacuity"] if v["not_trivially_true"] != "kernel-checked"]
    out = {"schema_version": 1, "kind": "proofforge-spec-vacuity-probe", "task": task.id,
           "report_sha256": rep["report_sha256"], "tool_sha256": taskmod.sha256(pathlib.Path(__file__)),
           "spec_strength_tool_sha256": ss.TOOL_SHA256, "attempts_per_requirement": attempts, "probes": []}
    if adapter_mod is None or not targets or not rep.get("supported"):
        out["note"] = ("no counterexample adapter" if adapter_mod is None else
                       "every requirement already has a kernel-checked refutation" if not targets else "task not measured")
        out["probe_sha256"] = probe_hash(out)
        return out
    gen = ss.mutants(task, rep["settings"].get("max_mutants"))
    sources = {m["id"]: m["source"] for m in gen["mutants"]}
    killed = [m for m in rep["mutants"] if m["status"] in ss.KILLED and cases_of(m)]
    judge.SLOT_DIR, judge.SLOTS = ss.SLOT_DIR, ss.SLOTS
    ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-sv-ws-"))
    (ws / "candidate").mkdir()
    (ws / "candidate" / "Solution.lean").write_text(gen["stripped"])
    project = judge.fresh_project(ws, judge.candidate_files(ws), task)
    shutil.rmtree(ws, ignore_errors=True)
    counter = ss._Counter()
    try:
        ss.add_cex_lib(project)
        (project / "mut").mkdir(exist_ok=True)
        (project / "mut" / "REF.lean").write_text(gen["stripped"])
        for rid in targets:
            rec = {"requirement": rid, "kernel_checked": False, "attempts": []}
            # mutants whose tests charged a violation to this requirement first, then the others
            order = sorted(killed, key=lambda m: not ((m.get("tests") or {}).get("violations", {}).get(rid)
                                                      or (m.get("extended_tests") or {}).get("violations", {}).get(rid)))
            checked = 0
            for m in order:
                if checked >= attempts or rec["kernel_checked"]:
                    break
                for inp, outp, origin in cases_of(m):
                    if checked >= attempts:
                        break
                    w = {"requirement": rid, "input": inp, "output": outp,
                         "message": f"vacuity probe of {rid} on a failing case of {m['id']}"}
                    if origin:
                        w["origin"] = origin
                    item = cexmod.generate(task, w)
                    if not item.get("lean_source"):
                        continue
                    for _ in range(2):   # one retry when the mounted file was read stale
                        ss.check_cex(project, task, sources[m["id"]], item, counter.next())
                        if item["kernel_checked"] or SYNC_ERROR not in str(item.get("reason")):
                            break
                        time.sleep(2)
                    checked += 1
                    rec["attempts"].append({"mutant": m["id"], **{k: item[k] for k in ss.CEX_KEYS if k in item}})
                    if item["kernel_checked"]:
                        rec["kernel_checked"], rec["mutant"] = True, m["id"]
                        break
            log(f"  {task.id} {rid}: " + (f"kernel-checked refutation for {rec['mutant']}" if rec["kernel_checked"]
                                          else f"no kernel-checked refutation in {checked} attempts"))
            out["probes"].append(rec)
    finally:
        shutil.rmtree(project, ignore_errors=True)
    out["probe_sha256"] = probe_hash(out)
    return out


def probe_hash(rec):
    body = {k: v for k, v in rec.items() if k != "probe_sha256"}
    return hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest()


def verify(probe_rec, report):
    """Problems with a probe record against its report (hashes only; no Lean)."""
    problems = []
    if probe_rec.get("probe_sha256") != probe_hash(probe_rec):
        problems.append("probe content hash differs")
    if probe_rec.get("report_sha256") != report.get("report_sha256"):
        problems.append("probe is for another report")
    return problems


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("report")
    ap.add_argument("--attempts", type=int, default=60)
    a = ap.parse_args(argv)
    rec = probe(a.report, a.attempts)
    (pathlib.Path(a.report).parent / "vacuity-probe.json").write_text(json.dumps(rec, indent=2, ensure_ascii=False) + "\n")
    for p in rec["probes"]:
        print(f"{p['requirement']:<28} {'KERNEL-CHECKED' if p['kernel_checked'] else 'not shown'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
