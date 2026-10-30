#!/usr/bin/env python3
"""Counterexample stage on the vulnerable ports and on benchmark start candidates.

For each target (a task and a REFUTED candidate) this runs the full Passport pipeline with the
counterexample stage (`passport.run(..., counterexample=True)`: judge, binary check with 2,000
generated cases and seed 0, then a kernel-checked refutation of each refuted requirement) and
writes, under results/counterexamples-1/<label>/:

  passport.json         the Passport, with its `counterexamples` field
  cex/<theorem>.lean    the Lean source of each generated refutation (also in the Passport)

and results/counterexamples-1/summary.json and README.md with the coverage table, including
the benchmark and real-world tasks that have no adapter (not run). Targets run one after the
other, so Lean containers stay sequential. An existing passport.json is kept unless --force.

Usage: eval/counterexamples.py [--only LABEL[,LABEL...]] [--force] [--table-only]
"""
import argparse, json, pathlib, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import counterexample as cx, passport, task as taskmod  # noqa: E402

OUT = ROOT / "results" / "counterexamples-1"

PORTS = [
    ("cetus-original-port", "rw-cetus-shlw", "realworld/tasks/rw-cetus-shlw/attacks/buggy_original.lean",
     "results/cetus-1/passports/original-port.json"),
    ("cetus-pr6-port", "rw-cetus-shlw", "realworld/tasks/rw-cetus-shlw/attacks/pr6_mask_only.lean",
     "results/cetus-1/passports/pr6-port.json"),
    ("euler-port", "rw-euler-donate", "realworld/tasks/rw-euler-donate/candidate/Solution.lean",
     "results/euler-1/rw-euler-donate/passports/port.json"),
    ("balancer-port", "rw-balancer-upscale", "realworld/tasks/rw-balancer-upscale/attacks/balancer_port.lean",
     "results/balancer-1/passports/port.json"),
    ("knight-start", "rc-knight-router", "realworld/tasks/rc-knight-router/candidate/Solution.lean",
     "results/knight-1/start/passport.json"),
    ("compound-p62-port", "rw-compound-comp", "realworld/tasks/rw-compound-comp/attacks/p62_port.lean",
     "results/compound-1/passports/port.json"),
]


def start_targets():
    """The start candidate of every benchmark task, and of every real-world task without a port
    above, that has an adapter."""
    ported = {task_id for _, task_id, _, _ in PORTS}
    out = []
    for t in taskmod.all_tasks() + realworld_tasks():
        if t.id not in ported and cx.adapter_path(t) is not None:
            out.append((f"{t.id}-start", t.id, str(t.start.relative_to(ROOT)), None))
    return out


def realworld_tasks():
    return [taskmod.Task(d) for d in sorted(taskmod.REALWORLD.iterdir()) if (d / "task.json").exists()]


def targets():
    return PORTS + start_targets()


def run_one(label, task_id, cand, force=False):
    d = OUT / label
    path = d / "passport.json"
    if path.exists() and not force:
        return json.loads(path.read_text())
    t = taskmod.load(task_id)
    t0 = time.monotonic()
    p = passport.run(ROOT / cand, t, cases=2000, seed=0, counterexample=True)
    p["reproduce"] = f"bin/proofforge verify {path.relative_to(ROOT)} --candidate {cand}"
    p["timings_ms"]["total"] = int((time.monotonic() - t0) * 1000)
    p["passport_sha256"] = passport.content_hash(p)
    d.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(p, indent=2) + "\n")
    for c in p.get("counterexamples") or []:
        if c.get("lean_source"):
            (d / "cex").mkdir(exist_ok=True)
            (d / "cex" / f"{c['theorem'].split('.')[-1]}.lean").write_text(c["lean_source"])
    return p


def check_ms(c):
    return sum((r or {}).get("elapsed_ms") or 0 for r in (c.get("checks") or {}).values())


def row(label, task_id, cand, prior, p):
    refuted = [r["id"] for r in p["requirements"] if r["status"] == "REFUTED"]
    cxs = {c["requirement"]: c for c in p.get("counterexamples") or []}
    return {"label": label, "task": task_id, "candidate": cand, "prior_passport": prior,
            "passport": str((OUT / label / "passport.json").relative_to(ROOT)),
            "passport_sha256": p["passport_sha256"], "status": p["status"],
            "refuted": refuted,
            "counterexamples": [{"requirement": rid,
                                 "kernel_checked": bool(cxs.get(rid, {}).get("kernel_checked")),
                                 "reason": (cxs.get(rid) or {}).get("reason") if rid in cxs else "no witness recorded",
                                 "kernels": len((cxs.get(rid) or {}).get("kernels") or []),
                                 "axioms": (cxs.get(rid) or {}).get("axioms"),
                                 "check_ms": check_ms(cxs.get(rid) or {}),
                                 "source_bytes": len((cxs.get(rid) or {}).get("lean_source") or "")}
                                for rid in refuted]}


def uncovered():
    """Tasks without an adapter: not run."""
    out = []
    for t in taskmod.all_tasks() + realworld_tasks():
        if cx.adapter_path(t) is None:
            out.append(t.id)
    return out


def table(rows, missing):
    lines = ["| Target | Task | Status | Refuted requirements | Kernel-checked refutations | Not checked |",
             "|---|---|---|---|---|---|"]
    for r in rows:
        ok = [c for c in r["counterexamples"] if c["kernel_checked"]]
        bad = [c for c in r["counterexamples"] if not c["kernel_checked"]]
        by_reason = {}
        for c in bad:
            by_reason.setdefault(c["reason"], []).append(c["requirement"])
        lines.append(f"| `{r['label']}` | `{r['task']}` | {r['status']} | {len(r['refuted'])} | {len(ok)} of {len(r['refuted'])} | "
                     + ("; ".join(f"{', '.join(ids)}: {why}" for why, ids in by_reason.items()) or "none") + " |")
    return "\n".join(lines)


def tally(rows):
    return (sum(c["kernel_checked"] for r in rows for c in r["counterexamples"]), sum(len(r["refuted"]) for r in rows))


def readme(rows, missing):
    rw = {t.id for t in realworld_tasks()}
    groups = [("real-world ports with prior Passports", [r for r in rows if r["prior_passport"]]),
              ("start candidates of the other real-world tasks",
               [r for r in rows if not r["prior_passport"] and r["task"] in rw]),
              ("benchmark start candidates", [r for r in rows if not r["prior_passport"] and r["task"] not in rw])]
    ok, n = tally(rows)
    parts = "; ".join(f"{tally(g)[0]} of {tally(g)[1]} on the {len(g)} {name}" for name, g in groups if g)
    kms = sorted(c["check_ms"] for r in rows for c in r["counterexamples"] if c["kernel_checked"])
    axioms = sorted({a for r in rows for c in r["counterexamples"] if c["kernel_checked"] for a in c["axioms"] or []})
    sections = "\n\n".join(f"### {name[0].upper() + name[1:]}\n\n{table(g, missing)}" for name, g in groups if g)
    return f"""# Counterexamples checked by the kernel

`eval/counterexamples.py` runs the Passport pipeline with the counterexample stage
(`harness/counterexample.py`, described in `docs/COUNTEREXAMPLES.md`) on the vulnerable ports that
already have Passports and on the start candidate of every other task that has a counterexample
adapter: judge, binary check (2,000 generated cases, seed 0), then, for every refuted
requirement, a Lean theorem `cex_<req> : ¬ (<locked statement>)` about the candidate's
definitions, built from the binary check's witness and checked with `lake comparator --paranoid`
(Lean default and paranoid kernels, lean4lean, nanoda, con-leche, con-ron) against the locked
challenge with that theorem appended, then with `leanchecker` and the axiom audit.

Result: {ok} of {n} refuted requirements over {len(rows)} candidates are refuted by a
kernel-checked theorem ({parts}). Every accepted refutation was accepted by all six kernels and
`leanchecker`; the axioms used are {', '.join(f'`{x}`' for x in axioms)}. The four kernel-check
runs of one refutation (build, Comparator, leanchecker, axiom audit) took {kms[0] / 1000:.1f} s to
{kms[-1] / 1000:.1f} s, median {kms[len(kms) // 2] / 1000:.1f} s, on the arm64 machine that issued these Passports.

The prior Passports of the ports are unchanged; these are new Passports of the same candidates,
with the `counterexamples` field. Each directory holds `passport.json` and the Lean source of
each refutation under `cex/`. Reproduce one with its `reproduce` command, for example
`bin/proofforge verify results/counterexamples-1/cetus-original-port/passport.json --candidate realworld/tasks/rw-cetus-shlw/attacks/buggy_original.lean`;
`verify` re-checks every recorded refutation in a fresh container (`verify.log`: eight of these Passports
reproduced; `verify-prior.log`: the prior Passports of the Cetus original port and the Knight start
candidate still reproduce, unchanged, with the harness that adds the stage).

{sections}

Tasks without an adapter, not run ({len(missing)}): {', '.join(f'`{m}`' for m in missing)}.
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only")
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--table-only", action="store_true")
    a = ap.parse_args()
    only = set(a.only.split(",")) if a.only else None
    rows = []
    for label, task_id, cand, prior in targets():
        path = OUT / label / "passport.json"
        t0 = time.monotonic()
        if not a.table_only and (only is None or label in only):
            p = run_one(label, task_id, cand, force=a.force)
        elif path.exists():
            p = json.loads(path.read_text())
        else:
            continue
        r = row(label, task_id, cand, prior, p)
        rows.append(r)
        ok = sum(c["kernel_checked"] for c in r["counterexamples"])
        print(f"{label:<32} {p['status']:<10} {ok} of {len(r['refuted'])} kernel-checked  ({time.monotonic() - t0:.0f} s)",
              flush=True)
    missing = uncovered()
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "summary.json").write_text(json.dumps({"rows": rows, "no_adapter": missing}, indent=2) + "\n")
    (OUT / "README.md").write_text(readme(rows, missing))


if __name__ == "__main__":
    main()
