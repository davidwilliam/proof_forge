#!/usr/bin/env python3
"""Library retrieval by goal shape: the usage prior and the offline evaluation.

No model is called. Lean runs in the pinned image (through harness/harvest.py's container limits).

  uses        every use of a library theorem in a tactic proof, with the goal the tactic that
              names it was run on, from Lean's info trees (harness/FinGoals.lean, which elaborates
              each file again with info trees and prints the main goal before the innermost
              tactic around each use; a use in a term-mode proof has no goal): the library's own
              modules, the harvested and salvaged modules and the demonstrations (in the
              kernel-check build of lib/), and the final candidates of runs that import the
              library (in their task projects; for a run that was not accepted only the
              declarations without `sorry` count, by the `sorry` check of FinGoals' caller).
  prior       harness/fin_usage.json: for each library theorem, the number of declarations whose
              proof uses it, over the demonstrations, the harvested and salvaged modules and the
              run candidates (the library's own proofs are left out: they reflect how the library
              is built, not what proofs about money code need).
  evaluation  one query per use with a goal: the goal is the query; the rank of the used lemma
              under the BM25 ranking (`Index.search(goal)` with no goal-aware part) and under the
              goal-aware ranking (`Index.search(goal, goal=goal)`) gives recall at 1, 5 and 10.
              The declaration being proved is left out of the ranking, and the usage prior leaves
              out the counts of the query's own source file. The library's own proofs are the
              tuning set of the mixing weights (`Index.MIX`); the demonstrations, the harvested
              and salvaged modules and the run candidates are the evaluation sets.

Usage: fin_retrieval.py uses [--results DIR] | prior | eval [--tune]
"""
import argparse, collections, json, math, pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import fin_kernels, fin_lib, harvest, mine, task as taskmod  # noqa: E402

ROOT = fin_lib.ROOT
OUT = ROOT / "results/feedback-library-1"
USES = OUT / "uses.json"
GOALS_SOURCE = pathlib.Path(__file__).resolve().parent / "FinGoals.lean"


def strip_ns(text):
    """A goal as a candidate that opens the library namespaces prints it."""
    return re.sub(r"\bProofForgeFin(?:Demo)?\.(?:[A-Z][\w']*\.)*", "", text or "")


def set_of(path):
    p = str(path)
    if "ProofForgeFinDemo" in p:
        return "demo"
    if "/Harvested" in p or "/Salvaged" in p:
        return "harvested"
    return "library"


def read_goals(f):
    out = []
    for line in (f.read_text(errors="replace").splitlines() if f.is_file() else []):
        if line.startswith("{"):
            try:
                out.append(json.loads(line))
            except ValueError:
                pass
    return out


EXE = """
[[lean_exe]]
name = "fingoals"
root = "FinGoals"
supportInterpreter = true
"""


def add_exe(d):
    """Add the `fingoals` executable to the project at `d` (its lakefile is rewritten, not
    edited through a hard link)."""
    import shutil
    shutil.copy2(GOALS_SOURCE, d / "FinGoals.lean")
    lf = d / "lakefile.toml"
    text = lf.read_text()
    lf.unlink()
    lf.write_text(text + EXE)


def per_file(files, out):
    """A shell loop running `fingoals` on each file, appending to `out`."""
    return "; ".join(f"lake env .lake/build/bin/fingoals {f} >> {out}.jsonl 2>> {out}.err" for f in files)


def library_uses(root=None, log=print, chunk=12):
    """Uses in the library, the harvested and salvaged modules and the demonstrations."""
    import shutil
    with harvest.limited():
        work = fin_kernels.ensure_built(root)
    d = harvest.WORK / f"goals-{fin_kernels.tree_sha256(root)[:16]}"
    shutil.rmtree(d, ignore_errors=True)
    harvest.link_tree(work, d)
    add_exe(d)
    files = [f for f in fin_kernels.staged_files(root) if f.endswith(".lean") and f.startswith("ProofForgeFin")
             and f not in ("ProofForgeFin.lean", "ProofForgeFinDemo.lean")]
    r = harvest.in_container(d, "lake build fingoals > exe.log 2>&1; rc=$?; tail -c 1500 exe.log; exit $rc", timeout=3600)
    if r["exit_code"] != 0:
        raise RuntimeError(f"fingoals build failed:\n{r['output_tail']}")
    rows = []
    for i, group in enumerate(harvest.batches(files, chunk)):
        harvest.in_container(d, per_file(group, f"goals{i}"), timeout=3600)
        got = read_goals(d / f"goals{i}.jsonl")
        log(f"library files {i * chunk}..{i * chunk + len(group)}: {len(got)} uses")
        for u in got:
            rows.append({"set": set_of(u["file"]), "source": u["file"], **{k: u[k] for k in ("decl", "lemma", "goal")}})
    return rows


def run_uses(results, root=None, log=print):
    """Uses in the final candidates of runs that import the library; for a run that was not
    accepted, declarations whose proof has `sorry` are left out."""
    import shutil
    rs = [r for r in mine.runs(results) if r["final"] and
          re.search(r"^import ProofForgeFin", pathlib.Path(r["final"]).read_text(errors="replace"), re.M)]
    exe = harvest.WORK / f"goals-{fin_kernels.tree_sha256(root)[:16]}/.lake/build/bin/fingoals"
    if not exe.is_file():
        raise RuntimeError("run library_uses first: it builds the fingoals executable")
    parent = harvest.WORK / "uses"
    shutil.rmtree(parent, ignore_errors=True)
    parent.mkdir(parents=True)
    with harvest.limited():
        pkg = fin_lib.ensure_built(root) / fin_lib.VENDOR
    cands = []
    for i, r in enumerate(rs):
        c = {"id": f"u{i:03d}", "task": r["task"], "file": r["final"], "run": r["run"], "outcome": r["outcome"]}
        d = harvest.measure_project(parent, c)
        (d / ".lake/build/bin").mkdir(parents=True, exist_ok=True)
        shutil.copy2(exe, d / ".lake/build/bin/fingoals")
        harvest.link_tree(pkg, d / fin_lib.VENDOR)
        fin_lib.add_require(d)
        cands.append(c)
    harvest.compile_all(parent, cands, lambda c: (
        f"lake build {taskmod.load(c['task']).lib} > build.log 2>&1; "
        "lake env .lake/build/bin/fingoals candidate/Solution.lean > uses.out 2> uses.err"), 3600, log)
    out = []
    for c in cands:
        text = pathlib.Path(c["file"]).read_text(errors="replace")
        sorry_decls = set()
        if c["outcome"] != "accepted":
            sites = harvest.sorry_sites(text)
            for name, a, b, _, _ in harvest.theorem_spans(text):
                if any(a <= x < b for x in sites):
                    sorry_decls.add(name.split(".")[-1])
        got = read_goals(parent / c["id"] / "uses.out")
        kept = [u for u in got if u["decl"].split(".")[-1] not in sorry_decls]
        for u in kept:
            out.append({"set": "runs", "source": c["run"], "outcome": c["outcome"],
                        **{k: u[k] for k in ("decl", "lemma", "goal")}})
        log(f"{c['run']} ({c['outcome']}): {len(got)} uses, {len(kept)} kept")
    return out


def build_prior(rows, index_names):
    """{"uses": {name: declarations}, "by_source": {source: {name: declarations}}} over the
    demonstrations, the harvested and salvaged modules and the run candidates."""
    seen = set()
    total, by = collections.Counter(), collections.defaultdict(collections.Counter)
    for r in rows:
        if r["set"] == "library" or r["lemma"] not in index_names or r["lemma"] == r["decl"]:
            continue
        key = (r["source"], r["decl"], r["lemma"])
        if key in seen:
            continue
        seen.add(key)
        total[r["lemma"]] += 1
        by[r["source"]][r["lemma"]] += 1
    return {"uses": dict(sorted(total.items())), "by_source": {k: dict(sorted(v.items())) for k, v in sorted(by.items())}}


def pairs(rows, theorems):
    """The uses with a goal, of an indexed theorem other than the declaration being proved, one per
    (source, declaration, lemma, goal)."""
    out, seen = [], set()
    for r in rows:
        if not r["goal"] or r["lemma"] not in theorems or r["lemma"] == r["decl"]:
            continue
        key = (r["source"], r["decl"], r["lemma"], r["goal"])
        if key not in seen:
            seen.add(key)
            out.append(r)
    return out


def ranks(idx, ps, prior, mix=None, limit=10):
    """For each use, the rank (1-based, None beyond `limit`) of the used lemma under BM25 and under
    the goal-aware ranking, with the declaration being proved left out and the prior without the
    use's own source."""
    out = []
    saved_mix, saved_usage, saved_max = dict(idx.MIX), idx.usage, idx.max_use
    if mix:
        idx.MIX = dict(mix)
    cache = {}
    for r in ps:
        key = (r["source"], r["decl"], r["goal"])
        if key not in cache:
            q = strip_ns(r["goal"])
            own = prior["by_source"].get(r["source"], {})
            idx.usage = {k: v - own.get(k, 0) for k, v in prior["uses"].items()}
            idx.max_use = max(idx.usage.values(), default=0)
            excl = {r["decl"]}
            old = [e["name"] for e in idx.search(q, limit=limit + 3, goal="") if e["name"] not in excl][:limit]
            new = [e["name"] for e in idx.search(q, limit=limit + 3, goal=q) if e["name"] not in excl][:limit]
            cache[key] = (old, new)
        old, new = cache[key]
        u = r["lemma"]
        out.append({"source": r["source"], "decl": r["decl"], "lemma": u,
                    "old": old.index(u) + 1 if u in old else None, "new": new.index(u) + 1 if u in new else None})
    idx.MIX, idx.usage, idx.max_use = saved_mix, saved_usage, saved_max
    return out


def recall(rs, k, which):
    return round(sum(1 for r in rs if r[which] and r[which] <= k) / len(rs), 4) if rs else None


def report(rs):
    return {"pairs": len(rs), "goals": len({(r["source"], r["decl"]) for r in rs}),
            **{f"{w}_recall@{k}": recall(rs, k, w) for w in ("old", "new") for k in (1, 5, 10)}}


def evaluate(root=None, tune=False, log=print):
    rows = json.loads(USES.read_text())["rows"]
    idx = fin_lib.Index.load(root)
    theorems = {e["name"] for e in idx.entries if e["kind"] == "theorem"}
    prior = build_prior(rows, theorems)
    out = {"index_entries": len(idx.entries), "theorems": len(theorems), "mix": dict(idx.MIX)}
    sets = collections.defaultdict(list)
    for r in rows:
        sets[r["set"]].append(r)
    out["uses"] = {k: {"uses": len(v), "with_goal": sum(bool(r["goal"]) for r in v)} for k, v in sorted(sets.items())}
    if tune:
        # Grid over the mixing weights on a sample of the library's own proofs.
        ps = pairs(sets["library"], theorems)
        ps = ps[::max(1, len(ps) // 1500)]
        grid = []
        for wb in (0.5, 1.0):
            for ws in (0.5, 1.0, 1.5, 2.0):
                for wp in (0.0, 0.15, 0.3):
                    rs = ranks(idx, ps, prior, {"bm25": wb, "shape": ws, "prior": wp})
                    grid.append({"mix": {"bm25": wb, "shape": ws, "prior": wp}, **report(rs)})
                    log(json.dumps(grid[-1]))
        best = max(grid, key=lambda g: (g["new_recall@10"], g["new_recall@5"], g["new_recall@1"]))
        out["tuning"] = {"pairs": len(ps), "grid": grid, "best": best["mix"]}
        idx.MIX = dict(best["mix"])
        out["mix"] = dict(idx.MIX)
    out["sets"], detail = {}, {}
    for name in ("library", "demo", "harvested", "runs"):
        ps = pairs(sets.get(name, []), theorems)
        rs = ranks(idx, ps, prior)
        out["sets"][name] = report(rs)
        detail[name] = rs
        log(f"{name}: {json.dumps(out['sets'][name])}")
    return out, detail, prior


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    u = sub.add_parser("uses")
    u.add_argument("--results", default=str(ROOT / "results"))
    sub.add_parser("prior")
    e = sub.add_parser("eval")
    e.add_argument("--tune", action="store_true")
    a = ap.parse_args()
    if a.cmd == "uses":
        rows = library_uses() + run_uses(a.results)
        OUT.mkdir(parents=True, exist_ok=True)
        USES.write_text(json.dumps({"library_sha256": fin_lib.tree_sha256(), "rows": rows}, indent=0) + "\n")
        print(json.dumps(collections.Counter(r["set"] for r in rows)))
    elif a.cmd == "prior":
        rows = json.loads(USES.read_text())["rows"]
        names = {e["name"] for e in fin_lib.load_index()}
        p = build_prior(rows, names)
        fin_lib.USAGE.write_text(json.dumps({"source": "results/feedback-library-1/uses.json",
                                             "uses": p["uses"]}, indent=1, sort_keys=True) + "\n")
        print(f"{len(p['uses'])} declarations with uses")
    elif a.cmd == "eval":
        out, detail, _ = evaluate(tune=a.tune)
        (OUT / "retrieval.json").write_text(json.dumps(out, indent=1) + "\n")
        (OUT / "retrieval-ranks.json").write_text(json.dumps(detail, indent=0) + "\n")
