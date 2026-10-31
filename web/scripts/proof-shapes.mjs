// "The shape of a guarantee": for committed Muse runs on the flagship tasks, the declarations each
// requirement theorem (a guarantee) transitively uses, as the Lean kernel records them, and the
// holes (`sorry`) of the runs that did not verify. Writes generated/shapes/<slug>.json per run and
// generated/shapes/summary.json; tests/shapes.test.ts recomputes every measurement from the JSON
// and checks the source hashes against the committed files. No model calls.
//
// Per run it stages the task (realworld/tasks/<task>) with the run's final.lean as
// candidate/Solution.lean, vendors ProofForgeFin at the version the run used when the file imports
// it (harness/fin_lib.py), builds it in the pinned Lean image and runs the extractor of the home
// page graph (scripts/proof-graph/ProofGraph.lean) from the task's requirement theorems.
//
// Usage: node scripts/proof-shapes.mjs [slug ...]   (needs Docker and the proofforge-lean:4.35.0
//        image, or PF_LEAN_HOME set to an unpacked Lean release of the same version; with slugs,
//        only those runs are extracted again; the summary is always rewritten)
//        node scripts/proof-shapes.mjs --summary      (rewrite the summary from the committed files)

import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { readPassport, readRunSummary } from "./lib/results.mjs";

const here = path.dirname(new URL(import.meta.url).pathname);
const root = path.resolve(here, "../..");
const OUT = path.join(here, "../generated/shapes");
const IMAGE = "proofforge-lean:4.35.0";
const EXTRACTOR = "web/scripts/proof-graph/ProofGraph.lean";
const SCRIPT = "web/scripts/proof-shapes.mjs";
/** A Lean toolchain directory (the release archive of the task's lean-toolchain, unpacked) to build
 * with instead of the image, for when Docker is unavailable. The version is checked against the task. */
const LOCAL = process.env.PF_LEAN_HOME || null;

/** The runs. `verified`: a Muse repair with a VERIFIED Passport; `attempt`: a run that did not verify. */
export const RUNS = [
  { slug: "verified-balancer", role: "verified", task: "rw-balancer-upscale", name: "Balancer V2", run: "results/balancer-1/repair-A2-1" },
  { slug: "verified-cetus", role: "verified", task: "rw-cetus-shlw", name: "Cetus", run: "results/cetus-1/repair-A1-1" },
  { slug: "verified-euler", role: "verified", task: "rw-euler-donate", name: "Euler Finance", run: "results/euler-1/rw-euler-donate/repair-A1-1" },
  { slug: "verified-hundred", role: "verified", task: "rw-hundred-vault", name: "Hundred Finance", run: "results/vault-1/repair-A1-1" },
  { slug: "verified-knight", role: "verified", task: "rc-knight-router", name: "Knight Capital", run: "results/knight-1/A2-2" },
  { slug: "holes-compound-A0-1", role: "attempt", task: "rw-compound-comp", name: "Compound", run: "results/library-1/rw-compound-comp/A0-1" },
  { slug: "holes-compound-A2-2", role: "attempt", task: "rw-compound-comp", name: "Compound", run: "results/library-1/rw-compound-comp/A2-2" },
  { slug: "holes-compound-A2-topdown-3", role: "attempt", task: "rw-compound-comp", name: "Compound", run: "results/library-1/rw-compound-comp/A2-topdown-3" },
  { slug: "holes-balancer-A0-1", role: "attempt", task: "rw-balancer-upscale", name: "Balancer V2", run: "results/library-1/rw-balancer-upscale/A0-1" },
];

export const DEFINITIONS = {
  guarantee: "One locked requirement theorem of the task (task.json, spec/<lib>/Challenge.lean). Its statement in plain language is the doc comment of the property it asserts in the locked specification, quoted with line breaks joined by spaces; `readme` is the row of the task README's requirement table that names it, when there is one.",
  shape: "The set of declarations the guarantee uses, directly or through others, following the constants the Lean kernel records in each declaration's type and value (the rule of the home page graph, under `rule`). The guarantee itself is not counted.",
  size: "The number of declarations in the shape.",
  depth: "The longest chain of uses from the guarantee down to a declaration that uses no other node: 0 for a declaration that uses none, else one more than its deepest dependency.",
  width: "width[d] is the number of declarations of the shape whose own depth is d, for d from 0 to depth - 1.",
  loadBearing: "`every`: the declarations in the shape of every guarantee of the task. `lemmas`: each lemma (a theorem that is not a requirement) in any shape, with the number of guarantees whose shape contains it.",
  hole: "A declaration whose type or value contains `sorryAx`, as the Lean kernel records it (an explicit `sorry`: `sorry`; one Lean inserted for an elaboration error: `error`), including a required theorem left `sorry`. Only declarations in some shape are seen this way; a `sorry` in a declaration of the candidate that no guarantee reaches is listed under build.sorryOutsideShapes, from Lean's `declaration uses 'sorry'` warnings, and no guarantee hangs from it.",
  hangsFrom: "The holes in a guarantee's shape, or the guarantee itself when it is a hole. A guarantee hangs from those holes.",
  complete: "A guarantee with no hole in its shape, that is not a hole itself, in a candidate that builds without errors.",
};

const read = (rel) => fs.readFileSync(path.join(root, rel), "utf8");
const sha256 = (rel) => createHash("sha256").update(fs.readFileSync(path.join(root, rel))).digest("hex");
const hashed = (rel) => ({ file: rel, sha256: sha256(rel) });
const ws1 = (s) => s.replace(/\s+/g, " ").trim();

/** Line number (1-based) of character offset `i` in `text`. */
const lineAt = (text, i) => text.slice(0, i).split("\n").length;

/** Requirements of a task with their plain-language statements from committed text. */
export function requirements(task) {
  const dir = `realworld/tasks/${task}`;
  const tj = JSON.parse(read(`${dir}/task.json`));
  const specDir = `${dir}/spec/${tj.lib}`;
  const challenge = read(`${specDir}/Challenge.lean`);
  const props = new Map([...challenge.matchAll(/^theorem\s+(req_\w+)\s*:\s*(\w+)/gm)].map((m) => [m[1], m[2]]));
  const specFiles = fs.readdirSync(path.join(root, specDir)).filter((f) => f.endsWith(".lean") && f !== "Challenge.lean").sort().map((f) => `${specDir}/${f}`);
  const readme = read(`${dir}/README.md`);
  const rows = [...readme.matchAll(/^\| *(REQ-[A-Z-]+(?:, *REQ-[A-Z-]+)*) *\|(.*)\| *$/gm)];
  return {
    tj,
    specDir,
    specFiles,
    reqs: tj.requirements.map(([id, thm]) => {
      const prop = props.get(thm);
      if (!prop) throw new Error(`${task}: ${thm} not in Challenge.lean`);
      let statement = null;
      for (const f of specFiles) {
        const text = read(f);
        const m = new RegExp(String.raw`/--((?:(?!-/)[\s\S])*?)-/\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev)\s+${prop}\b`).exec(text);
        if (!m) continue;
        const doc = ws1(m[1]);
        if (!doc.startsWith(`${id}: `)) throw new Error(`${task}: doc comment of ${prop} does not start with ${id}`);
        statement = { text: doc.slice(id.length + 2), file: f, lines: [lineAt(text, m.index), lineAt(text, m.index + 3 + m[1].length)] };
        break;
      }
      if (!statement) throw new Error(`${task}: no doc comment for ${prop}`);
      const row = rows.find((r) => r[1].split(/, */).includes(id));
      const cells = row ? row[2].split(" | ") : null;
      return {
        id,
        theorem: `${tj.namespace}.${thm}`,
        property: prop,
        statement,
        readme: row ? { text: cells[cells.length - 1].trim(), file: `${dir}/README.md`, line: lineAt(readme, row.index) } : null,
      };
    }),
  };
}

/** Build the candidate of `run` and run the extractor; returns the raw graph lines and the build log. */
function extract(cfg, tj, roots) {
  const TASK = `realworld/tasks/${cfg.task}`;
  const SOURCE = `${cfg.run}/final.lean`;
  const ws = fs.mkdtempSync(path.join(os.tmpdir(), "pf-shape-"));
  fs.cpSync(path.join(root, TASK), ws, { recursive: true, filter: (src) => !src.includes(`${path.sep}.lake`) });
  fs.copyFileSync(path.join(root, SOURCE), path.join(ws, "candidate/Solution.lean"));
  fs.copyFileSync(path.join(root, EXTRACTOR), path.join(ws, "ProofGraph.lean"));
  fs.writeFileSync(path.join(ws, "roots.txt"), roots.join(" ") + "\n");
  fs.writeFileSync(path.join(ws, "spec-root.txt"), tj.lib + "\n");
  let library = null;
  const imports = [...read(SOURCE).matchAll(/^import\s+(\S+)/gm)].map((m) => m[1]);
  if (imports.some((m) => m.startsWith("ProofForgeFin"))) {
    const lib = JSON.parse(read(`${cfg.run}/summary.json`)).library;
    if (!lib?.git_commit) throw new Error(`${cfg.slug}: imports ProofForgeFin but summary.json records no library version`);
    execFileSync("python3", ["-c", [
      "import pathlib, sys",
      "sys.path.insert(0, 'harness')",
      "import fin_lib",
      `src = fin_lib.materialize(${JSON.stringify(lib.git_commit)}, ${JSON.stringify(lib.source_tree_sha256)})`,
      "assert src, 'library sources not found at that commit'",
      `fin_lib.vendor(pathlib.Path(${JSON.stringify(ws)}), [pathlib.Path(${JSON.stringify(ws)}) / 'candidate/Solution.lean'], root=src)`,
    ].join("\n")], { cwd: root, stdio: "inherit" });
    library = { package: "proofforge-fin", source_tree_sha256: lib.source_tree_sha256, git_commit: lib.git_commit, imported: imports.filter((m) => m.startsWith("ProofForgeFin")).sort() };
  }
  const steps = "lean --version > lean.version; lake build Solution > build.log 2>&1; echo $? > build.rc; lake env lean ProofGraph.lean > graph.jsonl 2> graph.err; echo $? > graph.rc";
  if (LOCAL) {
    console.log(`${cfg.slug}: building ${SOURCE} with ${LOCAL}/bin/lean (${ws})`);
    execFileSync("bash", ["-c", steps], { cwd: ws, stdio: "inherit", env: { ...process.env, PATH: `${LOCAL}/bin:${process.env.PATH}` } });
  } else {
    console.log(`${cfg.slug}: building ${SOURCE} in ${IMAGE} (${ws})`);
    execFileSync("docker", ["run", "--rm", "--network", "none", "--memory", "4g", "-v", `${ws}:/work`, "-w", "/work", IMAGE, "bash", "-lc", steps], { stdio: "inherit" });
  }
  const lean = { toolchain: read(`${TASK}/lean-toolchain`).trim(), version: fs.readFileSync(path.join(ws, "lean.version"), "utf8").trim(), runner: LOCAL ? "local release build of the toolchain (PF_LEAN_HOME)" : `Docker image ${IMAGE}` };
  if (!lean.version.includes(`version ${lean.toolchain.split(":v")[1]},`)) throw new Error(`${cfg.slug}: Lean ${lean.version} is not ${lean.toolchain}`);
  const buildLog = fs.readFileSync(path.join(ws, "build.log"), "utf8");
  const buildRc = Number(fs.readFileSync(path.join(ws, "build.rc"), "utf8").trim());
  const graphRc = Number(fs.readFileSync(path.join(ws, "graph.rc"), "utf8").trim());
  if (graphRc !== 0) throw new Error(`${cfg.slug}: extractor failed (build exit ${buildRc}):\n${buildLog.slice(-3000)}\n${fs.readFileSync(path.join(ws, "graph.err"), "utf8").slice(-2000)}\n${fs.readFileSync(path.join(ws, "graph.jsonl"), "utf8").slice(-3000)}`);
  const raw = fs.readFileSync(path.join(ws, "graph.jsonl"), "utf8").trim().split("\n").filter(Boolean).map((l) => JSON.parse(l));
  fs.rmSync(ws, { recursive: true, force: true });
  return { raw, buildLog, buildRc, library, lean };
}

/** Declarations that `id` uses, directly or through others. */
function cone(out, id) {
  const seen = new Set();
  const stack = [id];
  while (stack.length) for (const m of out.get(stack.pop()) ?? []) if (!seen.has(m)) (seen.add(m), stack.push(m));
  return seen;
}

function shapeOf(cfg) {
  const TASK = `realworld/tasks/${cfg.task}`;
  const SOURCE = `${cfg.run}/final.lean`;
  const { tj, specFiles, reqs } = requirements(cfg.task);
  const { raw: lines, buildLog, buildRc, library, lean } = extract(cfg, tj, reqs.map((r) => r.theorem));
  const missing = lines.filter((d) => d.missing).map((d) => d.name);
  const raw = lines.filter((d) => !d.missing);
  const ns = `${tj.namespace}.`;
  const short = (n) => (n.startsWith(ns) ? n.slice(ns.length) : n);
  const reqOf = new Map(reqs.map((r) => [r.theorem, r.id]));
  const kindOf = (d) => (reqOf.has(d.name) ? "requirement" : d.kind === "theorem" ? "lemma" : d.kind === "structure" || d.kind === "inductive" ? "type" : "definition");
  const byName = new Map(raw.map((d) => [d.name, d]));
  const depth = new Map();
  const depthOf = (n) => {
    if (depth.has(n)) return depth.get(n);
    depth.set(n, -1);
    const ds = byName.get(n).deps;
    const v = ds.length ? 1 + Math.max(...ds.map(depthOf)) : 0;
    depth.set(n, v);
    return v;
  };
  raw.forEach((d) => depthOf(d.name));
  const order = { type: 0, definition: 1, lemma: 2, requirement: 3 };
  const nodes = raw
    .map((d) => ({
      id: short(d.name),
      kind: kindOf(d),
      origin: d.module === "Solution" ? "candidate" : "specification",
      file: d.module === "Solution" ? SOURCE : `${TASK}/spec/${d.module.replaceAll(".", "/")}.lean`,
      lines: d.lines,
      depth: depth.get(d.name),
      ...(reqOf.has(d.name) ? { requirement: reqOf.get(d.name) } : {}),
      hole: d.hole,
      ...(d.lib.length ? { library: d.lib } : {}),
    }))
    .sort((a, b) => a.depth - b.depth || order[a.kind] - order[b.kind] || a.id.localeCompare(b.id));
  const edges = raw.flatMap((d) => d.deps.map((t) => [short(d.name), short(t)])).sort((a, b) => a[0].localeCompare(b[0]) || a[1].localeCompare(b[1]));
  const out = new Map();
  for (const [a, b] of edges) out.set(a, [...(out.get(a) ?? []), b]);
  const node = new Map(nodes.map((n) => [n.id, n]));

  const source = read(SOURCE);
  const declared = [...source.matchAll(/^(?:theorem|lemma|def|abbrev)\s+([^\s:({]+)/gm)].map((m) => m[1]);
  const reached = new Set(nodes.map((n) => n.id));
  const excluded = declared.filter((n) => !reached.has(n));
  // Lean's own warnings for `sorry`, by line of the candidate.
  const sorryLines = [...new Set([...buildLog.matchAll(/Solution\.lean:(\d+):\d+: declaration uses .sorry./g)].map((m) => Number(m[1])))].sort((a, b) => a - b);
  const errorLines = [...new Set([...buildLog.matchAll(/error: [^\n]*Solution\.lean:(\d+):\d+:/g)].map((m) => Number(m[1])))].sort((a, b) => a - b);
  const inNode = (l) => nodes.some((n) => n.origin === "candidate" && n.lines && n.lines[0] <= l && l <= n.lines[1]);

  const holeIds = new Set(nodes.filter((n) => n.hole).map((n) => n.id));
  const guarantees = reqs.map((r) => {
    const id = short(r.theorem);
    if (!node.has(id)) return { ...r, id: r.id, node: id, missing: true, complete: false };
    const s = cone(out, id);
    const d = node.get(id).depth;
    const width = Array.from({ length: d }, (_, k) => [...s].filter((x) => node.get(x).depth === k).length);
    const count = (k) => [...s].filter((x) => node.get(x).kind === k).length;
    const hangsFrom = [...(holeIds.has(id) ? [id] : []), ...[...s].filter((x) => holeIds.has(x)).sort()];
    return {
      ...r,
      node: id,
      size: s.size,
      depth: d,
      width,
      composition: {
        requirements: count("requirement"),
        lemmas: count("lemma"),
        definitions: count("definition"),
        types: count("type"),
        candidate: [...s].filter((x) => node.get(x).origin === "candidate").length,
        specification: [...s].filter((x) => node.get(x).origin === "specification").length,
      },
      hangsFrom,
      proved: [...s].filter((x) => !holeIds.has(x)).length,
      complete: hangsFrom.length === 0 && buildRc === 0,
    };
  });
  const present = guarantees.filter((g) => !g.missing);
  const shapes = new Map(present.map((g) => [g.node, cone(out, g.node)]));
  const every = nodes.filter((n) => present.every((g) => shapes.get(g.node).has(n.id))).map((n) => ({ id: n.id, kind: n.kind, origin: n.origin, depth: n.depth }));
  const lemmas = nodes
    .filter((n) => n.kind === "lemma")
    .map((n) => ({ id: n.id, origin: n.origin, depth: n.depth, guarantees: present.filter((g) => shapes.get(g.node).has(n.id)).length }))
    .filter((l) => l.guarantees > 0)
    .sort((a, b) => b.guarantees - a.guarantees || b.depth - a.depth || a.id.localeCompare(b.id));
  const holes = nodes
    .filter((n) => n.hole)
    .map((n) => ({ id: n.id, kind: n.kind, hole: n.hole, origin: n.origin, file: n.file, lines: n.lines, depth: n.depth, guarantees: present.filter((g) => g.hangsFrom.includes(n.id)).map((g) => g.id) }));

  const summary = readRunSummary(`${cfg.run}/summary.json`);
  const hasPassport = fs.existsSync(path.join(root, cfg.run, "passport.json"));
  const passport = hasPassport ? readPassport(`${cfg.run}/passport.json`) : null;
  if (cfg.role === "verified" && passport?.status !== "VERIFIED") throw new Error(`${cfg.slug}: Passport is not VERIFIED`);
  const finalStatus = JSON.parse(read(`${cfg.run}/summary.json`)).final_status ?? null;
  return {
    title: cfg.role === "verified" ? `Shapes of the guarantees of the verified ${cfg.name} repair` : `Holes of the ${cfg.name} run ${path.basename(cfg.run)}`,
    slug: cfg.slug,
    role: cfg.role,
    definitions: DEFINITIONS,
    rule: "Nodes are the declarations reached from the requirement theorems by following the constants each declaration's type and value use, as the Lean kernel sees them, restricted to the candidate (final.lean) and the locked specification. Compiler-generated declarations are walked through, so their uses count for the declaration that generated them; constructors, recursors and projections count as their type; Lean's core library and ProofForgeFin are not shown (the ProofForgeFin declarations a node mentions are listed under its `library`). A declaration of the candidate that no requirement uses is left out and listed under excluded. An edge [a, b] means a uses b.",
    extractor: EXTRACTOR,
    script: SCRIPT,
    task: { id: cfg.task, name: cfg.name, namespace: tj.namespace, taskJson: hashed(`${TASK}/task.json`), readme: hashed(`${TASK}/README.md`), challenge: hashed(`${TASK}/spec/${tj.lib}/Challenge.lean`), specification: specFiles.map(hashed) },
    run: { dir: cfg.run, arm: summary.arm, model: summary.model, planner: summary.planner ?? null, summary: hashed(`${cfg.run}/summary.json`), finalStatus },
    source: hashed(SOURCE),
    library,
    passport: passport && { file: passport.path, sha256: passport.sha256, status: passport.status, requirements: passport.requirements, kernels: passport.kernels },
    lean,
    build: { ok: buildRc === 0, sorryWarningLines: sorryLines, errorLines, sorryOutsideShapes: sorryLines.filter((l) => !inNode(l)).map((l) => ({ line: l, declaration: /(?:theorem|lemma|def|abbrev|instance)\s+([^\s:({]+)/.exec(source.split("\n")[l - 1])?.[1] ?? null })) },
    counts: {
      guarantees: guarantees.length,
      complete: guarantees.filter((g) => g.complete).length,
      nodes: nodes.length,
      edges: edges.length,
      holes: holes.length,
      lemmas: nodes.filter((n) => n.kind === "lemma").length,
      definitions: nodes.filter((n) => n.kind === "definition").length,
      types: nodes.filter((n) => n.kind === "type").length,
      excluded: excluded.length,
    },
    guarantees,
    loadBearing: { every, lemmas },
    holes,
    missing,
    nodes,
    edges,
    excluded,
  };
}

/** Headline measurements of all shape files. */
function summarize() {
  const files = RUNS.map((r) => `web/generated/shapes/${r.slug}.json`).filter((f) => fs.existsSync(path.join(root, f)));
  const data = files.map((f) => ({ file: f, d: JSON.parse(read(f)) }));
  const verified = data.filter((x) => x.d.role === "verified").map(({ file, d }) => {
    const gs = d.guarantees;
    const maxDepth = Math.max(...gs.map((g) => g.depth));
    const maxSize = Math.max(...gs.map((g) => g.size));
    const top = d.loadBearing.lemmas.length ? d.loadBearing.lemmas[0].guarantees : 0;
    return {
      task: d.task.id,
      name: d.task.name,
      file,
      run: d.run.dir,
      passport: d.passport.sha256,
      guarantees: gs.length,
      nodes: d.counts.nodes,
      deepest: gs.filter((g) => g.depth === maxDepth).map((g) => ({ id: g.id, depth: g.depth, size: g.size })),
      largest: gs.filter((g) => g.size === maxSize).map((g) => ({ id: g.id, depth: g.depth, size: g.size })),
      smallest: (() => { const m = Math.min(...gs.map((g) => g.size)); return gs.filter((g) => g.size === m).map((g) => ({ id: g.id, depth: g.depth, size: g.size })); })(),
      lemmasInEveryShape: d.loadBearing.every.filter((n) => n.kind === "lemma").map((n) => n.id),
      declarationsInEveryShape: d.loadBearing.every.length,
      mostSharedLemmas: d.loadBearing.lemmas.filter((l) => l.guarantees === top).map((l) => ({ id: l.id, guarantees: l.guarantees, depth: l.depth })),
    };
  });
  const attempts = data.filter((x) => x.d.role === "attempt").map(({ file, d }) => ({
    task: d.task.id,
    name: d.task.name,
    run: d.run.dir,
    file,
    holes: d.holes.map((h) => ({ id: h.id, kind: h.kind, guarantees: h.guarantees.length })),
    holesOutsideShapes: d.build.sorryOutsideShapes.map((h) => h.declaration),
    complete: d.guarantees.filter((g) => g.complete).map((g) => g.id),
    open: d.guarantees.filter((g) => !g.complete).map((g) => ({ id: g.id, hangsFrom: g.hangsFrom, size: g.size, proved: g.proved })),
  }));
  const comp = attempts.filter((a) => a.task === "rw-compound-comp");
  const inAll = (lists) => lists.reduce((acc, l) => acc.filter((x) => l.includes(x)));
  const compound = comp.length && {
    runs: comp.map((a) => a.run),
    holesInEveryRun: inAll(comp.map((a) => a.holes.map((h) => h.id))),
    guaranteesOpenInEveryRun: inAll(comp.map((a) => a.open.map((g) => g.id))),
    guaranteesCompleteInSomeRun: [...new Set(comp.flatMap((a) => a.complete))].sort(),
  };
  const out = {
    title: "The shape of a guarantee: headline measurements",
    definitions: DEFINITIONS,
    script: SCRIPT,
    files: files.map((f) => ({ file: f, sha256: sha256(f) })),
    noPassportBackedRepair: [
      { task: "rw-compound-comp", name: "Compound", note: "No Muse run verifies (results/compound-1, results/library-1, results/baseline-flagships-1, results/frontier-1); results/library-live-1 is VERIFIED but written by the build team, not by a model." },
      { task: "payout-flagship", name: "payout flagship", note: "Muse runs were scored by the E1 evaluator (results/e1-dev-1, results/e1-dev-2, results/frontier-1) and no run has a Passport; the only payout-flagship Passport is the REFUTED start candidate in results/counterexamples-1." },
    ],
    verified,
    attempts,
    compound,
  };
  fs.writeFileSync(path.join(OUT, "summary.json"), JSON.stringify(out, null, 1) + "\n");
  console.log(`wrote summary of ${files.length} files`);
}

if (process.argv[1] && path.resolve(process.argv[1]) === new URL(import.meta.url).pathname) {
  fs.mkdirSync(OUT, { recursive: true });
  const args = process.argv.slice(2);
  if (!args.includes("--summary")) {
    const pick = args.length ? RUNS.filter((r) => args.includes(r.slug)) : RUNS;
    for (const cfg of pick) {
      const s = shapeOf(cfg);
      fs.writeFileSync(path.join(OUT, `${cfg.slug}.json`), JSON.stringify(s, null, 1) + "\n");
      console.log(`${cfg.slug}: ${s.counts.nodes} nodes, ${s.counts.holes} holes, ${s.counts.complete} of ${s.counts.guarantees} complete`);
    }
  }
  summarize();
}
