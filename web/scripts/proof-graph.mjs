// Extracts the dependency graph of the verified Balancer repair for the home page hero and writes
// generated/proof-graph.json. Run once; tests/proof-graph.test.ts checks the output against the
// source, the locked specification and the Passport.
//
// It stages the task (realworld/tasks/rw-balancer-upscale) with the repair as candidate/Solution.lean,
// builds it in the pinned Lean image and runs scripts/proof-graph/ProofGraph.lean, which walks the
// constants each declaration uses, as the kernel sees them, from the eight requirement theorems.
// Usage: node scripts/proof-graph.mjs   (needs Docker and the proofforge-lean:4.35.0 image)

import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";

const here = path.dirname(new URL(import.meta.url).pathname);
const root = path.resolve(here, "../..");
const IMAGE = "proofforge-lean:4.35.0";
const TASK = "realworld/tasks/rw-balancer-upscale";
const RUN = "results/balancer-1/repair-A2-1";
const SOURCE = `${RUN}/final.lean`;
const PASSPORT = `${RUN}/passport.json`;
const SPEC = `${TASK}/spec/BalancerSwap/Spec.lean`;
const EXTRACTOR = "web/scripts/proof-graph/ProofGraph.lean";

const sha256 = (file) => createHash("sha256").update(fs.readFileSync(path.join(root, file))).digest("hex");
const passport = JSON.parse(fs.readFileSync(path.join(root, PASSPORT), "utf8"));
const roots = passport.requirements.map((r) => r.theorem);

const ws = fs.mkdtempSync(path.join(os.tmpdir(), "pf-graph-"));
fs.cpSync(path.join(root, TASK), ws, { recursive: true, filter: (src) => !src.includes(`${path.sep}.lake`) });
fs.copyFileSync(path.join(root, SOURCE), path.join(ws, "candidate/Solution.lean"));
fs.copyFileSync(path.join(root, EXTRACTOR), path.join(ws, "ProofGraph.lean"));
fs.writeFileSync(path.join(ws, "roots.txt"), roots.join(" ") + "\n");

console.log(`building ${SOURCE} in ${IMAGE} (${ws})`);
execFileSync(
  "docker",
  ["run", "--rm", "--network", "none", "--memory", "4g", "-v", `${ws}:/work`, "-w", "/work", IMAGE, "bash", "-lc",
    "lake build Solution >/tmp/build.log 2>&1 || { tail -c 3000 /tmp/build.log; exit 3; }; lake env lean ProofGraph.lean > graph.jsonl"],
  { stdio: "inherit" },
);
const raw = fs.readFileSync(path.join(ws, "graph.jsonl"), "utf8").trim().split("\n").map((l) => JSON.parse(l));
fs.rmSync(ws, { recursive: true, force: true });

const short = (n) => n.replace(/^BalancerSwap\./, "");
const requirementOf = new Map(passport.requirements.map((r) => [r.theorem, r.id]));
const kindOf = (d) => {
  if (requirementOf.has(d.name)) return "requirement";
  if (d.kind === "theorem") return "lemma";
  if (d.kind === "structure" || d.kind === "inductive") return "type";
  return "definition";
};
const byName = new Map(raw.map((d) => [d.name, d]));

// Depth: 0 for a declaration that uses no other node, else one more than its deepest dependency.
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
    ...(requirementOf.has(d.name) ? { requirement: requirementOf.get(d.name) } : {}),
  }))
  .sort((a, b) => a.depth - b.depth || order[a.kind] - order[b.kind] || a.id.localeCompare(b.id));
const edges = raw.flatMap((d) => d.deps.map((t) => [short(d.name), short(t)])).sort((a, b) => a[0].localeCompare(b[0]) || a[1].localeCompare(b[1]));

// Declarations of the repair that no requirement reaches.
const declared = [...fs.readFileSync(path.join(root, SOURCE), "utf8").matchAll(/^(?:theorem|lemma|def|abbrev)\s+([^\s:({]+)/gm)].map((m) => m[1]);
const reached = new Set(nodes.map((n) => n.id));
const excluded = declared.filter((n) => !reached.has(n));

const axioms = [...new Set(passport.requirements.flatMap((r) => r.axioms_used))].sort();
const out = {
  title: "Dependency graph of the verified Balancer V2 repair",
  rule:
    "Nodes are the declarations reached from the eight requirement theorems by following the constants each declaration's type and value use, as the Lean kernel sees them, restricted to the repair (final.lean) and the locked specification. Compiler-generated declarations are walked through, so their uses count for the declaration that generated them; constructors, recursors and projections count as their type; Lean's core library is not shown. A declaration of the repair that no requirement uses is left out and listed under excluded. An edge [a, b] means a uses b.",
  extractor: EXTRACTOR,
  script: "web/scripts/proof-graph.mjs",
  source: { file: SOURCE, sha256: sha256(SOURCE) },
  specification: { file: SPEC, sha256: sha256(SPEC) },
  passport: {
    file: PASSPORT,
    sha256: passport.passport_sha256,
    status: passport.status,
    requirements: passport.requirements.length,
    verified: passport.requirements.filter((r) => r.status === "VERIFIED").length,
    kernels: passport.checks.comparator_kernels,
    propertyCases: passport.checks.property_tests.cases,
    axioms,
    lean: passport.toolchain.lean,
  },
  counts: {
    nodes: nodes.length,
    edges: edges.length,
    requirements: nodes.filter((n) => n.kind === "requirement").length,
    lemmas: nodes.filter((n) => n.kind === "lemma").length,
    definitions: nodes.filter((n) => n.kind === "definition").length,
    types: nodes.filter((n) => n.kind === "type").length,
    excluded: excluded.length,
  },
  nodes,
  edges,
  excluded,
};
const dest = path.join(here, "../generated/proof-graph.json");
fs.writeFileSync(dest, JSON.stringify(out, null, 1) + "\n");
console.log(`${nodes.length} nodes, ${edges.length} edges, ${excluded.length} declarations excluded; wrote ${path.relative(process.cwd(), dest)}`);
