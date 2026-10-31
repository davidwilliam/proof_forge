import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { PROOF_GRAPH as g, layoutGraph, transitiveReduction } from "../lib/proofgraph";
import { ROOT } from "../scripts/lib/results.mjs";

// generated/proof-graph.json is written once by scripts/proof-graph.mjs, which runs the Lean kernel's
// record of used constants in the pinned image. These checks need no Lean: they tie the committed graph
// to the committed source, the locked specification and the Passport.

const read = (rel: string) => readFileSync(path.join(ROOT, rel));
const sha = (rel: string) => createHash("sha256").update(read(rel)).digest("hex");
const passport = JSON.parse(read(g.passport.file).toString("utf8"));
const source = read(g.source.file).toString("utf8");
const lines = (file: string) => read(file).toString("utf8").split("\n");

/** The text of a node's declaration in its file. */
const declText = (n: (typeof g.nodes)[number]) => lines(n.file).slice(n.lines![0] - 1, n.lines![1]).join("\n");
const word = (id: string) => new RegExp(`(^|[^A-Za-z0-9_.'])${id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}($|[^A-Za-z0-9_'])`);

describe("proof graph of the verified Balancer repair", () => {
  it("is the graph of the file and the Passport it names", () => {
    expect(g.source.sha256).toBe(sha(g.source.file));
    expect(passport.solution.files["final.lean"]).toBe(g.source.sha256);
    expect(g.specification.sha256).toBe(sha(g.specification.file));
    expect(g.passport.sha256).toBe(passport.passport_sha256);
    expect(g.passport.sha256.startsWith("48930efd")).toBe(true);
  });

  it("carries the Passport readings shown in the hero", () => {
    expect(g.passport.status).toBe(passport.status);
    expect(g.passport.status).toBe("VERIFIED");
    expect(g.passport.requirements).toBe(passport.requirements.length);
    expect(g.passport.verified).toBe(passport.requirements.filter((r: { status: string }) => r.status === "VERIFIED").length);
    expect(g.passport.verified).toBe(8);
    expect(g.passport.kernels).toEqual(passport.checks.comparator_kernels);
    expect(g.passport.kernels).toHaveLength(6);
    expect(g.passport.propertyCases).toBe(passport.checks.property_tests.cases);
    expect(g.passport.propertyCases).toBe(2001);
    expect(g.passport.axioms).toEqual([...new Set(passport.requirements.flatMap((r: { axioms_used: string[] }) => r.axioms_used))].sort());
    for (const a of g.passport.axioms) expect(passport.permitted_axioms).toContain(a);
  });

  it("has the eight requirement theorems of the Passport as its requirements", () => {
    const reqs = g.nodes.filter((n) => n.kind === "requirement");
    expect(reqs.map((n) => `BalancerSwap.${n.id}`).sort()).toEqual(passport.requirements.map((r: { theorem: string }) => r.theorem).sort());
    for (const n of reqs) expect(passport.requirements.find((r: { id: string }) => r.id === n.requirement).theorem).toBe(`BalancerSwap.${n.id}`);
  });

  it("places every node at its declaration in the repair or the locked specification", () => {
    for (const n of g.nodes) {
      expect(n.lines, n.id).not.toBeNull();
      if (n.origin === "candidate") expect(n.file).toBe(g.source.file);
      else expect(n.file.startsWith("realworld/tasks/rw-balancer-upscale/spec/BalancerSwap/")).toBe(true);
      const short = n.id.split(".").pop()!;
      const kw = n.kind === "requirement" || n.kind === "lemma" ? "theorem" : n.kind === "type" ? "(structure|inductive)" : "(def|abbrev|instance)";
      const text = declText(n);
      if (n.id.startsWith("inst")) expect(text, n.id).toMatch(/instance/);
      else expect(text, n.id).toMatch(new RegExp(`${kw}\\s+${short}\\b`));
    }
  });

  it("has edges between nodes only, no cycles, and every node reachable from a requirement", () => {
    const ids = new Set(g.nodes.map((n) => n.id));
    expect(ids.size).toBe(g.nodes.length);
    for (const [a, b] of g.edges) {
      expect(ids.has(a), a).toBe(true);
      expect(ids.has(b), b).toBe(true);
      expect(a).not.toBe(b);
    }
    const out = new Map<string, string[]>();
    for (const [a, b] of g.edges) out.set(a, [...(out.get(a) ?? []), b]);
    const depth = new Map(g.nodes.map((n) => [n.id, n.depth]));
    // Depth strictly decreases along every edge, so the graph is acyclic.
    for (const [a, b] of g.edges) expect(depth.get(a)!).toBeGreaterThan(depth.get(b)!);
    const seen = new Set<string>();
    const stack = g.nodes.filter((n) => n.kind === "requirement").map((n) => n.id);
    while (stack.length) {
      const n = stack.pop()!;
      if (seen.has(n)) continue;
      seen.add(n);
      stack.push(...(out.get(n) ?? []));
    }
    expect(seen.size).toBe(g.nodes.length);
  });

  it("records a use of every lemma of the repair that its user names in the source", () => {
    // Uses of the repair's own lemmas are explicit in proof text (no simp sets or instances), so the
    // user's declaration names each one it uses.
    const lemma = new Set(g.nodes.filter((n) => n.origin === "candidate" && n.kind === "lemma").map((n) => n.id));
    for (const [a, b] of g.edges) {
      if (!lemma.has(b)) continue;
      const user = g.nodes.find((n) => n.id === a)!;
      expect(declText(user), `${a} uses ${b}`).toMatch(word(b));
    }
    // And the converse: a candidate declaration that names a lemma of the repair uses it.
    for (const n of g.nodes.filter((x) => x.origin === "candidate")) {
      const text = declText(n).split("\n").slice(1).join("\n");
      for (const l of lemma) if (l !== n.id && word(l).test(text)) expect(g.edges.some(([a, b]) => a === n.id && b === l), `${n.id} names ${l}`).toBe(true);
    }
  });

  it("leaves out exactly the declarations of the repair that no requirement uses", () => {
    const declared = [...source.matchAll(/^(?:theorem|lemma|def|abbrev)\s+([^\s:({]+)/gm)].map((m) => m[1]!);
    const nodes = new Set(g.nodes.map((n) => n.id));
    expect([...declared].sort()).toEqual([...g.nodes.filter((n) => n.origin === "candidate").map((n) => n.id), ...g.excluded].sort());
    for (const x of g.excluded) {
      expect(nodes.has(x)).toBe(false);
      // No declaration in the graph mentions an excluded one.
      for (const n of g.nodes.filter((m) => m.origin === "candidate")) expect(declText(n), `${n.id} mentions ${x}`).not.toMatch(word(x));
    }
    expect(g.rule).toMatch(/no requirement uses is left out/);
    expect(g.counts).toEqual({
      nodes: g.nodes.length,
      edges: g.edges.length,
      requirements: 8,
      lemmas: g.nodes.filter((n) => n.kind === "lemma").length,
      definitions: g.nodes.filter((n) => n.kind === "definition").length,
      types: g.nodes.filter((n) => n.kind === "type").length,
      excluded: g.excluded.length,
    });
  });

  it("lays out every node inside the frame with the kernels on the orbit", () => {
    const l = layoutGraph();
    expect(l.nodes).toHaveLength(g.nodes.length);
    for (const n of l.nodes) {
      const r = Math.hypot(n.x - l.center, n.y - l.center);
      expect(r).toBeLessThan(l.orbit);
      expect(n.at).toBeGreaterThanOrEqual(0);
    }
    // A declaration lights after everything it uses.
    const at = new Map(l.nodes.map((n) => [n.id, n.at]));
    for (const [a, b] of g.edges) expect(at.get(a)!).toBeGreaterThan(at.get(b)!);
    expect(l.kernels.map((k) => k.name)).toEqual(g.passport.kernels);
    for (const k of l.kernels) expect(Math.hypot(k.x - l.center, k.y - l.center)).toBeCloseTo(l.orbit, 0);
    expect(l.edges.length).toBe(transitiveReduction(g.edges).length);
    expect(l.edges.length).toBeLessThan(g.edges.length);
  });
});
