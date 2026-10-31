// The dependency graph of the verified Balancer V2 repair (generated/proof-graph.json, written by
// scripts/proof-graph.mjs and checked by tests/proof-graph.test.ts), and its layout for the home
// page hero: the eight requirements on an inner ring around the conclusion, every other declaration
// on a ring set by its depth (definitions outside, the lemmas that combine them further in), and
// the order in which a check reaches them (a declaration once everything it uses is checked).

import data from "@/generated/proof-graph.json";

export type NodeKind = "requirement" | "lemma" | "definition" | "type";

export interface GraphNode {
  id: string;
  kind: NodeKind;
  origin: "candidate" | "specification";
  file: string;
  lines: [number, number] | null;
  depth: number;
  requirement?: string;
}

export interface ProofGraphData {
  title: string;
  rule: string;
  extractor: string;
  script: string;
  source: { file: string; sha256: string };
  specification: { file: string; sha256: string };
  passport: {
    file: string;
    sha256: string;
    status: string;
    requirements: number;
    verified: number;
    kernels: string[];
    propertyCases: number;
    axioms: string[];
    lean: string;
  };
  counts: Record<"nodes" | "edges" | "requirements" | "lemmas" | "definitions" | "types" | "excluded", number>;
  nodes: GraphNode[];
  edges: [string, string][];
  excluded: string[];
}

export const PROOF_GRAPH = data as unknown as ProofGraphData;

export interface PlacedNode extends GraphNode {
  x: number;
  y: number;
  /** Seconds after the start of the check at which the node lights. */
  at: number;
}

export interface GraphLayout {
  size: number;
  center: number;
  rings: number[];
  orbit: number;
  nodes: PlacedNode[];
  /** Edges of the transitive reduction: [user, used]. The full edge list is in the data. */
  edges: { from: string; to: string; at: number }[];
  kernels: { name: string; x: number; y: number; angle: number; at: number }[];
  /** Seconds at which the last requirement lights. */
  done: number;
}

const TAU = Math.PI * 2;
const wrap = (a: number) => ((a % TAU) + TAU) % TAU;

/** Circular mean of angles; `fallback` when they cancel out. */
function meanAngle(as: number[], fallback: number) {
  if (!as.length) return fallback;
  let x = 0;
  let y = 0;
  for (const a of as) {
    x += Math.cos(a);
    y += Math.sin(a);
  }
  return Math.hypot(x, y) < 1e-9 ? fallback : wrap(Math.atan2(y, x));
}

/** Edges [a, b] of `edges` not implied by a longer path from a to b. */
export function transitiveReduction(edges: [string, string][]): [string, string][] {
  const out = new Map<string, Set<string>>();
  for (const [a, b] of edges) {
    if (!out.has(a)) out.set(a, new Set());
    out.get(a)!.add(b);
  }
  const memo = new Map<string, Set<string>>();
  const reach = (n: string): Set<string> => {
    const hit = memo.get(n);
    if (hit) return hit;
    const s = new Set<string>();
    memo.set(n, s);
    for (const m of out.get(n) ?? []) {
      s.add(m);
      for (const k of reach(m)) s.add(k);
    }
    return s;
  };
  return edges.filter(([a, b]) => ![...(out.get(a) ?? [])].some((c) => c !== b && reach(c).has(b)));
}

/** Declarations that `id` uses, directly or through others. */
export function dependencyCone(edges: [string, string][], id: string): Set<string> {
  const out = new Map<string, string[]>();
  for (const [a, b] of edges) out.set(a, [...(out.get(a) ?? []), b]);
  const seen = new Set<string>();
  const stack = [id];
  while (stack.length) {
    const n = stack.pop()!;
    for (const m of out.get(n) ?? []) {
      if (!seen.has(m)) {
        seen.add(m);
        stack.push(m);
      }
    }
  }
  return seen;
}

/** Deterministic layout of the graph in a square of side `size`. */
export function layoutGraph(g: ProofGraphData = PROOF_GRAPH, size = 640): GraphLayout {
  const c = size / 2;
  const orbit = size * 0.455;
  const outer = size * 0.39;
  const inner = size * 0.15;
  const reqRing = size * 0.085;

  const reqs = g.nodes.filter((n) => n.kind === "requirement");
  const rest = g.nodes.filter((n) => n.kind !== "requirement");
  const maxDepth = Math.max(...rest.map((n) => n.depth));
  // Ring radius by depth, depth 0 outermost. Outer rings hold more declarations, so they are spaced wider.
  const ringOf = (d: number) => inner + (outer - inner) * Math.pow(1 - d / maxDepth, 0.8);
  const rings = [...new Set(rest.map((n) => n.depth))].sort((a, b) => a - b).map(ringOf);

  const users = new Map<string, string[]>();
  for (const [a, b] of g.edges) users.set(b, [...(users.get(b) ?? []), a]);

  const angle = new Map<string, number>();
  // Requirements evenly around the conclusion, in source order (the order of the Passport), from the top.
  reqs
    .slice()
    .sort((a, b) => (a.lines?.[0] ?? 0) - (b.lines?.[0] ?? 0))
    .forEach((n, i) => angle.set(n.id, wrap(-Math.PI / 2 + (i * TAU) / reqs.length)));

  // Every other declaration: at the circular mean of the declarations that use it, innermost rings first.
  const byDepth = new Map<number, GraphNode[]>();
  for (const n of rest) byDepth.set(n.depth, [...(byDepth.get(n.depth) ?? []), n]);
  for (const d of [...byDepth.keys()].sort((a, b) => b - a)) {
    const ring = byDepth.get(d)!;
    const r = ringOf(d);
    const wanted = ring
      .map((n, i) => ({ n, a: meanAngle((users.get(n.id) ?? []).map((u) => angle.get(u)).filter((x): x is number => x !== undefined), (i * TAU) / ring.length) }))
      .sort((p, q) => p.a - q.a || p.n.id.localeCompare(q.n.id));
    // Evenly around the ring in that order, turned to sit closest to where the users pull each declaration.
    const slot = TAU / ring.length;
    const base = meanAngle(wanted.map((w, i) => w.a - i * slot), 0);
    const as = wanted.map((_, i) => wrap(base + i * slot));
    wanted.forEach((w, i) => angle.set(w.n.id, as[i]!));
  }

  // The check reaches a declaration once everything it uses is checked: by depth, then around the ring.
  const step = 0.28;
  const at = (n: GraphNode) => 0.3 + n.depth * step + (angle.get(n.id)! / TAU) * step * 0.85;
  const placed: PlacedNode[] = g.nodes.map((n) => {
    const r = n.kind === "requirement" ? reqRing : ringOf(n.depth);
    const a = angle.get(n.id)!;
    return { ...n, x: round(c + r * Math.cos(a)), y: round(c + r * Math.sin(a)), at: round(at(n)) };
  });
  const atOf = new Map(placed.map((n) => [n.id, n.at]));
  const done = Math.max(...placed.filter((n) => n.kind === "requirement").map((n) => n.at));
  const edges = transitiveReduction(g.edges).map(([from, to]) => ({ from, to, at: atOf.get(from)! }));
  const kernels = g.passport.kernels.map((name, i) => {
    const a = -Math.PI / 2 + (i * TAU) / g.passport.kernels.length + TAU / 12;
    return { name, angle: round((a * 180) / Math.PI), x: round(c + orbit * Math.cos(a)), y: round(c + orbit * Math.sin(a)), at: round(done + 0.7 + i * 0.17) };
  });
  return { size, center: c, rings: rings.map(round), orbit: round(orbit), nodes: placed, edges, kernels, done: round(done) };
}

const round = (x: number) => Math.round(x * 100) / 100;
