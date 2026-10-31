// The three lenses of the home page hero, all drawn from the same 106 declarations of the verified
// Balancer V2 repair (generated/proof-graph.json):
//   1. "The whole proof": the radial layout of lib/proofgraph.ts.
//   2. "The layers": the eight requirements in a row on top, the lemmas in the middle, the
//      definitions and types at the bottom, the six kernels on a tilted orbit.
//   3. "One guarantee": the dependency cone of one requirement theorem stacked as a bell, one ring
//      per level of dependency depth, the ring's width set by the number of declarations on it.
// Every figure the hero shows (cone sizes, levels, level widths) is computed here from the graph;
// tests/lenses.test.ts recomputes them independently and checks the quoted requirement statements
// against the task README.

import { PROOF_GRAPH, dependencyCone, layoutGraph, type GraphNode, type ProofGraphData } from "@/lib/proofgraph";

/** The task whose repair the graph shows. */
export const GRAPH_TASK = { dir: "realworld/tasks/rw-balancer-upscale", name: "Balancer V2" } as const;

/**
 * Each requirement's statement as the task README's requirement table writes it (column
 * "Statement" of realworld/tasks/rw-balancer-upscale/README.md), verbatim. The test compares every
 * entry with the table. A statement that begins with "and" continues the row above it.
 */
export const README_STATEMENTS: Record<string, string> = {
  "REQ-GIVEN-IN-SUCCEEDS":
    "for well-behaved math, a given-in swap between two tokens of the pool goes through when the token out has a positive scaling factor and the fee is below 100%",
  "REQ-GIVEN-OUT-SUCCEEDS":
    "for well-behaved math, a given-out swap goes through when the exact amount out rounded up is below the pool's scaled balance of that token, the token in has a positive scaling factor and the fee is below 100%",
  "REQ-GIVEN-IN-PAYS-AT-MOST": "for monotone prices, the trader receives at most what the math prices the exact amount in, net of the fee, rounded down",
  "REQ-GIVEN-IN-PAYS-AT-LEAST": "and at least what the math prices one raw unit less, less one raw unit out",
  "REQ-GIVEN-OUT-CHARGES-AT-LEAST":
    "for monotone prices, the charge, after the fee, is at least what the math prices the exact amount out rounded up to a whole 18-decimal unit",
  "REQ-GIVEN-OUT-CHARGES-AT-MOST":
    "and one raw unit less than the charge is below that price plus one raw unit: at most one unit for the conversion back and one for the fee",
  "REQ-SWAP-KEEPS-VALUE": "for well-behaved math, a swap that goes through never lowers the pool's value",
  "REQ-BATCH-KEEPS-VALUE":
    "for well-behaved math, any pool and any batch of swaps of either kind, a batch that goes through never lowers the pool's value",
};

/**
 * A quoted statement for display: its first letter capitalized, the rest verbatim. A statement that
 * continues the row above it ("and at least ...") keeps its lower case after an ellipsis.
 */
export const displayQuote = (s: string) => (s.startsWith("and ") ? `\u2026${s}` : s.charAt(0).toUpperCase() + s.slice(1));

/**
 * A short plain name from a locked requirement ID: its words in lower case without "REQ", and
 * without "given in" or "given out" before a verb that already says which kind of swap it is
 * (only a given-in swap pays out, only a given-out swap is charged).
 */
export function shortName(id: string): string {
  const w = id.replace(/^REQ-/, "").toLowerCase().split("-");
  if (w[0] === "given" && (w[2] === "pays" || w[2] === "charges")) w.splice(0, 2);
  return w.join(" ");
}

/** The short name in lines for narrow labels: "given in", "given out", "at most" and "at least" stay together. */
export function shortLines(id: string): string[] {
  const w = shortName(id).split(" ");
  const out: string[] = [];
  for (let i = 0; i < w.length; i++) {
    if ((w[i] === "given" || w[i] === "at") && i + 1 < w.length) out.push(`${w[i]} ${w[++i]}`);
    else out.push(w[i]!);
  }
  return out;
}

export interface Guarantee {
  /** Locked requirement ID, e.g. REQ-BATCH-KEEPS-VALUE. */
  id: string;
  /** The requirement theorem's node in the graph. */
  node: string;
  short: string;
  lines: string[];
  statement: string;
  /** Declarations the theorem uses, directly or through others (the theorem itself not counted). */
  size: number;
  /** Levels of the bell: the theorem's own depth plus one (the theorem is the top level). */
  levels: number;
  /** Declarations on each level from the top; the first is the theorem itself. */
  widths: number[];
}

const byLine = (a: GraphNode, b: GraphNode) => (a.lines?.[0] ?? 0) - (b.lines?.[0] ?? 0);

/** The requirement theorems in source order, which is the order of the task and of the Passport. */
export function guarantees(g: ProofGraphData = PROOF_GRAPH): Guarantee[] {
  const depth = new Map(g.nodes.map((n) => [n.id, n.depth]));
  return g.nodes
    .filter((n) => n.kind === "requirement")
    .sort(byLine)
    .map((n) => {
      const cone = dependencyCone(g.edges, n.id);
      const widths = Array.from({ length: n.depth + 1 }, () => 0);
      widths[0] = 1;
      for (const id of cone) widths[n.depth - depth.get(id)!]! += 1;
      const id = n.requirement!;
      const statement = README_STATEMENTS[id];
      if (!statement) throw new Error(`no README statement for ${id}`);
      return { id, node: n.id, short: shortName(id), lines: shortLines(id), statement, size: cone.size, levels: n.depth + 1, widths };
    });
}

/** Declarations in the cone of every requirement. */
export function sharedByAll(g: ProofGraphData = PROOF_GRAPH): string[] {
  const cones = g.nodes.filter((n) => n.kind === "requirement").map((n) => dependencyCone(g.edges, n.id));
  return g.nodes.filter((n) => cones.every((c) => c.has(n.id))).map((n) => n.id);
}

// ---------------------------------------------------------------------------------------------
// Geometry. All lenses share the square frame of layoutGraph (side 640, centre 320).

export const FRAME = 640;
const C = FRAME / 2;
const TAU = Math.PI * 2;
const round = (x: number) => Math.round(x * 100) / 100;

export interface Ellipse {
  cx: number;
  cy: number;
  rx: number;
  ry: number;
  /** Rotation in degrees. */
  rot: number;
}

/** The tilted orbit of the kernels around the bell (lens 3), and its flatter form between the lemmas and the definitions (lens 2). */
export const ORBIT: Ellipse = { cx: C, cy: 300, rx: 372, ry: 62, rot: -8 };
export const ORBIT_LAYERS: Ellipse = { cx: C, cy: 404, rx: 368, ry: 26, rot: -3 };

/** A point of a rotated ellipse at parameter `a` (radians); `z` is its depth, 1 nearest the viewer. */
export function onEllipse(e: Ellipse, a: number) {
  const r = (e.rot * Math.PI) / 180;
  const px = e.rx * Math.cos(a);
  const py = e.ry * Math.sin(a);
  return { x: e.cx + px * Math.cos(r) - py * Math.sin(r), y: e.cy + px * Math.sin(r) + py * Math.cos(r), z: Math.sin(a) };
}

/** Where the six kernels sit on the orbit, as ellipse parameters: two at the sides, two behind, two in front. */
export const KERNEL_PHASES = [0, 1, 2, 3, 4, 5].map((i) => round(((i * 60 + 12) * Math.PI) / 180));

export interface LayersLayout {
  nodes: Record<string, { x: number; y: number }>;
  /** Rows from the top: requirements, then lemmas, then definitions and types. */
  rows: { kind: "requirement" | "lemma" | "definition"; y: number; ids: string[] }[];
  kernels: { x: number; y: number }[];
  /** Short names of the requirements, two lines each, above their squares. */
  labels: { id: string; x: number; lines: string[] }[];
  labelY: number;
}

/**
 * Lens 2. Requirements in source order across the top; lemmas in rows below them, deepest first;
 * definitions and types in rows at the bottom, deepest first. Within a row a declaration sits
 * under the mean position of the declarations that use it, so most uses run straight down.
 */
export function layoutLayers(g: ProofGraphData = PROOF_GRAPH): LayersLayout {
  const radial = layoutGraph(g);
  const angle = new Map(radial.nodes.map((n) => [n.id, Math.atan2(n.y - C, n.x - C)]));
  const users = new Map<string, string[]>();
  for (const [a, b] of g.edges) users.set(b, [...(users.get(b) ?? []), a]);
  const pos: Record<string, { x: number; y: number }> = {};
  const rows: LayersLayout["rows"] = [];
  const left = 24;
  const right = FRAME - 24;

  const place = (kind: LayersLayout["rows"][number]["kind"], ids: string[], y: number, maxGap: number) => {
    const n = ids.length;
    const gap = n > 1 ? Math.min(maxGap, (right - left) / (n - 1)) : 0;
    const x0 = C - (gap * (n - 1)) / 2;
    ids.forEach((id, i) => (pos[id] = { x: round(x0 + i * gap), y }));
    rows.push({ kind, y, ids });
  };
  /** Order a row by the mean x of the placed users; ties and unplaced users fall back to the radial angle. */
  const ordered = (ids: string[]) => {
    const key = new Map(
      ids.map((id) => {
        const xs = (users.get(id) ?? []).map((u) => pos[u]?.x).filter((x): x is number => x !== undefined);
        return [id, xs.length ? xs.reduce((a, b) => a + b, 0) / xs.length : C + 200 * Math.cos(angle.get(id)!)];
      }),
    );
    return ids.slice().sort((a, b) => key.get(a)! - key.get(b)! || a.localeCompare(b));
  };
  /** Split nodes, deepest first, into `k` rows of nearly equal length and place them from `y0` by `dy`. */
  const band = (kind: "lemma" | "definition", nodes: GraphNode[], k: number, y0: number, dy: number, maxGap: number) => {
    const sorted = nodes.slice().sort((a, b) => b.depth - a.depth || a.id.localeCompare(b.id));
    const per = Math.ceil(sorted.length / k);
    for (let r = 0; r < k; r++) place(kind, ordered(sorted.slice(r * per, (r + 1) * per).map((n) => n.id)), y0 + r * dy, maxGap);
  };

  const reqs = g.nodes.filter((n) => n.kind === "requirement").sort(byLine);
  place("requirement", reqs.map((n) => n.id), 112, 80);
  band("lemma", g.nodes.filter((n) => n.kind === "lemma"), 3, 214, 64, 40);
  band("definition", g.nodes.filter((n) => n.kind === "definition" || n.kind === "type"), 2, 470, 70, 30);

  const kernels = g.passport.kernels.map((_, i) => {
    const p = onEllipse(ORBIT_LAYERS, KERNEL_PHASES[i]!);
    return { x: round(p.x), y: round(p.y) };
  });
  const labels = reqs.map((n) => ({ id: n.requirement!, x: pos[n.id]!.x, lines: shortLines(n.requirement!) }));
  return { nodes: pos, rows, kernels, labels, labelY: 82 };
}

export interface BellLevel {
  /** Index from the top; level 0 is the guarantee alone. */
  level: number;
  y: number;
  rx: number;
  ry: number;
  /** Declarations on the ring, in order around it. */
  ids: string[];
  /** Ellipse parameter of the first declaration; the others follow evenly. */
  phase: number;
}

export interface Bell {
  node: string;
  levels: BellLevel[];
}

/** Vertical distance between levels and the y of the lowest one; the same for every guarantee. */
export const BELL = { base: 566, step: 54, rx0: 30, rxPerRoot: 64, tilt: 0.25 } as const;

/** Ring half-width for a level of `n` declarations: the area under the ring grows with the count. */
export const ringRadius = (n: number) => round(BELL.rx0 + BELL.rxPerRoot * (Math.sqrt(n) - 1));

/** The nodes and edges a bell needs: the proof graph or the graph of another run. */
export interface GraphLike {
  nodes: { id: string; depth: number }[];
  edges: [string, string][];
}

/**
 * Lens 3 for one guarantee: its cone by depth, one ring per level. Around each ring the
 * declarations follow `angle` (for the proof graph, their angles in the radial lens, so the shape
 * turns out of it); without one, each sits at the mean angle of the declarations above that use it.
 */
export function bellOf(node: string, g: GraphLike = PROOF_GRAPH, angle?: Map<string, number>): Bell {
  if (!angle && g === PROOF_GRAPH) {
    const radial = layoutGraph(PROOF_GRAPH);
    angle = new Map(radial.nodes.map((n) => [n.id, Math.atan2(n.y - C, n.x - C)]));
  }
  const depth = new Map(g.nodes.map((n) => [n.id, n.depth]));
  const top = depth.get(node);
  if (top === undefined) throw new Error(`no node ${node}`);
  const cone = [...dependencyCone(g.edges, node)];
  const users = new Map<string, string[]>();
  for (const [a, b] of g.edges) users.set(b, [...(users.get(b) ?? []), a]);
  const placed = new Map<string, number>();
  const levels: BellLevel[] = [];
  for (let level = 0; level <= top; level++) {
    let ids = level === 0 ? [node] : cone.filter((id) => top - depth.get(id)! === level);
    const key = (id: string, i: number) =>
      angle?.get(id) ?? meanAngle((users.get(id) ?? []).map((u) => placed.get(u)).filter((x): x is number => x !== undefined), (i * TAU) / ids.length);
    const keys = new Map(ids.sort().map((id, i) => [id, key(id, i)]));
    ids = ids.sort((a, b) => keys.get(a)! - keys.get(b)! || a.localeCompare(b));
    const rx = level === 0 ? 0 : ringRadius(ids.length);
    const first = ids.length ? keys.get(ids[0]!)! : 0;
    // A small turn per level (the golden angle) keeps declarations of neighbouring rings from lining up.
    const phase = round(first + level * 2.39996);
    ids.forEach((id, i) => placed.set(id, phase + (i * TAU) / ids.length));
    levels.push({ level, y: BELL.base - (top - level) * BELL.step, rx, ry: round(rx * BELL.tilt), ids, phase });
  }
  return { node, levels };
}

/** Circular mean of angles; `fallback` when there are none or they cancel out. */
function meanAngle(as: number[], fallback: number) {
  let x = 0;
  let y = 0;
  for (const a of as) {
    x += Math.cos(a);
    y += Math.sin(a);
  }
  return as.length && Math.hypot(x, y) > 1e-9 ? Math.atan2(y, x) : fallback;
}

/** The kernels' orbit around a bell: tilted, through the middle of its height. */
export const orbitFor = (b: Bell): Ellipse => ({ ...ORBIT, cy: round((b.levels[0]!.y + BELL.base) / 2 + 12) });

/** A declaration's place on its ring at turn `theta`; `z` is 1 at the front of the ring and -1 at the back. */
export function bellPoint(l: BellLevel, i: number, theta: number) {
  if (l.level === 0) return { x: C, y: l.y, z: 1 };
  const a = l.phase + (i * TAU) / l.ids.length + theta;
  return { x: C + l.rx * Math.cos(a), y: l.y + l.ry * Math.sin(a), z: Math.sin(a) };
}
