import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { PROOF_GRAPH as g } from "../lib/proofgraph";
import {
  BELL,
  GRAPH_TASK,
  KERNEL_PHASES,
  ORBIT,
  ORBIT_LAYERS,
  README_STATEMENTS,
  bellOf,
  bellPoint,
  guarantees,
  layoutLayers,
  onEllipse,
  orbitFor,
  ringRadius,
  sharedByAll,
  shortLines,
  shortName,
} from "../lib/lenses";
import { ROOT } from "../scripts/lib/results.mjs";

// The hero's three lenses. Every figure is recomputed here from generated/proof-graph.json with
// an independent walk of its edges, and every quoted statement is compared with the task README.

const read = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");
const task = JSON.parse(read(`${GRAPH_TASK.dir}/task.json`)) as { requirements: [string, string][] };
const readme = read(`${GRAPH_TASK.dir}/README.md`);

const depth = new Map(g.nodes.map((n) => [n.id, n.depth]));
const kind = new Map(g.nodes.map((n) => [n.id, n.kind]));
/** Everything `id` uses, by breadth-first search over the edge list. */
function uses(id: string): Set<string> {
  const seen = new Set<string>();
  let frontier = [id];
  while (frontier.length) {
    const next: string[] = [];
    for (const [a, b] of g.edges) if (frontier.includes(a) && !seen.has(b)) (seen.add(b), next.push(b));
    frontier = next;
  }
  return seen;
}

describe("the guarantees of the verified Balancer repair", () => {
  const gs = guarantees();

  it("are the task's eight requirement theorems, in the order the task locks them", () => {
    expect(gs.map((x) => [x.id, x.node])).toEqual(task.requirements);
  });

  it("quote each requirement's statement from the README table verbatim", () => {
    const rows = new Map([...readme.matchAll(/^\| (REQ-[A-Z-]+) \| (.+) \|$/gm)].map((m) => [m[1]!, m[2]!]));
    expect([...rows.keys()].sort()).toEqual(task.requirements.map(([id]) => id).sort());
    for (const x of gs) {
      expect(x.statement, x.id).toBe(rows.get(x.id));
      expect(README_STATEMENTS[x.id]).toBe(rows.get(x.id));
    }
  });

  it("rest on the declarations the kernel records, counted by an independent walk", () => {
    for (const x of gs) expect(x.size, x.id).toBe(uses(x.node).size);
    expect(Object.fromEntries(gs.map((x) => [x.node, x.size]))).toEqual({
      req_given_out_charges_at_least: 33,
      req_given_out_charges_at_most: 34,
      req_given_out_succeeds: 41,
      req_given_in_pays_at_least: 35,
      req_given_in_succeeds: 43,
      req_given_in_pays_at_most: 36,
      req_swap_keeps_value: 61,
      req_batch_keeps_value: 64,
    });
  });

  it("stack by dependency depth: one level per depth, the theorem alone on top", () => {
    for (const x of gs) {
      const top = depth.get(x.node)!;
      expect(x.levels).toBe(top + 1);
      const widths = Array.from({ length: top + 1 }, (_, l) => (l === 0 ? 1 : [...uses(x.node)].filter((id) => depth.get(id) === top - l).length));
      expect(x.widths, x.id).toEqual(widths);
      expect(x.widths.reduce((a, b) => a + b, 0)).toBe(x.size + 1);
    }
    const batch = gs.find((x) => x.id === "REQ-BATCH-KEEPS-VALUE")!;
    expect(batch.size).toBe(64);
    expect(batch.levels).toBe(10);
    expect(batch.widths).toEqual([1, 1, 2, 2, 3, 6, 10, 15, 18, 7]);
  });

  it("all use the lemma aux_bal_eq, the only lemma under every one", () => {
    const shared = sharedByAll();
    for (const x of gs) expect(uses(x.node).has("aux_bal_eq"), x.id).toBe(true);
    expect(shared.filter((id) => kind.get(id) === "lemma")).toEqual(["aux_bal_eq"]);
    expect(shared.length).toBe(g.nodes.filter((n) => gs.every((x) => uses(x.node).has(n.id))).length);
  });

  it("have short names made of the words of their IDs", () => {
    for (const [id] of task.requirements) {
      const words = id.toLowerCase().split("-");
      const short = shortName(id).split(" ");
      // In order, a subsequence of the ID's words, never REQ, and the verb and its bound kept.
      let k = 0;
      for (const w of short) {
        k = words.indexOf(w, k) + 1;
        expect(k, `${id}: ${w}`).toBeGreaterThan(0);
      }
      expect(short).not.toContain("req");
      expect(shortLines(id).join(" ")).toBe(shortName(id));
    }
    expect(gs.map((x) => x.short)).toEqual([
      "given in succeeds",
      "given out succeeds",
      "pays at most",
      "pays at least",
      "charges at least",
      "charges at most",
      "swap keeps value",
      "batch keeps value",
    ]);
    expect(new Set(gs.map((x) => x.short)).size).toBe(gs.length);
  });
});

describe("lens 2: the layers", () => {
  const l = layoutLayers();

  it("places every declaration once, inside the frame, never two in one place", () => {
    expect(Object.keys(l.nodes).sort()).toEqual(g.nodes.map((n) => n.id).sort());
    expect(l.rows.flatMap((r) => r.ids).sort()).toEqual(g.nodes.map((n) => n.id).sort());
    const at = new Set<string>();
    for (const [id, p] of Object.entries(l.nodes)) {
      expect(p.x, id).toBeGreaterThanOrEqual(0);
      expect(p.x, id).toBeLessThanOrEqual(640);
      expect(p.y, id).toBeGreaterThan(0);
      expect(p.y, id).toBeLessThan(640);
      const key = `${p.x},${p.y}`;
      expect(at.has(key), id).toBe(false);
      at.add(key);
    }
  });

  it("puts the requirements on top in task order, then the lemmas, then the definitions and types", () => {
    expect(l.rows[0]!.kind).toBe("requirement");
    expect(l.rows[0]!.ids).toEqual(task.requirements.map(([, thm]) => thm));
    const xs = l.rows[0]!.ids.map((id) => l.nodes[id]!.x);
    expect(xs).toEqual([...xs].sort((a, b) => a - b));
    for (const r of l.rows) {
      for (const id of r.ids) {
        const k = kind.get(id)!;
        expect(r.kind === "definition" ? k === "definition" || k === "type" : k === r.kind, id).toBe(true);
        expect(l.nodes[id]!.y).toBe(r.y);
      }
    }
    const ys = l.rows.map((r) => r.y);
    expect(ys).toEqual([...ys].sort((a, b) => a - b));
    expect(new Set(ys).size).toBe(ys.length);
    const order = l.rows.map((r) => r.kind);
    expect(order.lastIndexOf("requirement")).toBeLessThan(order.indexOf("lemma"));
    expect(order.lastIndexOf("lemma")).toBeLessThan(order.indexOf("definition"));
    expect(l.labels.map((x) => x.id)).toEqual(task.requirements.map(([id]) => id));
    expect(l.labels.map((x) => x.lines.join(" "))).toEqual(task.requirements.map(([id]) => shortName(id)));
  });

  it("keeps the deeper lemmas and definitions in the higher rows", () => {
    for (const k of ["lemma", "definition"] as const) {
      const rows = l.rows.filter((r) => r.kind === k);
      for (let i = 1; i < rows.length; i++) {
        const above = Math.min(...rows[i - 1]!.ids.map((id) => depth.get(id)!));
        const below = Math.max(...rows[i]!.ids.map((id) => depth.get(id)!));
        expect(above).toBeGreaterThanOrEqual(below);
      }
    }
  });

  it("puts the six kernels on the flat orbit between the lemmas and the definitions", () => {
    expect(l.kernels).toHaveLength(g.passport.kernels.length);
    l.kernels.forEach((k, i) => {
      const p = onEllipse(ORBIT_LAYERS, KERNEL_PHASES[i]!);
      expect(k.x).toBeCloseTo(p.x, 1);
      expect(k.y).toBeCloseTo(p.y, 1);
    });
  });
});

describe("lens 3: one guarantee as a bell", () => {
  const gs = guarantees();

  it("has one ring per level, as wide as the declarations on it, holding exactly the cone", () => {
    for (const x of gs) {
      const b = bellOf(x.node);
      expect(b.levels.map((l) => l.ids.length), x.id).toEqual(x.widths);
      expect(b.levels[0]!.ids).toEqual([x.node]);
      expect(b.levels.slice(1).flatMap((l) => l.ids).sort()).toEqual([...uses(x.node)].sort());
      const top = depth.get(x.node)!;
      for (const l of b.levels) for (const id of l.ids) expect(depth.get(id), id).toBe(top - l.level);
      // The lowest ring sits on the same base for every guarantee; the levels are evenly spaced.
      expect(b.levels.at(-1)!.y).toBe(BELL.base);
      b.levels.forEach((l, i) => expect(l.y).toBe(BELL.base - (b.levels.length - 1 - i) * BELL.step));
      for (const l of b.levels.slice(1)) {
        expect(l.rx).toBe(ringRadius(l.ids.length));
        expect(l.ry).toBeCloseTo(l.rx * BELL.tilt, 1);
      }
    }
  });

  it("draws wider rings for more declarations, and fits the widest in the frame", () => {
    for (let n = 1; n < 30; n++) expect(ringRadius(n + 1)).toBeGreaterThan(ringRadius(n));
    const widest = Math.max(...gs.flatMap((x) => x.widths.slice(1)));
    expect(widest).toBe(18);
    expect(320 - ringRadius(widest)).toBeGreaterThan(0);
    const tallest = Math.max(...gs.map((x) => x.levels));
    expect(BELL.base - (tallest - 1) * BELL.step).toBeGreaterThan(30);
  });

  it("turns each declaration on its ring, brighter at the front", () => {
    const b = bellOf("req_batch_keeps_value");
    for (const theta of [0, 1, 2.5]) {
      for (const l of b.levels.slice(1)) {
        l.ids.forEach((_, i) => {
          const p = bellPoint(l, i, theta);
          expect(((p.x - 320) / l.rx) ** 2 + ((p.y - l.y) / l.ry) ** 2).toBeCloseTo(1, 5);
          expect(p.z).toBeCloseTo((p.y - l.y) / l.ry, 5);
        });
      }
    }
    expect(bellPoint(b.levels[0]!, 0, 1)).toEqual({ x: 320, y: b.levels[0]!.y, z: 1 });
    // The kernel orbit passes through each bell, between its top and its base.
    for (const x of gs) {
      const bx = bellOf(x.node);
      const o = orbitFor(bx);
      expect({ ...o, cy: 0 }).toEqual({ ...ORBIT, cy: 0 });
      expect(o.cy).toBeGreaterThan(bx.levels[0]!.y);
      expect(o.cy).toBeLessThan(BELL.base);
    }
  });
});
