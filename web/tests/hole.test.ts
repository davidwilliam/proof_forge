import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { HOLE_PICK, holeView } from "../lib/hole";
import { BELL, ringRadius } from "../lib/lenses";
import { ROOT } from "../scripts/lib/results.mjs";

// The hero's "A guarantee with a hole", recomputed from the committed run and its extracted graph.

const read = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");
const h = holeView();
const shape = JSON.parse(read(`web/generated/shapes/holes-compound-A2-topdown-3.json`)) as {
  run: { dir: string };
  nodes: { id: string; depth: number; hole: string | null; kind: string }[];
  edges: [string, string][];
};

function uses(id: string): Set<string> {
  const seen = new Set<string>();
  let frontier = [id];
  while (frontier.length) {
    const next: string[] = [];
    for (const [a, b] of shape.edges) if (frontier.includes(a) && !seen.has(b)) (seen.add(b), next.push(b));
    frontier = next;
  }
  return seen;
}

describe("a guarantee with a hole", () => {
  it("comes from a run that did not verify and has no Passport", () => {
    expect(shape.run.dir).toBe(HOLE_PICK.run);
    expect(existsSync(path.join(ROOT, HOLE_PICK.run, "passport.json"))).toBe(false);
    const summary = JSON.parse(read(`${HOLE_PICK.run}/summary.json`));
    expect(summary.accepted_in_session).toBe(false);
    expect(summary.final_status[h.guarantee.node]).toBe("SORRY");
    expect(h.passport).toBeNull();
  });

  it("quotes the requirement from the task README", () => {
    const tj = JSON.parse(read(`realworld/tasks/${h.task.id}/task.json`)) as { requirements: [string, string][] };
    expect(tj.requirements).toContainEqual([h.guarantee.id, h.guarantee.node]);
    const row = read(h.guarantee.readme.file).split("\n")[h.guarantee.readme.line - 1]!;
    expect(row).toBe(`| ${h.guarantee.id} | ${h.guarantee.quote} |`);
    expect(h.guarantee.readme.file).toBe(`realworld/tasks/${h.task.id}/README.md`);
  });

  it("hangs from lemmas left as sorry, each a sorry in the run's source", () => {
    const cone = uses(h.guarantee.node);
    const holes = [...cone, h.guarantee.node].filter((id) => shape.nodes.find((n) => n.id === id)!.hole);
    expect(h.holes.map((x) => x.id).sort()).toEqual(holes.sort());
    expect(h.holes.map((x) => x.id).sort()).toEqual(["td0_exec_inv", "td0_exec_potentialTo_le", "td0_potentialTo_of_no_position", "td0_scaled_le_add"]);
    for (const x of h.holes) {
      expect(x.kind).toBe("lemma");
      expect(x.hole).toBe("sorry");
      const src = read(x.file).split("\n").slice(x.lines[0] - 1, x.lines[1]).join("\n");
      expect(src).toMatch(new RegExp(`theorem\\s+${x.id}\\b`));
      expect(src).toMatch(/\bsorry\b/);
    }
  });

  it("is open in every Compound run measured", () => {
    const summary = JSON.parse(read("web/generated/shapes/summary.json"));
    expect(h.openInEveryRun).toEqual({ runs: summary.compound.runs.length, open: true });
    expect(summary.compound.runs).toHaveLength(3);
    for (const run of summary.compound.runs) {
      const s = JSON.parse(read(`${run}/summary.json`));
      expect(s.final_status[h.guarantee.node], run).not.toBe("PROVED");
    }
  });

  it("is the same kind of bell as the verified guarantees, measured from the run's graph", () => {
    const depth = new Map(shape.nodes.map((n) => [n.id, n.depth]));
    const top = depth.get(h.guarantee.node)!;
    const cone = uses(h.guarantee.node);
    expect(h.guarantee.size).toBe(cone.size);
    expect(h.guarantee.levels).toBe(top + 1);
    expect(h.guarantee.widths).toEqual(Array.from({ length: top + 1 }, (_, l) => (l === 0 ? 1 : [...cone].filter((id) => depth.get(id) === top - l).length)));
    expect(h.bell.levels.slice(1).flatMap((l) => l.ids).sort()).toEqual([...cone].sort());
    for (const l of h.bell.levels.slice(1)) expect(l.rx).toBe(ringRadius(l.ids.length));
    expect(h.bell.levels.at(-1)!.y).toBe(BELL.base);
    for (const x of h.holes) {
      expect(x.level).toBe(top - depth.get(x.id)!);
      expect(h.bell.levels[x.level]!.ids).toContain(x.id);
    }
  });

  it("marks as the chain exactly the declarations that use a hole", () => {
    const holes = new Set(h.holes.map((x) => x.id));
    for (const n of h.nodes) {
      const above = !holes.has(n.id) && [...uses(n.id)].some((x) => holes.has(x));
      expect(n.role === "chain" || n.role === "top", n.id).toBe(above);
      expect(n.role === "hole", n.id).toBe(holes.has(n.id));
    }
    for (const e of h.edges) {
      const role = (id: string) => h.nodes.find((n) => n.id === id)!.role;
      expect(e.chain, `${e.from} > ${e.to}`).toBe(role(e.from) !== "plain" && role(e.from) !== "hole" && role(e.to) !== "plain");
      expect(shape.edges).toContainEqual([e.from, e.to]);
    }
    for (const x of h.holes) expect(h.edges.some((e) => e.chain && e.to === x.id), x.id).toBe(true);
  });
});
