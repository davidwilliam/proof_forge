// "A guarantee with a hole" in the hero's guarantee lens: one guarantee of a run that did not
// verify, drawn as a bell like the verified ones, from the extracted graph of that run
// (generated/shapes/, lib/shapes.ts). The guarantee hangs from lemmas the run left as `sorry`
// (its holes); the declarations between the guarantee and a hole are the chain that fails with it.
// tests/hole.test.ts recomputes everything here from the JSON, the run and the task README.

import { ATTEMPT_SHAPES, SHAPES_SUMMARY, type Shape } from "@/lib/shapes";
import { bellOf, shortName, type Bell } from "@/lib/lenses";
import { dependencyCone, transitiveReduction } from "@/lib/proofgraph";

/**
 * The run and guarantee shown. No Muse run verifies Compound. REQ-NO-BACKDATED-REWARDS is open in
 * every Compound run measured; in this one (Muse Spark with the Muse Wonder planner, top-down) it
 * hangs from four lemmas left as `sorry`.
 */
export const HOLE_PICK = { run: "results/library-1/rw-compound-comp/A2-topdown-3", guarantee: "REQ-NO-BACKDATED-REWARDS" } as const;

export type HoleRole = "top" | "chain" | "hole" | "plain";

export interface HoleView {
  task: { id: string; name: string };
  run: { dir: string; arm: string; model: string; planner: string | null; source: string };
  /** The run has no Passport: no kernel check accepted it. */
  passport: null;
  guarantee: { id: string; node: string; short: string; quote: string; readme: { file: string; line: number }; size: number; levels: number; widths: number[] };
  holes: { id: string; kind: string; hole: string; file: string; lines: [number, number]; level: number }[];
  /** Runs of the same task measured, and whether the guarantee is open in every one of them. */
  openInEveryRun: { runs: number; open: boolean };
  nodes: { id: string; kind: string; origin: string; depth: number; role: HoleRole }[];
  /** Edges of the transitive reduction of the guarantee's cone, [user, used], and whether they lie on the chain. */
  edges: { from: string; to: string; chain: boolean }[];
  bell: Bell;
}

export function holeView(shapes: Shape[] = ATTEMPT_SHAPES, summary: { compound: { runs: string[]; guaranteesOpenInEveryRun: string[] } } = SHAPES_SUMMARY as never): HoleView {
  const s = shapes.find((x) => x.run.dir === HOLE_PICK.run);
  if (!s) throw new Error(`no shape for ${HOLE_PICK.run}`);
  const g = s.guarantees.find((x) => x.id === HOLE_PICK.guarantee);
  if (!g || !g.readme) throw new Error(`no guarantee ${HOLE_PICK.guarantee} with a README row`);
  if (!g.hangsFrom.length || g.hangsFrom.includes(g.node)) throw new Error(`${g.id} must hang from lemmas`);
  const holeIds = new Set(g.hangsFrom);
  const cone = dependencyCone(s.edges, g.node);
  const inShape = new Set([g.node, ...cone]);
  const edges = s.edges.filter(([a, b]) => inShape.has(a) && inShape.has(b));
  // The chain: declarations of the shape that use a hole, the guarantee included.
  const chain = new Set([...inShape].filter((id) => !holeIds.has(id) && [...dependencyCone(edges, id)].some((x) => holeIds.has(x))));
  const role = (id: string): HoleRole => (id === g.node ? "top" : holeIds.has(id) ? "hole" : chain.has(id) ? "chain" : "plain");
  const nodes = s.nodes.filter((n) => inShape.has(n.id)).map((n) => ({ id: n.id, kind: n.kind, origin: n.origin, depth: n.depth, role: role(n.id) }));
  const onChain = (id: string) => chain.has(id) || holeIds.has(id);
  const bell = bellOf(g.node, { nodes, edges });
  const top = g.depth;
  return {
    task: { id: s.task.id, name: s.task.name },
    run: { dir: s.run.dir, arm: s.run.arm, model: s.run.model, planner: s.run.planner, source: s.source.file },
    passport: null,
    guarantee: {
      id: g.id,
      node: g.node,
      short: shortName(g.id),
      quote: g.readme.text,
      readme: { file: g.readme.file, line: g.readme.line },
      size: g.size,
      levels: top + 1,
      widths: bell.levels.map((l) => l.ids.length),
    },
    holes: s.holes
      .filter((x) => holeIds.has(x.id))
      .map((x) => ({ id: x.id, kind: x.kind, hole: x.hole, file: x.file, lines: x.lines, level: top - x.depth }))
      .sort((a, b) => a.level - b.level || a.id.localeCompare(b.id)),
    openInEveryRun: { runs: summary.compound.runs.length, open: summary.compound.guaranteesOpenInEveryRun.includes(g.id) && s.task.id === "rw-compound-comp" },
    nodes,
    edges: transitiveReduction(edges).map(([from, to]) => ({ from, to, chain: chain.has(from) && onChain(to) })),
    bell,
  };
}
