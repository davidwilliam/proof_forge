// "A guarantee with a hole" in the hero's guarantee lens: the guarantees of a run that did not
// verify, drawn as bells like the verified ones, from the extracted graph of that run
// (generated/shapes/, lib/shapes.ts). A guarantee hangs from the declarations of its shape the run
// left as `sorry` (its holes); the declarations that use a hole are the chain that fails with it.
// tests/hole.test.ts recomputes everything here from the JSON, the run and the task README.

import { ATTEMPT_SHAPES, SHAPES_SUMMARY, type Shape } from "@/lib/shapes";
import { bellOf, shortLines, shortName, type Bell } from "@/lib/lenses";
import { dependencyCone, transitiveReduction } from "@/lib/proofgraph";

/**
 * The run and the guarantee shown first. No Muse run verifies Compound. REQ-NO-BACKDATED-REWARDS is
 * open in every Compound run measured; in this one (Muse Spark with the Muse Wonder planner,
 * top-down) it hangs from four lemmas left as `sorry`.
 */
export const HOLE_PICK = { run: "results/library-1/rw-compound-comp/A2-topdown-3", guarantee: "REQ-NO-BACKDATED-REWARDS" } as const;

/**
 * A README row that points elsewhere ("the sequence-level bound below", "the same bound for every
 * single account") does not state the guarantee on its own; for those the quote is the locked
 * specification's doc comment of the property, verbatim.
 */
export const REFERS_ELSEWHERE = /\bbelow\b|^the same\b/;

export type HoleRole = "chain" | "hole" | "plain";

export interface HoleGuarantee {
  id: string;
  node: string;
  short: string;
  lines: string[];
  quote: string;
  /** Where the quote comes from: the task README's requirement table, or the property's doc comment in the locked specification. */
  quoteFrom: { kind: "readme"; file: string; line: number } | { kind: "specification"; file: string; lines: [number, number] };
  size: number;
  levels: number;
  widths: number[];
  /** No hole in its shape and not a hole itself, in a candidate that builds. */
  complete: boolean;
  holes: { id: string; kind: string; hole: string; file: string; lines: [number, number]; level: number }[];
  /** Open in every run of the task that was measured. */
  openInEveryRun: boolean;
}

export interface HoleRun {
  task: { id: string; name: string };
  run: { dir: string; name: string; arm: string; model: string; planner: string | null; source: string };
  /** The run has no Passport: no kernel check accepted it. */
  passport: null;
  runsMeasured: number;
  /** Every declaration of the run's graph; a hole or a declaration that uses one is the same in every shape. */
  nodes: { id: string; kind: string; origin: string; depth: number; role: HoleRole }[];
  /** Edges of the transitive reduction, [user, used]; `chain` when both ends are on a chain to a hole. */
  edges: { from: string; to: string; chain: boolean }[];
  guarantees: HoleGuarantee[];
  bells: Bell[];
  /** Index of the guarantee shown first. */
  initial: number;
}

type Summary = { compound: { runs: string[]; guaranteesOpenInEveryRun: string[] } };

export function holeRun(shapes: Shape[] = ATTEMPT_SHAPES, summary: Summary = SHAPES_SUMMARY as unknown as Summary): HoleRun {
  const s = shapes.find((x) => x.run.dir === HOLE_PICK.run);
  if (!s) throw new Error(`no shape for ${HOLE_PICK.run}`);
  const holeIds = new Set(s.nodes.filter((n) => n.hole).map((n) => n.id));
  const uses = new Map(s.nodes.map((n) => [n.id, dependencyCone(s.edges, n.id)]));
  const chain = new Set(s.nodes.filter((n) => !holeIds.has(n.id) && [...uses.get(n.id)!].some((x) => holeIds.has(x))).map((n) => n.id));
  const role = (id: string): HoleRole => (holeIds.has(id) ? "hole" : chain.has(id) ? "chain" : "plain");
  const onChain = (id: string) => chain.has(id) || holeIds.has(id);
  const depth = new Map(s.nodes.map((n) => [n.id, n.depth]));
  const open = s.task.id === "rw-compound-comp" ? summary.compound.guaranteesOpenInEveryRun : [];
  const guarantees = s.guarantees.map((g): HoleGuarantee => {
    const fromReadme = g.readme && !REFERS_ELSEWHERE.test(g.readme.text);
    const top = depth.get(g.node)!;
    const cone = uses.get(g.node)!;
    return {
      id: g.id,
      node: g.node,
      short: shortName(g.id),
      lines: shortLines(g.id),
      quote: fromReadme ? g.readme!.text : g.statement.text,
      quoteFrom: fromReadme
        ? { kind: "readme", file: g.readme!.file, line: g.readme!.line }
        : { kind: "specification", file: g.statement.file, lines: g.statement.lines },
      size: g.size,
      levels: top + 1,
      widths: Array.from({ length: top + 1 }, (_, l) => (l === 0 ? 1 : [...cone].filter((id) => depth.get(id) === top - l).length)),
      complete: g.complete,
      holes: s.holes
        .filter((x) => g.hangsFrom.includes(x.id))
        .map((x) => ({ id: x.id, kind: x.kind, hole: x.hole, file: x.file, lines: x.lines, level: top - x.depth }))
        .sort((a, b) => a.level - b.level || a.id.localeCompare(b.id)),
      openInEveryRun: open.includes(g.id),
    };
  });
  const initial = guarantees.findIndex((g) => g.id === HOLE_PICK.guarantee);
  if (initial < 0) throw new Error(`no guarantee ${HOLE_PICK.guarantee}`);
  return {
    task: { id: s.task.id, name: s.task.name },
    run: { dir: s.run.dir, name: s.run.dir.split("/").pop()!, arm: s.run.arm, model: s.run.model, planner: s.run.planner, source: s.source.file },
    passport: null,
    runsMeasured: s.task.id === "rw-compound-comp" ? summary.compound.runs.length : 1,
    nodes: s.nodes.map((n) => ({ id: n.id, kind: n.kind, origin: n.origin, depth: n.depth, role: role(n.id) })),
    edges: transitiveReduction(s.edges).map(([from, to]) => ({ from, to, chain: onChain(from) && onChain(to) })),
    guarantees,
    bells: guarantees.map((g) => bellOf(g.node, s)),
    initial,
  };
}
