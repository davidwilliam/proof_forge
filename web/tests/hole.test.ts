import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { HOLE_PICK, REFERS_ELSEWHERE, holeRun } from "../lib/hole";
import { BELL, displayQuote, ringRadius, shortLines, shortName } from "../lib/lenses";
import { ROOT } from "../scripts/lib/results.mjs";

// The hero's "A guarantee with a hole", recomputed from the committed run and its extracted graph.

const read = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");
const h = holeRun();
const shape = JSON.parse(read(`web/generated/shapes/holes-compound-A2-topdown-3.json`)) as {
  run: { dir: string };
  build: { ok: boolean };
  nodes: { id: string; depth: number; hole: string | null; kind: string }[];
  edges: [string, string][];
  guarantees: { id: string; statement: { text: string; file: string; lines: [number, number] } }[];
};
const tj = JSON.parse(read(`realworld/tasks/${h.task.id}/task.json`)) as { requirements: [string, string][] };
const readme = read(`realworld/tasks/${h.task.id}/README.md`);
// A row names one requirement or several ("REQ-SUPPLY-HOOK, REQ-BORROW-HOOK").
const rowLines = readme.split("\n").map((l, i) => ({ l, line: i + 1, m: /^\| (REQ-[A-Z-]+(?:, REQ-[A-Z-]+)*) \| (.+) \|$/.exec(l) }));
const rows = new Map(rowLines.filter((r) => r.m).flatMap((r) => r.m![1]!.split(", ").map((id) => [id, { text: r.m![2]!, line: r.line }] as const)));
const runSummary = JSON.parse(read(`${HOLE_PICK.run}/summary.json`));
const depth = new Map(shape.nodes.map((n) => [n.id, n.depth]));
const isHole = new Set(shape.nodes.filter((n) => n.hole).map((n) => n.id));

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
    expect(runSummary.accepted_in_session).toBe(false);
    expect(h.passport).toBeNull();
    expect(h.run.name).toBe("A2-topdown-3");
  });

  it("has a bar for each of the task's guarantees, in task order, labelled from its ID and sized by its shape", () => {
    expect(h.guarantees.map((x) => [x.id, x.node])).toEqual(tj.requirements);
    for (const x of h.guarantees) {
      expect(x.size, x.id).toBe(uses(x.node).size);
      expect(x.short).toBe(shortName(x.id));
      expect(x.lines).toEqual(shortLines(x.id));
    }
    expect(h.guarantees.map((x) => x.size)).toEqual([29, 35, 37, 35, 31, 73, 71, 57]);
    expect(h.guarantees[h.initial]!.id).toBe("REQ-NO-BACKDATED-REWARDS");
  });

  it("marks each bar proved or hanging from holes, as the run's own check left it", () => {
    for (const x of h.guarantees) {
      const holes = [...uses(x.node), x.node].filter((id) => isHole.has(id));
      expect(x.holes.map((y) => y.id).sort(), x.id).toEqual(holes.sort());
      expect(x.complete, x.id).toBe(holes.length === 0 && shape.build.ok);
      expect(runSummary.final_status[x.node] === "PROVED", x.id).toBe(x.complete);
    }
    // In this run every guarantee hangs from at least one hole.
    expect(h.guarantees.every((x) => !x.complete)).toBe(true);
    const nb = h.guarantees[h.initial]!;
    expect(nb.holes.map((x) => x.id).sort()).toEqual(["td0_exec_inv", "td0_exec_potentialTo_le", "td0_potentialTo_of_no_position", "td0_scaled_le_add"]);
    expect(h.guarantees.find((x) => x.id === "REQ-REWARDS-BOUNDED")!.holes).toHaveLength(3);
  });

  it("has holes that are sorry in the run's source", () => {
    for (const x of h.guarantees.flatMap((g) => g.holes)) {
      expect(x.hole).toBe("sorry");
      const src = read(x.file).split("\n").slice(x.lines[0] - 1, x.lines[1]).join("\n");
      expect(src).toMatch(new RegExp(`theorem\\s+${x.id}\\b`));
      expect(src).toMatch(/\bsorry\b/);
    }
  });

  it("quotes the README row, or the locked doc comment where the row points elsewhere", () => {
    for (const x of h.guarantees) {
      const { text: row, line } = rows.get(x.id)!;
      expect(row, x.id).toBeTruthy();
      if (REFERS_ELSEWHERE.test(row)) {
        const st = shape.guarantees.find((g) => g.id === x.id)!.statement;
        expect(x.quoteFrom.kind, x.id).toBe("specification");
        expect(x.quote).toBe(st.text);
        // The doc comment, with its line breaks joined, at the recorded lines of the locked specification.
        const text = read(st.file).split("\n").slice(st.lines[0] - 1, st.lines[1]).join(" ").replace(/\s+/g, " ");
        expect(text).toContain(`${x.id}: ${x.quote}`);
      } else {
        expect(x.quoteFrom).toEqual({ kind: "readme", file: `realworld/tasks/${h.task.id}/README.md`, line });
        expect(x.quote, x.id).toBe(row);
      }
    }
    expect(h.guarantees.filter((x) => x.quoteFrom.kind === "specification").map((x) => x.id)).toEqual(["REQ-REWARDS-BOUNDED", "REQ-ACCOUNT-BOUNDED"]);
    expect(h.guarantees[h.initial]!.quote).toBe("an account with no position gains at most the COMP emitted from then on");
  });

  it("reads open in every Compound run measured only for the guarantees that are", () => {
    const summary = JSON.parse(read("web/generated/shapes/summary.json"));
    expect(h.runsMeasured).toBe(summary.compound.runs.length);
    expect(h.runsMeasured).toBe(3);
    for (const x of h.guarantees) {
      const open = summary.compound.runs.every((run: string) => JSON.parse(read(`${run}/summary.json`)).final_status[x.node] !== "PROVED");
      expect(x.openInEveryRun, x.id).toBe(open);
    }
    expect(h.guarantees.filter((x) => x.openInEveryRun).map((x) => x.id)).toEqual(["REQ-REWARDS-BOUNDED", "REQ-ACCOUNT-BOUNDED", "REQ-NO-BACKDATED-REWARDS"]);
  });

  it("states the frontier-4 runs that later verified Compound, each with every requirement VERIFIED", () => {
    expect(h.laterVerified).toEqual({ verified: 8, runs: 10, experiment: "frontier-4" });
    for (const run of [1, 3, 4, 5, 6, 7, 8, 9].map((i) => `proofforge-full-${i}`)) {
      const p = JSON.parse(read(`results/frontier-4/judged/rw-compound-comp/${run}/passport.json`));
      expect(p.status).toBe("VERIFIED");
      expect(p.requirements.map((r: { id: string }) => r.id)).toEqual(expect.arrayContaining(["REQ-REWARDS-BOUNDED", "REQ-ACCOUNT-BOUNDED", "REQ-NO-BACKDATED-REWARDS"]));
      expect(p.requirements.every((r: { status: string }) => r.status === "VERIFIED"), run).toBe(true);
    }
  });

  it("draws each guarantee as a bell with the rules of the verified ones", () => {
    h.guarantees.forEach((x, gi) => {
      const top = depth.get(x.node)!;
      const cone = uses(x.node);
      const b = h.bells[gi]!;
      expect(x.levels).toBe(top + 1);
      expect(x.widths).toEqual(Array.from({ length: top + 1 }, (_, l) => (l === 0 ? 1 : [...cone].filter((id) => depth.get(id) === top - l).length)));
      expect(b.levels.map((l) => l.ids.length)).toEqual(x.widths);
      expect(b.levels.slice(1).flatMap((l) => l.ids).sort()).toEqual([...cone].sort());
      for (const l of b.levels.slice(1)) expect(l.rx).toBe(ringRadius(l.ids.length));
      expect(b.levels.at(-1)!.y).toBe(BELL.base);
      for (const y of x.holes) {
        expect(y.level).toBe(top - depth.get(y.id)!);
        expect(b.levels[y.level]!.ids).toContain(y.id);
      }
    });
  });

  it("marks as the chain exactly the declarations that use a hole", () => {
    for (const n of h.nodes) {
      const above = !isHole.has(n.id) && [...uses(n.id)].some((x) => isHole.has(x));
      expect(n.role === "chain", n.id).toBe(above);
      expect(n.role === "hole", n.id).toBe(isHole.has(n.id));
    }
    const role = new Map(h.nodes.map((n) => [n.id, n.role]));
    for (const e of h.edges) {
      expect(e.chain, `${e.from} > ${e.to}`).toBe(role.get(e.from) !== "plain" && role.get(e.to) !== "plain");
      expect(shape.edges).toContainEqual([e.from, e.to]);
    }
    for (const x of h.guarantees[h.initial]!.holes) expect(h.edges.some((e) => e.chain && e.to === x.id), x.id).toBe(true);
  });
});

describe("quotes as displayed", () => {
  it("capitalize only the first letter and keep the rest verbatim", () => {
    for (const q of h.guarantees.map((x) => x.quote)) {
      const d = displayQuote(q);
      expect(d.charAt(0)).toBe(q.charAt(0).toUpperCase());
      expect(d.charAt(0).toLowerCase()).toBe(q.charAt(0).toLowerCase());
      expect(d.slice(1)).toBe(q.slice(1));
    }
    expect(displayQuote("for well-behaved math, a swap")).toBe("For well-behaved math, a swap");
    // A row that continues the one above it keeps its lower case after an ellipsis.
    expect(displayQuote("and at least what")).toBe("…and at least what");
  });
});
