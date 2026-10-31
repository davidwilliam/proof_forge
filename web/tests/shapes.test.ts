import { createHash } from "node:crypto";
import { readdirSync, readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { PROOF_GRAPH } from "../lib/proofgraph";
import { ROOT, readPassport } from "../scripts/lib/results.mjs";

// generated/shapes/*.json is written by scripts/proof-shapes.mjs, which builds each committed
// candidate in the pinned Lean image and runs the extractor of the home page graph. These checks need
// no Lean: they tie every file to the committed sources by hash, recompute every measurement from the
// nodes and edges with code independent of the generator, and recompute the summary.

const DIR = "web/generated/shapes";
const read = (rel: string) => readFileSync(path.join(ROOT, rel));
const text = (rel: string) => read(rel).toString("utf8");
const sha = (rel: string) => createHash("sha256").update(read(rel)).digest("hex");
const ws1 = (s: string) => s.replace(/\s+/g, " ").trim();

type Node = { id: string; kind: string; origin: string; file: string; lines: [number, number] | null; depth: number; requirement?: string; hole: string | null; library?: string[] };
type Guarantee = {
  id: string;
  theorem: string;
  property: string;
  node: string;
  statement: { text: string; file: string; lines: [number, number] };
  readme: { text: string; file: string; line: number } | null;
  size: number;
  depth: number;
  width: number[];
  composition: Record<string, number>;
  hangsFrom: string[];
  proved: number;
  complete: boolean;
  missing?: boolean;
};
type Shape = {
  slug: string;
  role: "verified" | "attempt";
  definitions: Record<string, string>;
  task: { id: string; name: string; namespace: string; taskJson: { file: string; sha256: string }; readme: { file: string; sha256: string }; challenge: { file: string; sha256: string }; specification: { file: string; sha256: string }[] };
  run: { dir: string; summary: { file: string; sha256: string }; finalStatus: Record<string, string> | null };
  source: { file: string; sha256: string };
  library: { source_tree_sha256: string; git_commit: string; imported: string[] } | null;
  passport: { file: string; sha256: string; status: string; requirements: Record<string, string> } | null;
  build: { ok: boolean; sorryWarningLines: number[]; errorLines: number[]; sorryOutsideShapes: { line: number; declaration: string }[] };
  counts: Record<string, number>;
  guarantees: Guarantee[];
  loadBearing: { every: { id: string; kind: string; origin: string; depth: number }[]; lemmas: { id: string; origin: string; depth: number; guarantees: number }[] };
  holes: { id: string; kind: string; hole: string; origin: string; file: string; lines: [number, number]; depth: number; guarantees: string[] }[];
  missing: string[];
  nodes: Node[];
  edges: [string, string][];
  excluded: string[];
};

const files = readdirSync(path.join(ROOT, DIR)).filter((f) => f.endsWith(".json") && f !== "summary.json").sort();
const shapes: Shape[] = files.map((f) => JSON.parse(text(`${DIR}/${f}`)));
const summary = JSON.parse(text(`${DIR}/summary.json`));
const bySlug = new Map(shapes.map((s) => [s.slug, s]));

/** Code of a Lean file without comments, line structure kept. */
const code = (src: string) => src.replace(/\/-[\s\S]*?-\//g, (m) => m.replace(/[^\n]/g, " ")).replace(/--[^\n]*/g, "");
const declLines = (n: { file: string; lines: [number, number] | null }) => text(n.file).split("\n").slice(n.lines![0] - 1, n.lines![1]).join("\n");

function graph(s: Shape) {
  const out = new Map<string, string[]>();
  for (const [a, b] of s.edges) out.set(a, [...(out.get(a) ?? []), b]);
  const node = new Map(s.nodes.map((n) => [n.id, n]));
  const coneOf = (id: string) => {
    const seen = new Set<string>();
    const todo = [...(out.get(id) ?? [])];
    while (todo.length) {
      const m = todo.pop()!;
      if (seen.has(m)) continue;
      seen.add(m);
      todo.push(...(out.get(m) ?? []));
    }
    return seen;
  };
  const memo = new Map<string, number>();
  const depthOf = (id: string): number => {
    if (memo.has(id)) return memo.get(id)!;
    const ds = out.get(id) ?? [];
    const d = ds.length ? 1 + Math.max(...ds.map(depthOf)) : 0;
    memo.set(id, d);
    return d;
  };
  return { out, node, coneOf, depthOf };
}

describe("shapes of guarantees", () => {
  it("has one file per run named in the summary, each with the hash in the summary", () => {
    expect(files.length).toBe(9);
    expect(summary.files.map((f: { file: string }) => f.file).sort()).toEqual(files.map((f) => `${DIR}/${f}`));
    for (const f of summary.files) expect(sha(f.file), f.file).toBe(f.sha256);
    for (const s of shapes) expect(`${s.slug}.json`).toBe(files.find((f) => f === `${s.slug}.json`));
    for (const k of ["guarantee", "shape", "size", "depth", "width", "loadBearing", "hole", "hangsFrom", "complete"]) {
      expect(summary.definitions[k]).toBeTruthy();
      for (const s of shapes) expect(s.definitions[k]).toBe(summary.definitions[k]);
    }
  });

  it("is the shape of the committed candidate, task and run it names", () => {
    for (const s of shapes) {
      const hashed = [s.source, s.task.taskJson, s.task.readme, s.task.challenge, s.run.summary, ...s.task.specification];
      for (const h of hashed) expect(sha(h.file), `${s.slug} ${h.file}`).toBe(h.sha256);
      expect(s.source.file).toBe(`${s.run.dir}/final.lean`);
      expect(s.task.taskJson.file).toBe(`realworld/tasks/${s.task.id}/task.json`);
      const runSummary = JSON.parse(text(s.run.summary.file));
      expect(runSummary.task).toBe(s.task.id);
      if (s.library) {
        expect(runSummary.library.source_tree_sha256).toBe(s.library.source_tree_sha256);
        expect(runSummary.library.git_commit).toBe(s.library.git_commit);
        for (const m of s.library.imported) expect(text(s.source.file)).toMatch(new RegExp(`^import ${m.replaceAll(".", "\\.")}$`, "m"));
      } else expect(text(s.source.file)).not.toMatch(/^import ProofForgeFin/m);
      if (s.passport) {
        const p = readPassport(s.passport.file);
        expect(p.sha256).toBe(s.passport.sha256);
        expect(p.recomputedSha256).toBe(p.sha256);
        expect(p.status).toBe(s.passport.status);
        expect(p.requirements).toEqual(s.passport.requirements);
        expect(JSON.parse(text(s.passport.file)).solution.files["final.lean"]).toBe(s.source.sha256);
      }
    }
  });

  it("states every guarantee of the task in the committed words of its specification and README", () => {
    for (const s of shapes) {
      const tj = JSON.parse(text(s.task.taskJson.file));
      expect(s.guarantees.map((g) => [g.id, g.theorem])).toEqual(tj.requirements.map(([id, t]: [string, string]) => [id, `${tj.namespace}.${t}`]));
      const challenge = text(s.task.challenge.file);
      for (const g of s.guarantees) {
        expect(challenge).toMatch(new RegExp(`theorem\\s+${g.theorem.split(".").pop()}\\s*:\\s*${g.property}\\b`));
        expect(s.task.specification.map((f) => f.file)).toContain(g.statement.file);
        const doc = text(g.statement.file).split("\n").slice(g.statement.lines[0] - 1, g.statement.lines[1]).join("\n");
        expect(ws1(doc), g.id).toBe(`/-- ${g.id}: ${g.statement.text} -/`);
        expect(text(g.statement.file).split("\n")[g.statement.lines[1]]).toMatch(new RegExp(`(def|abbrev)\\s+${g.property}\\b`));
        if (g.readme) {
          expect(g.readme.file).toBe(s.task.readme.file);
          const row = text(g.readme.file).split("\n")[g.readme.line - 1]!;
          expect(row.startsWith("|") && row.split(" | ")[0]!.includes(g.id), g.id).toBe(true);
          expect(row.trimEnd().endsWith(`${g.readme.text} |`), g.id).toBe(true);
        }
      }
    }
  });

  it("has a well-formed graph: edges between nodes, depth recomputed, every node reached from a guarantee", () => {
    for (const s of shapes) {
      const { node, depthOf, coneOf } = graph(s);
      expect(node.size).toBe(s.nodes.length);
      for (const [a, b] of s.edges) {
        expect(node.has(a) && node.has(b), `${s.slug} ${a} -> ${b}`).toBe(true);
        expect(node.get(a)!.depth).toBeGreaterThan(node.get(b)!.depth);
      }
      for (const n of s.nodes) {
        expect(n.depth, `${s.slug} ${n.id}`).toBe(depthOf(n.id));
        expect(n.lines, n.id).not.toBeNull();
        if (n.origin === "candidate") expect(n.file).toBe(s.source.file);
        else expect(s.task.specification.map((f) => f.file)).toContain(n.file);
      }
      const reached = new Set<string>();
      for (const g of s.guarantees.filter((x) => !x.missing)) {
        reached.add(g.node);
        for (const x of coneOf(g.node)) reached.add(x);
      }
      expect(reached.size).toBe(s.nodes.length);
      expect(s.nodes.filter((n) => n.kind === "requirement").map((n) => n.requirement).sort()).toEqual(s.guarantees.filter((g) => !g.missing).map((g) => g.id).sort());
    }
  });

  it("recomputes every guarantee's size, depth, width, composition, holes and completeness", () => {
    for (const s of shapes) {
      const { node, coneOf } = graph(s);
      const holes = new Set(s.nodes.filter((n) => n.hole).map((n) => n.id));
      for (const g of s.guarantees) {
        if (g.missing) {
          expect(g.complete).toBe(false);
          continue;
        }
        const shape = [...coneOf(g.node)];
        const of = (k: string) => shape.filter((x) => node.get(x)!.kind === k).length;
        expect(g.size, `${s.slug} ${g.id}`).toBe(shape.length);
        expect(g.depth).toBe(node.get(g.node)!.depth);
        const width = Array.from({ length: g.depth }, (_, d) => shape.filter((x) => node.get(x)!.depth === d).length);
        expect(g.width).toEqual(width);
        expect(width.reduce((a, b) => a + b, 0)).toBe(g.size);
        expect(g.composition).toEqual({
          requirements: of("requirement"),
          lemmas: of("lemma"),
          definitions: of("definition"),
          types: of("type"),
          candidate: shape.filter((x) => node.get(x)!.origin === "candidate").length,
          specification: shape.filter((x) => node.get(x)!.origin === "specification").length,
        });
        const hangs = [...(holes.has(g.node) ? [g.node] : []), ...shape.filter((x) => holes.has(x)).sort()];
        expect(g.hangsFrom).toEqual(hangs);
        expect(g.proved).toBe(shape.filter((x) => !holes.has(x)).length);
        expect(g.complete).toBe(hangs.length === 0 && s.build.ok);
      }
      const present = s.guarantees.filter((g) => !g.missing);
      const cones = new Map(present.map((g) => [g.node, coneOf(g.node)]));
      expect(s.loadBearing.every.map((n) => n.id).sort()).toEqual(s.nodes.filter((n) => present.every((g) => cones.get(g.node)!.has(n.id))).map((n) => n.id).sort());
      const lemmaUse = s.nodes.filter((n) => n.kind === "lemma").map((n) => [n.id, present.filter((g) => cones.get(g.node)!.has(n.id)).length] as const).filter(([, c]) => c > 0);
      expect(Object.fromEntries(s.loadBearing.lemmas.map((l) => [l.id, l.guarantees]))).toEqual(Object.fromEntries(lemmaUse));
      expect(s.holes.map((h) => [h.id, h.guarantees])).toEqual(s.nodes.filter((n) => n.hole).map((n) => [n.id, present.filter((g) => g.hangsFrom.includes(n.id)).map((g) => g.id)]));
      expect(s.counts).toEqual({
        guarantees: s.guarantees.length,
        complete: s.guarantees.filter((g) => g.complete).length,
        nodes: s.nodes.length,
        edges: s.edges.length,
        holes: s.holes.length,
        lemmas: s.nodes.filter((n) => n.kind === "lemma").length,
        definitions: s.nodes.filter((n) => n.kind === "definition").length,
        types: s.nodes.filter((n) => n.kind === "type").length,
        excluded: s.excluded.length,
      });
    }
  });

  it("puts every hole on a declaration whose source says sorry, with Lean's warning inside it", () => {
    for (const s of shapes) {
      const src = code(text(s.source.file)).split("\n");
      const warned = new Set(s.build.sorryWarningLines);
      for (const n of s.nodes.filter((x) => x.origin === "candidate")) {
        const body = src.slice(n.lines![0] - 1, n.lines![1]).join("\n");
        if (n.hole === "sorry") {
          expect(body, `${s.slug} ${n.id}`).toMatch(/\bsorry\b/);
          expect(s.build.sorryWarningLines.some((l) => n.lines![0] <= l && l <= n.lines![1]), `${s.slug} ${n.id} warned`).toBe(true);
        } else if (!n.hole) {
          expect(body, `${s.slug} ${n.id}`).not.toMatch(/\bsorry\b/);
        }
      }
      for (const n of s.nodes.filter((x) => x.origin === "specification")) expect(n.hole).toBeNull();
      // Every warning is inside a hole of the graph or listed as outside every shape.
      const inHole = (l: number) => s.nodes.some((n) => n.hole && n.origin === "candidate" && n.lines![0] <= l && l <= n.lines![1]);
      const outside = s.build.sorryOutsideShapes.map((h) => h.line);
      for (const l of warned) expect(inHole(l) !== outside.includes(l), `${s.slug} line ${l}`).toBe(true);
      // A sorry outside every shape is in a declaration of the candidate that no guarantee reaches.
      const ids = new Set(s.nodes.map((n) => n.id));
      for (const h of s.build.sorryOutsideShapes) {
        expect(h.declaration, `${s.slug} line ${h.line}`).toBeTruthy();
        expect(text(s.source.file).split("\n")[h.line - 1]).toMatch(new RegExp(`\\b${h.declaration.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`));
        expect(ids.has(h.declaration)).toBe(false);
      }
      expect(s.build.ok).toBe(true);
      expect(s.build.errorLines).toEqual([]);
    }
  });

  it("finds no hole in a verified repair and every guarantee of it complete", () => {
    const verified = shapes.filter((s) => s.role === "verified");
    expect(verified.map((s) => s.task.id).sort()).toEqual(["rc-knight-router", "rw-balancer-upscale", "rw-cetus-shlw", "rw-euler-donate", "rw-hundred-vault"]);
    for (const s of verified) {
      expect(s.passport!.status).toBe("VERIFIED");
      expect(Object.values(s.passport!.requirements).every((v) => v === "VERIFIED")).toBe(true);
      expect(s.holes).toEqual([]);
      expect(s.build.sorryWarningLines).toEqual([]);
      expect(s.guarantees.every((g) => g.complete)).toBe(true);
      expect(s.missing).toEqual([]);
    }
  });

  it("agrees with each attempt's own final check on which guarantees are complete", () => {
    const attempts = shapes.filter((s) => s.role === "attempt");
    expect(attempts.map((s) => s.slug).sort()).toEqual(["holes-balancer-A0-1", "holes-compound-A0-1", "holes-compound-A2-2", "holes-compound-A2-topdown-3"]);
    for (const s of attempts) {
      expect(s.run.finalStatus).not.toBeNull();
      for (const g of s.guarantees) expect(g.complete, `${s.slug} ${g.id}`).toBe(s.run.finalStatus![g.theorem.split(".").pop()!] === "PROVED");
      if (s.passport) for (const g of s.guarantees) expect(s.passport.requirements[g.id] === "VERIFIED").toBe(g.complete);
    }
  });

  it("matches the home page graph on the verified Balancer repair", () => {
    const s = bySlug.get("verified-balancer")!;
    expect(s.source).toEqual(PROOF_GRAPH.source);
    expect(s.passport!.sha256).toBe(PROOF_GRAPH.passport.sha256);
    const strip = (n: Node) => ({ id: n.id, kind: n.kind, origin: n.origin, file: n.file, lines: n.lines, depth: n.depth, ...(n.requirement ? { requirement: n.requirement } : {}) });
    expect(s.nodes.map(strip)).toEqual(PROOF_GRAPH.nodes);
    expect(s.edges).toEqual(PROOF_GRAPH.edges);
    expect(s.excluded).toEqual(PROOF_GRAPH.excluded);
  });

  it("recomputes the headline measurements of the summary", () => {
    const pick = (gs: Guarantee[], v: number, k: "depth" | "size") => gs.filter((g) => g[k] === v).map((g) => ({ id: g.id, depth: g.depth, size: g.size }));
    const verified = shapes.filter((s) => s.role === "verified");
    expect(summary.verified.map((v: { task: string }) => v.task).sort()).toEqual(verified.map((s) => s.task.id).sort());
    for (const v of summary.verified) {
      const s = verified.find((x) => x.task.id === v.task)!;
      const gs = s.guarantees;
      expect(v.file).toBe(`${DIR}/${s.slug}.json`);
      expect(v.passport).toBe(s.passport!.sha256);
      expect(v.guarantees).toBe(gs.length);
      expect(v.nodes).toBe(s.nodes.length);
      expect(v.deepest).toEqual(pick(gs, Math.max(...gs.map((g) => g.depth)), "depth"));
      expect(v.largest).toEqual(pick(gs, Math.max(...gs.map((g) => g.size)), "size"));
      expect(v.smallest).toEqual(pick(gs, Math.min(...gs.map((g) => g.size)), "size"));
      expect(v.lemmasInEveryShape).toEqual(s.loadBearing.every.filter((n) => n.kind === "lemma").map((n) => n.id));
      expect(v.declarationsInEveryShape).toBe(s.loadBearing.every.length);
      const top = Math.max(0, ...s.loadBearing.lemmas.map((l) => l.guarantees));
      expect(v.mostSharedLemmas.map((l: { id: string }) => l.id).sort()).toEqual(s.loadBearing.lemmas.filter((l) => l.guarantees === top).map((l) => l.id).sort());
    }
    const comp = shapes.filter((s) => s.role === "attempt" && s.task.id === "rw-compound-comp");
    expect(comp).toHaveLength(3);
    const inAll = (ls: string[][]) => ls.reduce((a, l) => a.filter((x) => l.includes(x)));
    expect(summary.compound.runs).toEqual(comp.map((s) => s.run.dir).sort((a, b) => summary.compound.runs.indexOf(a) - summary.compound.runs.indexOf(b)));
    expect([...summary.compound.holesInEveryRun].sort()).toEqual(inAll(comp.map((s) => s.holes.map((h) => h.id))).sort());
    expect([...summary.compound.guaranteesOpenInEveryRun].sort()).toEqual(inAll(comp.map((s) => s.guarantees.filter((g) => !g.complete).map((g) => g.id))).sort());
    expect(summary.compound.guaranteesCompleteInSomeRun).toEqual([...new Set(comp.flatMap((s) => s.guarantees.filter((g) => g.complete).map((g) => g.id)))].sort());
    for (const a of summary.attempts) {
      const s = shapes.find((x) => x.run.dir === a.run)!;
      expect(a.holes).toEqual(s.holes.map((h) => ({ id: h.id, kind: h.kind, guarantees: h.guarantees.length })));
      expect(a.holesOutsideShapes).toEqual(s.build.sorryOutsideShapes.map((h) => h.declaration));
      expect(a.complete).toEqual(s.guarantees.filter((g) => g.complete).map((g) => g.id));
      expect(a.open).toEqual(s.guarantees.filter((g) => !g.complete).map((g) => ({ id: g.id, hangsFrom: g.hangsFrom, size: g.size, proved: g.proved })));
    }
    expect(summary.noPassportBackedRepair.map((x: { task: string }) => x.task).sort()).toEqual(["payout-flagship", "rw-compound-comp"]);
  });
});
