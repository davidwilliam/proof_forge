// What the /results page draws: the task-by-arm grids of the E1 sets (generated/e1-tasks.json,
// written by scripts/e1-tasks.mjs from results/e1-*/e1.json), the sentence that leads each set
// and the figures of the page's top strip. Every count comes from the per-run records or from the
// summary GET /api/results serves; tests/results-view.test.ts pins both to the result files.

import data from "@/generated/e1-tasks.json";
import { formatUsd } from "./format";
import type { E1Summary, E2Aggregate } from "./results";

export interface E1Run {
  completed: boolean;
  judge: string | null;
  binary: string | null;
  stop: string | null;
  usdList: number | null;
  elapsedS: number | null;
}

export interface E1TaskSet {
  source: string;
  tasks: string[];
  family: Record<string, string>;
  runs: Record<string, Record<string, E1Run>>;
}

export const E1_TASKS = data as unknown as { sets: Record<string, E1TaskSet>; testTasks: { id: string; family: string }[] };

/** The arms of E1 (agents/, eval/e1.py). */
export const ARMS: Record<string, { name: string; detail: string }> = {
  A0: { name: "On its own", detail: "compile-and-retry: the model sees Lean's errors and the axiom audit only" },
  A1: { name: "ProofForge harness", detail: "behavior first, one dialog per proof obligation, snippet checks and property tests" },
  A2: { name: "Harness and planner", detail: "the ProofForge harness with Muse Wonder proposing helper lemmas" },
};
export const armName = (arm: string) => ARMS[arm]?.name ?? arm;
const ARM_PHRASE: Record<string, string> = { A1: "the ProofForge harness", A2: "the harness and planner" };

/** The model of each E1 set (results/<set>/config.json, field model) and how its dollars are priced. */
export const SET_MODEL: Record<string, { model: string; price: "list" | "gpu" }> = {
  "e1-test-1": { model: "Muse Spark 1.3", price: "list" },
  "e1-test-open-2": { model: "Muse Spark Open", price: "list" },
  "e1-test-open-2-rerun": { model: "Muse Spark Open", price: "list" },
  "e1-test-open-1": { model: "Muse Spark Open", price: "list" },
  "e1-test-glimmer-1": { model: "Muse Glimmer 30B", price: "gpu" },
  "e1-dev-2": { model: "Muse Spark 1.3", price: "list" },
  "e1-dev-1": { model: "Muse Spark 1.3", price: "list" },
};

/** Current sets in reading order: complete test sets first, then the incomplete one, then development. */
export const SET_ORDER = ["e1-test-1", "e1-test-open-2", "e1-test-open-1", "e1-test-glimmer-1", "e1-dev-2"];

/**
 * Runs ended by the GPU host's outage, counted in the summary as recorded
 * (results/e1-test-glimmer-1/README.md, "Runs affected by the outage").
 */
export const OUTAGE: Record<string, Record<string, string[]>> = {
  "e1-test-glimmer-1": {
    "permissions-grants-b1": ["A1"],
    "permissions-grants-b2": ["A1"],
    "permissions-grants-b3": ["A1"],
  },
};

export type CellState = "done" | "missed" | "outage" | "none";
export interface GridCell {
  state: CellState;
  run: E1Run | null;
}
export interface GridTask {
  id: string;
  family: string;
  /** "pf": an arm with ProofForge completed it and the model on its own did not; "alone": the reverse. */
  mark: "pf" | "alone" | null;
  cells: Record<string, GridCell>;
}
export interface GridFamily {
  family: string;
  tasks: GridTask[];
  counts: Record<string, { completed: number; n: number }>;
}
export interface E1Grid {
  arms: string[];
  families: GridFamily[];
  /** Tasks shown that the set never ran (an incomplete test set shows the whole frozen split). */
  notStarted: number;
  pfOnly: number;
  aloneOnly: number;
}

/** The task-by-arm grid of one E1 set, or null when the generated file does not have its runs. */
export function e1Grid(name: string, s: E1Summary): E1Grid | null {
  const set = E1_TASKS.sets[name];
  if (!set) return null;
  const arms = Object.keys(s.arms ?? {});
  const pfArms = arms.filter((a) => a !== "A0");
  const isTest = name.includes("-test-");
  const ids =
    isTest && set.tasks.length < E1_TASKS.testTasks.length
      ? E1_TASKS.testTasks.map((t) => t.id)
      : set.tasks;
  const famOf = (id: string) => set.family[id] ?? E1_TASKS.testTasks.find((t) => t.id === id)?.family ?? id.split("-")[0]!;
  const outage = OUTAGE[name] ?? {};
  const tasks: GridTask[] = ids.map((id) => {
    const runs = set.runs[id] ?? {};
    const cells: Record<string, GridCell> = {};
    for (const a of arms) {
      const run = runs[a] ?? null;
      cells[a] = { run, state: !run ? "none" : outage[id]?.includes(a) ? "outage" : run.completed ? "done" : "missed" };
    }
    const a0 = runs.A0;
    const pfDone = pfArms.some((a) => runs[a]?.completed);
    const pfMissed = pfArms.some((a) => runs[a] && !runs[a]!.completed);
    const mark = a0 && !a0.completed && pfDone ? "pf" : a0?.completed && pfMissed ? "alone" : null;
    return { id, family: famOf(id), mark, cells };
  });
  const families: GridFamily[] = [...new Set(tasks.map((t) => t.family))].map((family) => {
    const ft = tasks.filter((t) => t.family === family);
    const counts = Object.fromEntries(
      arms.map((a) => [a, { completed: ft.filter((t) => t.cells[a]!.run?.completed).length, n: ft.filter((t) => t.cells[a]!.run).length }]),
    );
    return { family, tasks: ft, counts };
  });
  return {
    arms,
    families,
    notStarted: tasks.filter((t) => arms.every((a) => !t.cells[a]!.run)).length,
    pfOnly: tasks.filter((t) => t.mark === "pf").length,
    aloneOnly: tasks.filter((t) => t.mark === "alone").length,
  };
}

/** Dollars per completed repair: the arm's total over its completed runs, as e1.md prints it. */
export function usdPerCompleted(a: { completed: number; usd_list_total?: number }): number | null {
  return a.completed && a.usd_list_total != null ? a.usd_list_total / a.completed : null;
}

const of = (a: { completed: number; n: number }) => (a.completed === a.n ? `all ${a.n}` : `${a.completed} of ${a.n}`);
const tasksWord = (n: number) => (n === 1 ? "1 task" : `${n} tasks`);

/** The sentence that opens an E1 set: what the arms with ProofForge completed, against the model on its own. */
export function e1Lead(name: string, s: E1Summary): string {
  const arms = s.arms ?? {};
  const model = SET_MODEL[name]?.model ?? "The model";
  const a0 = arms.A0;
  const pf = Object.entries(arms).filter(([a]) => a !== "A0");
  if (!a0 || !pf.length) return "";
  const pfText = pf.map(([a, v]) => `${of(v)} with ${ARM_PHRASE[a] ?? a} (${a})`).join(" and ");
  const parts = [`${model} completed ${pfText}, against ${a0.completed} of ${a0.n} on its own (A0).`];
  const disc = pf
    .map(([a]) => [a, s.pairs?.[`${a}-A0`]?.discordant] as const)
    .filter((x): x is readonly [string, { hi_only: number; lo_only: number }] => !!x[1]);
  if (disc.length) {
    parts.push(
      disc
        .map(([a, d], i) => `${i ? "" : "Paired by task, "}${a} completed ${tasksWord(d.hi_only)} that A0 did not, and A0 ${d.lo_only || "none"} that ${a} did not`)
        .join("; ") + ".",
    );
  }
  return parts.join(" ");
}

export interface Kpi {
  value: string;
  label: string;
  href: string;
}

/** The top strip: each current test set as on its own → with ProofForge, E2, and the cost per completed repair of e1-test-1. */
export function resultsKpis(e1: Record<string, E1Summary>, e2: { name: string; agg: E2Aggregate } | null): Kpi[] {
  const out: Kpi[] = [];
  const best = (s: E1Summary) =>
    Object.entries(s.arms ?? {})
      .filter(([a]) => a !== "A0")
      .sort(([, x], [, y]) => y.completed / Math.max(1, y.n) - x.completed / Math.max(1, x.n))[0];
  for (const name of SET_ORDER.filter((k) => k.includes("-test-") && e1[k])) {
    const s = e1[name]!;
    const a0 = s.arms?.A0;
    const b = best(s);
    if (!a0 || !b) continue;
    const [arm, v] = b;
    out.push({
      value: `${a0.completed} → ${v.completed}`,
      label:
        a0.n === v.n
          ? `${SET_MODEL[name]?.model ?? name}, ${v.n} frozen test tasks: completed on its own → with ProofForge (${arm})`
          : `${SET_MODEL[name]?.model ?? name}, ${a0.n} and ${v.n} scored test runs: completed on its own → with ProofForge (${arm})`,
      href: `#${name}`,
    });
  }
  if (e2) {
    const arm = (k: string) => e2.agg.arms.find((a) => a.arm === k)!;
    const o = arm("ordinary").falseAccept;
    const p = arm("proofforge").falseAccept;
    out.push({ value: `${o.count} → ${p.count}`, label: `of the ${p.of} seeded bad candidates of E2 accepted: ordinary checking → ProofForge`, href: `#${e2.name}` });
  }
  const t1 = e1["e1-test-1"];
  if (t1?.arms?.A0 && t1.arms.A1) {
    const x = usdPerCompleted(t1.arms.A0);
    const y = usdPerCompleted(t1.arms.A1);
    if (x != null && y != null) out.push({ value: `${formatUsd(x)} → ${formatUsd(y)}`, label: "Muse Spark 1.3, frozen test tasks: list cost per completed repair, on its own → with ProofForge (A1)", href: "#e1-cost" });
  }
  return out;
}
