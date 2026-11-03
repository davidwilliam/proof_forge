import { execFileSync } from "node:child_process";
import { readFileSync, readdirSync, existsSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { formatUsd } from "../lib/format";
import { aggregateE2, type E1Summary, type E2Data } from "../lib/results";
import { E1_TASKS, OUTAGE, e1Grid, e1Lead, resultsKpis, usdPerCompleted } from "../lib/results-view";
import { ROOT } from "../scripts/lib/results.mjs";

// Every E1 set as GET /api/results serves it: the summary of results/<set>/e1.json.
const sets = readdirSync(path.join(ROOT, "results"))
  .filter((d) => d.startsWith("e1-") && existsSync(path.join(ROOT, "results", d, "e1.json")))
  .map((d) => [d, JSON.parse(readFileSync(path.join(ROOT, "results", d, "e1.json"), "utf8")).summary as E1Summary] as const);
const summary = Object.fromEntries(sets);

describe("the /results page figures", () => {
  it("reads an up-to-date generated/e1-tasks.json", () => {
    expect(() => execFileSync("node", ["scripts/e1-tasks.mjs", "--check"], { cwd: path.join(ROOT, "web"), stdio: "pipe" })).not.toThrow();
    expect(Object.keys(E1_TASKS.sets).sort()).toEqual(sets.map(([k]) => k).sort());
  });

  it("draws each grid with the summary's totals per arm and per family", () => {
    for (const [name, s] of sets) {
      const g = e1Grid(name, s)!;
      for (const [arm, a] of Object.entries(s.arms ?? {})) {
        const runs = g.families.flatMap((f) => f.tasks).filter((t) => t.cells[arm]!.run);
        expect([name, arm, runs.filter((t) => t.cells[arm]!.run!.completed).length, runs.length]).toEqual([name, arm, a.completed, a.n]);
      }
      for (const f of g.families.filter((f) => s.families?.[f.family])) {
        for (const [arm, c] of Object.entries(s.families![f.family]!)) expect([name, f.family, arm, f.counts[arm]]).toEqual([name, f.family, arm, c]);
      }
      // With one arm with ProofForge, the marks are the discordant pairs of the summary.
      const pf = Object.keys(s.arms ?? {}).filter((a) => a !== "A0");
      if (pf.length === 1) {
        const d = s.pairs?.[`${pf[0]}-A0`]?.discordant;
        expect([name, g.pfOnly, g.aloneOnly]).toEqual([name, d?.hi_only, d?.lo_only]);
      }
    }
  });

  it("shows the whole frozen split for the incomplete Glimmer set, and its outage runs as recorded", () => {
    const g = e1Grid("e1-test-glimmer-1", summary["e1-test-glimmer-1"]!)!;
    expect(g.families.flatMap((f) => f.tasks).length).toBe(30);
    expect(g.notStarted).toBe(14);
    for (const [task, arms] of Object.entries(OUTAGE["e1-test-glimmer-1"]!)) {
      for (const arm of arms) {
        const cell = g.families.flatMap((f) => f.tasks).find((t) => t.id === task)!.cells[arm]!;
        expect([task, cell.state, cell.run?.completed, cell.run?.stop]).toEqual([task, "outage", false, "usd"]);
      }
    }
  });

  it("prints the dollars per completed repair of each e1.md", () => {
    for (const [name, s] of sets) {
      const md = readFileSync(path.join(ROOT, "results", name, "e1.md"), "utf8");
      for (const [arm, a] of Object.entries(s.arms ?? {})) {
        const row = md.split("\n").find((l) => l.startsWith(`| ${arm} |`))!;
        const cell = row.split("|").map((c) => c.trim()).filter(Boolean).at(-1)!;
        const v = usdPerCompleted(a);
        expect([name, arm, v == null ? "n/a" : formatUsd(v)]).toEqual([name, arm, cell === "n/a" ? "n/a" : `$${cell}`]);
      }
    }
  });

  it("leads with the arms with ProofForge and keeps the top strip on the source figures", () => {
    expect(e1Lead("e1-test-1", summary["e1-test-1"]!)).toBe(
      "Muse Spark 1.3 completed all 30 with the ProofForge harness (A1) and all 30 with the harness and planner (A2), against 28 of 30 on its own (A0). Paired by task, A1 completed 2 tasks that A0 did not, and A0 none that A1 did not; A2 completed 2 tasks that A0 did not, and A0 none that A2 did not.",
    );
    expect(e1Lead("e1-test-open-1", summary["e1-test-open-1"]!)).toContain("A1 completed 6 tasks that A0 did not, and A0 3 that A1 did not");
    expect(e1Lead("e1-test-open-2", summary["e1-test-open-2"]!)).toContain("A1 completed 6 tasks that A0 did not, and A0 4 that A1 did not");
    const e2 = JSON.parse(readFileSync(path.join(ROOT, "results/e2-all-1/e2.json"), "utf8")) as E2Data;
    const kpis = resultsKpis(summary, { name: "e2-all-1", agg: aggregateE2(e2) });
    expect(kpis.map((k) => k.value)).toEqual(["28 → 30", "22 → 24", "21 → 24", "0 → 3", "233 → 0", "$0.87 → $0.61"]);
  });
});
