import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  BASELINE_SOURCE,
  CETUS_HOTFIX,
  COMPARISON,
  COMPOUND,
  COST_PER_VERIFIED,
  COUNTEREXAMPLES,
  HACKATHON,
  LIBRARY,
  LIBRARY_COMPOUND,
  LIBRARY_RUN,
  META_TOOLING,
  OPEN_WEIGHTS,
  PLANNER,
  SPEC_STRENGTH,
  aloneRuns,
  plannerRuns,
  type Runs,
} from "../lib/contribution";
import { FLAGSHIPS, IMPLEMENTED_FLAGSHIPS } from "../lib/flagships";
import { ROOT, fileSha256, readExact, readPassport, readRunSummary } from "../scripts/lib/results.mjs";

const text = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");
const flatText = (rel: string) => text(rel).replace(/\s+/g, " ");

function checkRuns(task: string, r: Runs) {
  let accepted = 0;
  for (const run of r.runs) {
    const s = readRunSummary(`${run}/summary.json`);
    expect(s.task, run).toBe(task);
    expect(s.arm, run).toBe(r.arm);
    expect(s.model, run).toBe("muse-spark-1.3-contributor");
    if (r.arm !== "A0") expect(s.planner, run).toBe(r.arm === "A2" ? "muse-wonder-1.0" : "none");
    const pp = `${run}/passport.json`;
    const verified = existsSync(path.join(ROOT, pp)) && readPassport(pp).status === "VERIFIED";
    if (verified) {
      const p = readPassport(pp);
      expect(p.recomputedSha256, pp).toBe(p.sha256);
      expect(p.task, pp).toBe(task);
    }
    expect(s.acceptedInSession && verified, run).toBe(s.acceptedInSession);
    if (s.acceptedInSession) accepted++;
  }
  expect(accepted, `${task} ${r.arm} ${r.runs.join(", ")}`).toBe(r.accepted);
}

describe("Muse alone against Muse with ProofForge", () => {
  for (const row of COMPARISON) {
    it(row.key, () => {
      const task = JSON.parse(text(`realworld/tasks/${row.task}/task.json`));
      expect(task.requirements.length).toBe(row.requirements);
      expect(row.alone.arm).toBe("A0");
      expect(row.alone.runs.every((r) => r.startsWith(`${BASELINE_SOURCE}/${row.task}/`))).toBe(true);
      checkRuns(row.task, row.alone);
      for (const h of row.harness) {
        expect(h.arm).not.toBe("A0");
        checkRuns(row.task, h);
      }
      checkRuns(row.task, row.implement);
      if (row.library) {
        const lib = row.library;
        expect(lib.source).toBe(LIBRARY_RUN.source);
        const all = [lib.alone, lib.withLibrary, lib.topdown].filter((r): r is Runs => r !== null);
        for (const r of all) {
          expect(r.runs.every((x) => x.startsWith(`${LIBRARY_RUN.source}/${row.task}/`)), r.runs.join(", ")).toBe(true);
          checkRuns(row.task, r);
        }
        if (lib.alone) expect(lib.alone.arm).toBe("A0");
        const mode = (run: string) => readExact(`${run}/summary.json`) as { mode?: string; library?: { enabled?: boolean } };
        for (const [r, loop] of [[lib.withLibrary, "orchestrated"], [lib.topdown, "topdown"]] as const) {
          if (!r) continue;
          expect(r.arm).toBe("A2");
          for (const run of r.runs) {
            expect(mode(run).mode, run).toBe(loop);
            expect(mode(run).library?.enabled, run).toBe(true);
          }
        }
      }
      const f = FLAGSHIPS.find((x) => x.key === row.key);
      if (f) {
        expect(path.basename(f.task)).toBe(row.task);
        expect(row.harness.flatMap((h) => h.runs)).toContain(f.repair.run);
        const impl = IMPLEMENTED_FLAGSHIPS.find((i) => i.key === row.key)!;
        expect(row.implement.runs).toContain(impl.run);
      }
    });
  }

  it("every run of the baseline is in the table", () => {
    const listed = COMPARISON.flatMap((r) => r.alone.runs);
    const dirs = readdirSync(path.join(ROOT, BASELINE_SOURCE)).filter((d) => statSync(path.join(ROOT, BASELINE_SOURCE, d)).isDirectory());
    const all = dirs.flatMap((d) => readdirSync(path.join(ROOT, BASELINE_SOURCE, d)).map((r) => `${BASELINE_SOURCE}/${d}/${r}`));
    expect([...listed].sort()).toEqual(all.sort());
  });

  it("the baseline README states the same acceptances", () => {
    const readme = text(`${BASELINE_SOURCE}/README.md`);
    expect(readme).toContain("accepted in 2 of 2 attempts on Cetus, Euler and Hundred, 1 of 2 on Balancer and Knight, 0 of 2 on Compound");
  });

  it("every run of the library comparison is in the table, with the outcome its README states", () => {
    for (const row of COMPARISON) {
      if ((LIBRARY_RUN.tasks as readonly string[]).includes(row.task)) expect(row.library, `${row.key}: fill from ${LIBRARY_RUN.source}`).not.toBeNull();
      else expect(row.library, row.key).toBeNull();
    }
    const listed = COMPARISON.flatMap((r) => (r.library ? [r.library.alone, r.library.withLibrary, r.library.topdown] : [])).flatMap((r) => r?.runs ?? []);
    const dirs = readdirSync(path.join(ROOT, LIBRARY_RUN.source)).filter((d) => statSync(path.join(ROOT, LIBRARY_RUN.source, d)).isDirectory());
    const all = dirs.flatMap((d) => readdirSync(path.join(ROOT, LIBRARY_RUN.source, d)).map((r) => `${LIBRARY_RUN.source}/${d}/${r}`));
    expect([...listed].sort()).toEqual(all.sort());
    const readme = text(`${LIBRARY_RUN.source}/README.md`);
    for (const run of all) {
      const [task, id] = run.split("/").slice(-2);
      const line = readme.split("\n").find((l) => l.startsWith(`| ${task} | ${id} |`));
      expect(line, run).toBeDefined();
      expect(line, run).toContain(readRunSummary(`${run}/summary.json`).acceptedInSession ? "| VERIFIED |" : "| UNRESOLVED |");
    }
  });

  it("the library-1 Muse-alone Compound runs ran the full wall cap", () => {
    const row = COMPARISON.find((r) => r.key === "compound")!;
    for (const run of row.library!.alone!.runs) expect(readRunSummary(`${run}/summary.json`).seconds, run).toBeGreaterThanOrEqual(14400);
    for (const run of row.alone.runs) expect(readRunSummary(`${run}/summary.json`).seconds, run).toBeLessThan(14400);
  });

  it("how far the library runs got on Compound", () => {
    const lib = COMPARISON.find((r) => r.key === "compound")!.library!;
    const status = (run: string) => (readExact(`${run}/summary.json`) as { final_status: Record<string, string> }).final_status;
    const runs = [...lib.withLibrary.runs, ...lib.topdown!.runs];
    expect(Math.max(...runs.map((r) => Object.values(status(r)).filter((v) => v === "PROVED").length))).toBe(LIBRARY_COMPOUND.bestProved);
    expect(runs.filter((r) => LIBRARY_COMPOUND.bounds.some((b) => status(r)[b] === "PROVED")).length).toBe(LIBRARY_COMPOUND.runsProvingABound);
    const task = JSON.parse(text("realworld/tasks/rw-compound-comp/task.json")) as { requirements: [string, string][] };
    for (const b of LIBRARY_COMPOUND.bounds) expect(task.requirements.map((r) => r[1])).toContain(b);
  });

  it("no method has verified Compound; the build team's library proof is VERIFIED", () => {
    const row = COMPARISON.find((r) => r.key === "compound")!;
    expect(aloneRuns(row).accepted).toBe(0);
    expect(plannerRuns(row)!.accepted).toBe(0);
    expect(row.harness.every((h) => h.accepted === 0) && row.implement.accepted === 0).toBe(true);
    const p = readPassport(LIBRARY.compoundLivePassportFile);
    expect(p.sha256).toBe(LIBRARY.compoundLivePassport);
    expect(p.recomputedSha256).toBe(p.sha256);
    expect(p.status).toBe("VERIFIED");
    expect(p.task).toBe(row.task);
  });
});

/** One-sided Fisher exact p that the first group's success rate exceeds the second's. */
function fisherGreater(s1: number, n1: number, s2: number, n2: number) {
  const choose = (n: number, k: number) => {
    let r = 1;
    for (let i = 1; i <= k; i++) r = (r * (n - k + i)) / i;
    return r;
  };
  const k = s1 + s2;
  const total = choose(n1 + n2, k);
  let p = 0;
  for (let x = s1; x <= Math.min(n1, k); x++) p += (choose(n1, x) * choose(n2, k - x)) / total;
  return p;
}

describe("cost per verified run", () => {
  for (const c of COST_PER_VERIFIED)
    it(c.key, () => {
      const row = COMPARISON.find((r) => r.key === c.key)!;
      const arms = [
        [c.alone, aloneRuns(row)],
        [c.planner, plannerRuns(row)!],
      ] as const;
      for (const [figure, runs] of arms) {
        expect(runs.runs.length).toBe(figure.runs);
        expect(runs.accepted).toBe(figure.verified);
        const usd = runs.runs.reduce((n, r) => n + readRunSummary(`${r}/summary.json`).usdList, 0);
        expect(Math.round(usd * 100) / 100).toBe(figure.usdList);
        expect(Math.round((usd / figure.verified) * 100) / 100).toBe(figure.usdPerVerified);
      }
      const p = fisherGreater(c.planner.verified, c.planner.runs, c.alone.verified, c.alone.runs);
      expect(Math.round(p * 100) / 100).toBe(c.fisherOneSidedP);
      expect(c.planner.usdPerVerified).toBeLessThan(c.alone.usdPerVerified);
    });

  it("Balancer as library-1/README.md states it", () => {
    const c = COST_PER_VERIFIED.find((x) => x.key === "balancer")!;
    const readme = text(`${LIBRARY_RUN.source}/README.md`);
    expect(readme).toContain(`| Muse alone (A0) | ${c.alone.verified} of ${c.alone.runs} | ${c.alone.usdList.toFixed(2)} | ${c.alone.usdPerVerified.toFixed(2)} |`);
    expect(readme).toContain(`| ${c.planner.verified} of ${c.planner.runs} | ${c.planner.usdList.toFixed(2)} | ${c.planner.usdPerVerified.toFixed(2)} |`);
    expect(readme).toContain(`p = ${c.fisherOneSidedP}`);
  });
});

describe("specification strength", () => {
  it("totals", () => {
    const s = readExact(`${SPEC_STRENGTH.source}/summary.json`) as { tasks: unknown[] | Record<string, unknown>; total: Record<string, number> };
    expect(Object.keys(s.tasks).length).toBe(SPEC_STRENGTH.specifications);
    expect(s.total).toMatchObject({
      generated: SPEC_STRENGTH.mutants,
      compiled: SPEC_STRENGTH.compiled,
      killed: SPEC_STRENGTH.rejected,
      killed_kernel: SPEC_STRENGTH.kernelChecked,
      survived_differs: SPEC_STRENGTH.survivedDiffers,
      survived_same: SPEC_STRENGTH.survivedSame,
    });
    expect(SPEC_STRENGTH.compiled - SPEC_STRENGTH.rejected).toBe(SPEC_STRENGTH.survivedDiffers + SPEC_STRENGTH.survivedSame);
    expect(text(`${SPEC_STRENGTH.source}/README.md`)).toContain(`the ${SPEC_STRENGTH.specifications} runs cover all ${SPEC_STRENGTH.tasksCovered} tasks`);
    expect(existsSync(path.join(ROOT, SPEC_STRENGTH.doc))).toBe(true);
  });
});

describe("counterexamples", () => {
  const summary = readExact(COUNTEREXAMPLES.source) as {
    rows: { label: string; task: string; passport: string; refuted: string[]; counterexamples: { kernel_checked: boolean }[] }[];
  };

  it("totals", () => {
    expect(summary.rows.length).toBe(COUNTEREXAMPLES.candidates);
    expect(summary.rows.reduce((n, r) => n + r.refuted.length, 0)).toBe(COUNTEREXAMPLES.refuted);
    expect(summary.rows.reduce((n, r) => n + r.counterexamples.filter((c) => c.kernel_checked).length, 0)).toBe(COUNTEREXAMPLES.kernelChecked);
    expect(text("results/counterexamples-1/README.md")).toContain(`median ${COUNTEREXAMPLES.medianSeconds} s`);
  });

  for (const row of COMPARISON)
    it(row.key, () => {
      for (const r of row.refutations) {
        const s = summary.rows.find((x) => x.label === r.target)!;
        expect(s, r.target).toBeDefined();
        expect(s.task).toBe(row.task);
        expect(s.refuted.length).toBe(r.refuted);
        expect(s.counterexamples.filter((c) => c.kernel_checked).length).toBe(r.kernelChecked);
        const p = readPassport(s.passport);
        expect(p.recomputedSha256).toBe(p.sha256);
      }
    });

  it("the Cetus hotfix counterexample", () => {
    const p = readExact(CETUS_HOTFIX.passport);
    const c = p.counterexamples.find((x: { requirement: string }) => x.requirement === CETUS_HOTFIX.requirement);
    expect(c.kernel_checked).toBe(true);
    expect(c.kernels.length).toBe(CETUS_HOTFIX.kernels);
    expect(c.statement).toBe(CETUS_HOTFIX.statement);
    expect(String(c.input.n)).toBe(CETUS_HOTFIX.input);
    expect(BigInt(CETUS_HOTFIX.input)).toBe(2n ** 192n);
    expect(c.output).toEqual({ overflow: false, value: 0 });
  });
});

describe("open-weight models", () => {
  for (const o of OPEN_WEIGHTS)
    it(o.key, () => {
      const e = readExact(o.source) as {
        summary: { arms: Record<string, { completed: number; n: number }>; pairs: Record<string, { n: number; ci95_cluster: [number, number]; mcnemar_p: number }> };
        results: { task: string; arm: string; binary: string; completed: boolean }[];
      };
      expect(e.summary.arms.A0).toMatchObject(o.a0);
      expect(e.summary.arms.A1).toMatchObject(o.a1);
      const pair = e.summary.pairs["A1-A0"]!;
      expect(pair.n).toBe(o.paired);
      expect(pair.ci95_cluster.map((x) => Math.round(x * 1000) / 1000)).toEqual(o.ci95);
      expect(Math.round(pair.mcnemar_p * 100) / 100).toBe(o.mcnemarP);
      expect(e.results.filter((r) => r.arm === "A0" && r.binary === "PASS").length).toBe(o.binaryPass.a0);
      expect(e.results.filter((r) => r.arm === "A1" && r.binary === "PASS").length).toBe(o.binaryPass.a1);
      if (o.outage) {
        const out = new Set(o.outage.runs);
        const a1 = e.results.filter((r) => r.arm === "A1" && !out.has(`${r.task}/${r.arm}`));
        expect(a1.length).toBe(o.outage.a1N);
        expect(a1.filter((r) => r.completed).length).toBe(o.outage.a1Completed);
        expect(text(o.source.replace("e1.json", "README.md"))).toContain(`| A1 | ${o.outage.a1Completed}/${o.outage.a1N} |`);
      }
    });
});

describe("the Wonder planner", () => {
  it("Compound", () => {
    const p = PLANNER[0];
    const readme = text("results/compound-1/README.md");
    const row = (id: string) => readme.split("\n").find((l) => l.startsWith(`| \`${id}\` |`))!;
    expect(row("repair-A1-1")).toContain(`| ${p.a1[0]} of ${p.requirements} |`);
    expect(row("repair-A1-2")).toContain(`| ${p.a1[1]} of ${p.requirements} |`);
    expect(row("repair-A2-1")).toContain(`| ${p.a2[0]} of ${p.requirements} |`);
    expect(row("repair-A2-2")).toContain(`| ${p.a2[1]} of ${p.requirements} |`);
    expect(readme).toContain("No run proved all eight requirements");
  });
  it("Knight", () => {
    const p = PLANNER[1];
    const readme = text("results/knight-1/README.md");
    const row = (id: string) => readme.split("\n").find((l) => l.startsWith(`| ${id} |`))!;
    expect(row("A1-1")).toContain(`| ${p.a1[0]} of ${p.requirements} |`);
    expect(row("A1-2")).toContain(`| ${p.a1[1]} of ${p.requirements} |`);
    expect(row("A2-1")).toContain(`| ${p.a2[0]} of ${p.requirements} |`);
    expect(row("A2-2")).toContain(`| ${p.a2[1]} of ${p.requirements} | VERIFIED`);
  });
});

describe("ProofForgeFin", () => {
  it("the Compound fixture and the deployed judge's Passport", () => {
    expect(fileSha256(LIBRARY.compoundFixture)).toBe(LIBRARY.compoundFixtureSha256);
    expect(LIBRARY.compoundLivePassport).toMatch(/^[0-9a-f]{64}$/);
  });
});

it("hackathon dates are the ones ORIGIN.md states", () => {
  const origin = text("ORIGIN.md");
  expect(origin).toContain(`kickoff ${HACKATHON.firstCommit}`);
  expect(origin).toContain(`submissions due ${HACKATHON.submissionsDue}`);
  expect(origin).toContain(`Implementation started ${HACKATHON.firstCommit}`);
});

describe("the Meta models and tools", () => {
  const budget = text("agents/budget.py");
  const flat = (s: string) => s.replace(/\s+/g, " ");
  it("every path and experiment exists", () => {
    for (const m of META_TOOLING) {
      for (const p of m.paths) expect(existsSync(path.join(ROOT, p)), p).toBe(true);
      for (const e of m.experiments) expect(statSync(path.join(ROOT, e)).isDirectory(), e).toBe(true);
    }
  });
  it("every Muse Code run of the listed experiments ran the stated version with Muse Spark 1.3", () => {
    const mc = META_TOOLING.find((m) => m.key === "muse-code")!;
    const version = mc.name.replace(/^Muse Code /, "");
    let runs = 0;
    for (const e of mc.experiments) {
      const dirs = existsSync(path.join(ROOT, e, "runs")) ? [path.join(e, "runs")] : [e];
      for (const d of dirs)
        for (const task of readdirSync(path.join(ROOT, d)).filter((x) => statSync(path.join(ROOT, d, x)).isDirectory()))
          for (const run of readdirSync(path.join(ROOT, d, task))) {
            const f = path.join(d, task, run, "summary.json");
            if (!existsSync(path.join(ROOT, f))) continue;
            const s = readExact(f);
            if (!s.muse_code) continue;
            expect(s.muse_code, f).toMatch(new RegExp(`^Muse Code ${version.replace(/\./g, "\\.")} `));
            expect(s.model, f).toBe("muse-spark-1.3-contributor");
            runs++;
          }
    }
    expect(runs).toBeGreaterThan(50);
  });
  it("every model ID is priced in agents/budget.py", () => {
    for (const id of ["muse-spark-1.3-contributor", "muse-wonder-1.0", "meta-models/muse-spark-open-1026", "glimmer/muse-glimmer-30b"]) {
      expect(META_TOOLING.some((m) => m.id === id), id).toBe(true);
      expect(budget).toContain(`"${id}"`);
    }
  });
  it("the open-weight servings are the ones OPEN_WEIGHTS states", () => {
    expect(META_TOOLING.find((m) => m.key === "muse-glimmer")!.kind).toContain(OPEN_WEIGHTS.find((o) => o.key === "glimmer")!.serving);
    expect(OPEN_WEIGHTS.find((o) => o.key === "spark-open")!.serving).toContain("Baseten Model APIs");
    expect(flat(text("results/frontier-3/PREREGISTRATION.md"))).toContain(`${META_TOOLING[0].name}, \`MUSE_NO_AUTO_UPDATE=1\`, model \`muse-spark-1.3-contributor\``);
  });
});

describe("Compound Proposal 62", () => {
  const readme = flatText(COMPOUND.readme);
  it("the incident facts are the task README's", () => {
    expect(readme).toContain("280,000 COMP tokens");
    expect(readme).toContain("worth about $80 million");
    expect(readme).toContain("2021-09-29");
    for (const s of COMPOUND.loss.sources) expect(readme).toContain(s);
    expect(readme).toContain("about one COMP per token borrowed");
    expect(readme).toContain("changes `>` to `>=` on both lines");
    expect(readme).toContain(COMPOUND.property.text.replace(/^F/, "f").replace(/\.$/, ""));
    expect(existsSync(path.join(ROOT, COMPOUND.vulnerable.witness))).toBe(true);
    expect(readme).toContain("the port pays 18977306140567618322762");
  });
  it("the Passports of the port, the fix and the two verified Muse Code runs", () => {
    const port = readPassport(COMPOUND.vulnerable.passport);
    expect(port.recomputedSha256).toBe(port.sha256);
    expect(port.status).toBe("REFUTED");
    expect(Object.values(port.requirements).filter((s) => s === "REFUTED")).toHaveLength(5);
    const fix = readPassport(COMPOUND.fix.passport);
    expect(fix.status).toBe("VERIFIED");
    const f3 = flatText("results/frontier-3/README.md");
    for (const r of COMPOUND.museRepairs) {
      const p = readPassport(r.passport);
      expect(p.recomputedSha256, r.passport).toBe(p.sha256);
      expect(p.status, r.passport).toBe("VERIFIED");
      expect(p.task).toBe(COMPOUND.task);
      expect(f3).toContain(`| ${r.run} | VERIFIED | VERIFIED | 8 of 8 |`);
      expect(f3).toContain(`\`${p.sha256.slice(0, 16)}\``);
      const sol = readExact(r.passport).solution.files["final.lean"];
      expect(fileSha256(r.candidate), r.candidate).toBe(sol);
      expect(readExact(r.summary).model).toBe("muse-spark-1.3-contributor");
    }
  });
  it("the real-code comparison is the report's", () => {
    const c = flatText("results/compound-1/README.md");
    expect(c).toContain(`| Proposal 62 build identical to the Lean port, every operation | ${COMPOUND.realCode.sequences} of ${COMPOUND.realCode.sequences} sequences |`);
    for (const row of COMPOUND.realCode.rows) expect(c).toContain(`| ${row.code} build breaks a requirement | ${row.violating}`);
    expect(existsSync(path.join(ROOT, COMPOUND.realCode.report))).toBe(true);
  });
});
