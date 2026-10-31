import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  BASELINE_SOURCE,
  CETUS_HOTFIX,
  COMPARISON,
  COUNTEREXAMPLES,
  HACKATHON,
  LIBRARY,
  LIBRARY_RUN,
  OPEN_WEIGHTS,
  PLANNER,
  type Runs,
} from "../lib/contribution";
import { FLAGSHIPS, IMPLEMENTED_FLAGSHIPS } from "../lib/flagships";
import { ROOT, fileSha256, readExact, readPassport, readRunSummary } from "../scripts/lib/results.mjs";

const text = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");

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

  it("the library comparison is shown only once its results are committed", () => {
    const committed = existsSync(path.join(ROOT, LIBRARY_RUN.source));
    for (const row of COMPARISON) {
      if (!committed) expect(row.library, row.key).toBeNull();
      else if ((LIBRARY_RUN.tasks as readonly string[]).includes(row.task)) expect(row.library, `${row.key}: fill from ${LIBRARY_RUN.source}`).not.toBeNull();
    }
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
  function count(dir: string) {
    const files: string[] = [];
    const walk = (d: string) => {
      for (const n of readdirSync(d)) {
        const f = path.join(d, n);
        if (statSync(f).isDirectory()) walk(f);
        else if (n.endsWith(".lean")) files.push(f);
      }
    };
    walk(path.join(ROOT, "lib", dir));
    let theorems = 0;
    let definitions = 0;
    for (const f of files) {
      const src = readFileSync(f, "utf8").replace(/\/-[\s\S]*?-\//g, "").replace(/--[^\n]*/g, "");
      theorems += (src.match(/^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)*(?:theorem|lemma)\s/gm) ?? []).length;
      definitions += (src.match(/^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*(?:def|abbrev)\s/gm) ?? []).length;
    }
    return { files: files.length, theorems, definitions };
  }

  it("declaration counts", () => {
    expect(count("ProofForgeFin")).toEqual({ files: LIBRARY.files, theorems: LIBRARY.theorems, definitions: LIBRARY.definitions });
    expect(count("ProofForgeFinDemo").theorems).toBe(LIBRARY.demoTheorems);
  });

  it("the kernel check and the Compound fixture", () => {
    const readme = text("lib/README.md").replace(/\s+/g, " ");
    expect(readme).toContain(`all ${LIBRARY.constantsChecked.toLocaleString("en-US")} safe constants`);
    expect(readme).toContain(`accepts all ${LIBRARY.modulesReplayed} modules`);
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
