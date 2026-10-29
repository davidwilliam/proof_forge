import { readdirSync, readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { BENCHMARK, FEATURED, FLAGSHIPS, type Flagship, type PassportRef } from "../lib/flagships";
import { ROOT, readExact, readPassport, readRunSummary } from "../scripts/lib/results.mjs";

const text = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");
const round = (x: number, places: number) => Math.round(x * 10 ** places) / 10 ** places;
const allPassports = (f: Flagship): PassportRef[] =>
  [f.vulnerable.passport, f.repair.passport, ...f.timeline.map((v) => v.passport)].filter((p): p is PassportRef => !!p);

describe("flagship Passports match the committed files", () => {
  for (const f of FLAGSHIPS) {
    it(f.key, () => {
      for (const ref of allPassports(f)) {
        const p = readPassport(ref.path);
        expect(p.recomputedSha256, `${ref.path} content hash`).toBe(p.sha256);
        expect(p.sha256, ref.path).toBe(ref.sha256);
        expect(p.status, ref.path).toBe(ref.status);
        expect(p.requirements, ref.path).toEqual(ref.requirements);
        expect(p.reproduce, ref.path).toBe(ref.reproduce);
        expect(p.task, ref.path).toBe(path.basename(f.task));
      }
      const r = readPassport(f.repair.passport.path);
      expect(Object.values(r.requirements).every((s) => s === "VERIFIED")).toBe(true);
      expect(r.kernels).toBe(f.repair.kernels);
      expect(r.propertyCases).toBe(f.repair.propertyCases);
      expect(r.executableStatus).toBe("PASS");
      if (f.vulnerable.passport) expect(readPassport(f.vulnerable.passport.path).executableStatus).toBe("REFUTED");
      expect(text(`${f.repair.run}/verify.txt`)).toMatch(/^reproduced$/m);
    });
  }
});

describe("flagship repair runs match summary.json", () => {
  for (const f of FLAGSHIPS) {
    it(f.key, () => {
      const s = readRunSummary(`${f.repair.run}/summary.json`);
      expect(s.task).toBe(path.basename(f.task));
      expect(s.arm).toBe(f.repair.arm);
      expect(s.model).toBe("muse-spark-1.3-contributor");
      expect(s.planner).toBe("none");
      expect(s.acceptedInSession).toBe(true);
      expect(Math.round(s.seconds)).toBe(f.repair.seconds);
      expect(s.calls).toBe(f.repair.calls);
      // Shown to two decimals, or three when the amount is under five cents.
      expect(round(s.usdList, 2)).toBe(f.repair.usdList);
      expect(round(s.usdCharged, s.usdCharged < 0.045 ? 3 : 2)).toBe(f.repair.usdCharged);
      expect(f.repair.attempt).toBe(Number(/repair-A1-(\d+)$/.exec(f.repair.run)![1]));
    });
  }
});

describe("loss figures are quoted from the task READMEs", () => {
  for (const f of FLAGSHIPS) {
    it(f.key, () => {
      const readme = text(`${f.task}/README.md`);
      const amount = f.loss.amount.replace(/^about /, "");
      const m = /^\$(\d+) million$/.exec(amount)!;
      expect(m, f.loss.amount).not.toBeNull();
      expect(f.loss.amount.startsWith("about ")).toBe(true);
      // The README states it as "about $223 million" or "about $197M".
      expect(readme.includes(`about ${amount}`) || readme.includes(`about $${m[1]}M`)).toBe(true);
      for (const c of f.loss.citations) expect(readme, c.url).toContain(c.url);
    });
  }
});

/** Incident-specific figures, recomputed from each real-code report. Every flagship needs one. */
const realCode: Record<string, (f: Flagship) => void> = {
  cetus(f) {
    const r = readExact(f.realCode.report);
    expect(r.cases).toBe(f.realCode.total);
    expect(r.documented_cases).toBe(7);
    expect(r.sui_version).toContain("1.83.0");
    const keys = ["original", "pr6", "pr7"];
    expect(f.realCode.rows.length).toBe(keys.length);
    f.realCode.rows.forEach((row, i) => {
      const v = r.versions[keys[i]!];
      expect(v.commit).toBe(row.commit);
      expect(v.outputs).toBe(f.realCode.total);
      expect(v.violating_cases).toBe(row.violating);
      expect(v.agrees_with_port).toBe(row.sameAsPort);
      expect(v.same_as_proved).toBe(row.sameAsProved);
    });
    expect(r.versions.pr6.by_requirement["REQ-SHLW-EXACT"]).toBe(32);
    expect(r.versions.original.witnesses[0].output.amount).toBe(1);
    expect(r.reference.candidate).toContain(f.repair.passport.sha256.slice(0, 16));
    expect(r.lean_confirmation).toMatchObject({ goals: f.realCode.confirmedInLean.goals, checked: f.realCode.confirmedInLean.checked });

    // Counterexamples on the timeline.
    const owed = /rounded up, is (\d+) units/.exec(r.versions.original.witnesses[0].message)![1]!;
    expect(f.vulnerable.finding).toContain(owed);
    const original = f.timeline.find((v) => v.key === "original")!;
    expect(original.finding).toContain(owed);
    const sci = Number(owed) / 10 ** (owed.length - 1);
    expect(original.finding).toContain(`about ${sci.toFixed(2)} × 10^${owed.length - 1}`);
    const pr6 = r.versions.pr6.witnesses.find((w: { input: { n?: bigint } }) => w.input.n === 2n ** 192n);
    expect(pr6.output).toEqual({ value: 0, overflow: false });

    // Merge times and the timeline's commits.
    const merged = (k: string) => /merged (\S+Z)/.exec(r.versions[k].note)![1]!;
    expect(merged("pr6")).toBe("2025-05-22T14:37:30Z");
    expect(merged("pr7")).toBe("2025-05-22T16:09:27Z");
    const minutes = (Date.parse(merged("pr7")) - Date.parse(merged("pr6"))) / 60000;
    expect(Math.round(minutes)).toBe(92);
    for (const v of f.timeline) {
      if (v.commit) expect(Object.values(r.versions).map((x) => (x as { commit: string }).commit)).toContain(v.commit);
      if (v.key === "pr6" || v.key === "pr7") {
        expect(v.merged).toBe(merged(v.key));
        expect(v.detail).toContain(merged(v.key).slice(11, 16));
      } else expect(v.merged).toBeNull();
    }
    const eq = f.equivalence!;
    expect(text(eq.file)).toContain(eq.theorem);
    const name = /^theorem (\S+)/.exec(eq.theorem)![1];
    expect(text(eq.output)).toContain(`'${name}' depends on axioms: [${eq.axioms}]`);
  },

  euler(f) {
    const r = readExact(f.realCode.report);
    const [plain, patched] = [r.versions.b1ee326, r.versions["b1ee326+checkLiquidity"]];
    for (const v of [plain, patched]) expect(v.sequences).toBe(f.realCode.total);
    const [a, b] = f.realCode.rows;
    expect([plain.commit, plain.violating_sequences, plain.same_as_proved]).toEqual([a!.commit, a!.violating, a!.sameAsProved]);
    expect(plain.euler_liquidity_violations).toBe(a!.violating);
    expect([patched.violating_sequences, patched.same_as_proved]).toEqual([b!.violating, b!.sameAsProved]);
    expect(r.proved.candidate).toContain(f.repair.passport.sha256.slice(0, 16));
    expect(r.lean_confirmation.goals).toBe(f.realCode.confirmedInLean.goals);
    expect(r.lean_confirmation.checked).toBe(true);
    expect(r.lean.kernel_refutation.checked).toBe(true);

    // The attack, from the binary check's witness on the port (whole DAI, exchange rate 1).
    const w = readExact(`${f.task}/validation.json`).checks.start.witness;
    const ops: [string, number, number, number | string][] = w.input.ops;
    const steps: { acct: [number, number][]; cash: number; reserves: number; r: number }[] = w.output.steps;
    const all = f.attack.map((s) => `${s.text} ${s.after ?? ""}`).join(" ");
    const n = (x: number) => x.toLocaleString("en-US");
    for (const [op, , amount] of ops) if (op !== "liquidate" && typeof amount === "number") expect(all).toContain(n(amount));
    const [e5, d5] = steps[4]!.acct[1]!;
    expect(f.attack[1]!.after).toContain(`collateral ${n(e5)}, debt ${n(d5)}`);
    const [e6, d6] = steps[5]!.acct[1]!;
    expect(f.attack[2]!.after).toContain(`collateral ${n(e6)}, debt ${n(d6)}`);
    expect(steps[6]!.r).toBe(256_000_000);
    expect(f.attack[3]!.text).toContain(n(steps[6]!.r));
    const [e7, d7] = steps[6]!.acct[1]!;
    expect(f.attack[3]!.after).toContain(`collateral ${n(e7)}, debt ${n(d7)}`);
    expect(steps[7]!.cash).toBe(0);
    expect(f.outcome).toContain(n(d7));
    // The unmodified contracts reach the same final state, in wei.
    const fin = plain.documented[0].final;
    expect(fin.acct[1]).toEqual([0, BigInt(d7) * 10n ** 18n]);
    expect(fin.cash).toBe(0);
  },

  hundred(f) {
    const r = readExact(f.realCode.report);
    const c = r.comparison;
    expect(c.cases).toBe(f.realCode.total);
    const [deployed, muse] = f.realCode.rows;
    expect([c.real_same_as_port, c.violating_cases, c.real_same_as_proved]).toEqual([deployed!.sameAsPort, deployed!.violating, deployed!.sameAsProved]);
    expect(c.real_differs_from_port).toEqual([]);
    expect(c.proved_violations).toBe(muse!.violating);
    expect(r.fork_block).toBe(90761917);
    expect(f.realCode.how).toContain(String(r.fork_block));
    expect(r.proved.candidate).toContain(f.repair.passport.sha256.slice(0, 16));
    expect(r.lean_confirmation).toMatchObject(f.realCode.confirmedInLean);
    expect(r.port.kernel_refutation_checked).toBe(true);
    expect(r.port.kernel_refutation).toBe(f.vulnerable.witness);

    // The vulnerable port has no Passport; validate_task.py rejects it and refutes its binary.
    const start = readExact(`${f.task}/validation.json`).checks.start;
    expect(f.vulnerable.passport).toBeNull();
    expect([start.judge, start.binary]).toEqual(["REJECT", "REFUTED"]);

    // The attack on the deployed contract, and the Muse repair on the same operations.
    const w = c.witnesses.find((x: { documented: boolean }) => x.documented);
    const n = (x: number) => x.toLocaleString("en-US");
    const all = f.attack.map((s) => `${s.text} ${s.after ?? ""}`).join(" ");
    for (const op of w.input.ops) expect(all).toContain(n(op.amount ?? op.shares));
    const real = w.real_steps;
    expect(real[0].supply).toBe(20_000_000_000);
    expect(f.attack[1]!.after).toContain(n(real[0].supply));
    expect([real[1].supply, real[1].assets]).toEqual([2, 1]);
    expect(real[2].assets).toBe(50_030_063_817);
    expect(f.attack[3]!.after).toContain(n(real[2].assets));
    expect([real[3].supply, real[3].assets]).toEqual([1, 2]);
    expect(w.proved_steps[3].supply).toBe(0);
    expect(w.message).toContain("1.99999999992");
    expect(f.attack[4]!.text).toContain("1.99999999992");
  },
};

describe("real-code comparisons and attacks match the reports", () => {
  it("every number in a scoreboard result is a reported figure", () => {
    for (const f of FLAGSHIPS) {
      const known = new Set([f.realCode.total, f.realCode.rows.length, ...f.realCode.rows.flatMap((r) => [r.violating, r.sameAsPort, r.sameAsProved])]);
      const shown = (`${f.realCode.short} ${f.realCode.result}`.match(/\d[\d,]*/g) ?? []).map((x) => Number(x.replace(/,/g, "")));
      for (const x of shown) expect(known.has(x), `${f.key}: ${x}`).toBe(true);
      expect(f.realCode.result).toMatch(new RegExp(`\\b${f.realCode.rows[0]!.violating}\\b`));
    }
  });
  it("every flagship has a check", () => expect(Object.keys(realCode).sort()).toEqual(FLAGSHIPS.map((f) => f.key).sort()));
  for (const f of FLAGSHIPS) it(f.key, () => realCode[f.key]!(f));
  it("the featured incident has a timeline ending in the Muse repair", () => {
    expect(FEATURED.timeline.at(-1)!.passport.sha256).toBe(FEATURED.repair.passport.sha256);
  });
});

describe("benchmark breadth", () => {
  it("counts tasks by family and split", () => {
    const dirs = readdirSync(path.join(ROOT, "tasks"), { withFileTypes: true }).filter((d) => d.isDirectory());
    const tasks = [...dirs.map((d) => readExact(`tasks/${d.name}/task.json`)), readExact("formal/task.json")];
    expect(tasks.length).toBe(BENCHMARK.tasks);
    for (const fam of BENCHMARK.families) expect(tasks.filter((t) => t.family === fam.key).length, fam.key).toBe(fam.tasks);
    expect(BENCHMARK.families.reduce((n, x) => n + x.tasks, 0)).toBe(BENCHMARK.tasks);
    for (const [split, count] of Object.entries(BENCHMARK.splits)) expect(tasks.filter((t) => t.split === split).length, split).toBe(count);
  });
});
