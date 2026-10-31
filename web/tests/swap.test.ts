import { createHash } from "node:crypto";
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  MEASURED,
  PRESETS,
  REQUIREMENTS,
  TASK,
  VERSIONS,
  batchFromFields,
  describeSwap,
  fieldsFromBatch,
  formatBig,
  formatPct,
  outcome,
  parseSwaps,
  parseWhole,
  pct,
  valueSeries,
  type SwapResultOut,
} from "../lib/swap";
import { ROOT, readPassport } from "../scripts/lib/results.mjs";

const text = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");
const sha256 = (rel: string) => createHash("sha256").update(readFileSync(path.join(ROOT, rel))).digest("hex");

/** Numbers to strings, as POST /api/swap returns them. */
const strings = (v: unknown): unknown =>
  typeof v === "number" ? String(v) : Array.isArray(v) ? v.map(strings) : v && typeof v === "object" ? Object.fromEntries(Object.entries(v).map(([k, x]) => [k, strings(x)])) : v;

describe("versions match the committed Passports and sources", () => {
  for (const v of VERSIONS) {
    it(v.key, () => {
      const p = readPassport(v.passport.path);
      expect(p.recomputedSha256).toBe(p.sha256);
      expect(p.sha256).toBe(v.passport.sha256);
      expect(p.status).toBe(v.verdict);
      expect(p.requirements).toEqual(v.passport.requirements);
      expect(p.task).toBe("rw-balancer-upscale");
      const files = JSON.parse(text(v.passport.path)).solution.files as Record<string, string>;
      expect(Object.values(files)).toContain(sha256(v.source));
      for (const c of v.counterexamples) expect(existsSync(path.join(ROOT, c.path)), c.path).toBe(true);
      // the code shown, without the added comment lines, is in the source, whitespace aside
      const flat = (x: string) => x.replace(/\s+/g, " ").trim();
      const shown = flat(v.code.filter((l) => !l.trim().startsWith("--")).join("\n"));
      expect(flat(text(v.source)), v.key).toContain(shown);
    });
  }

  it("the refuted versions list kernel-checked refutations in their Passports", () => {
    for (const v of VERSIONS.filter((x) => x.verdict === "REFUTED")) {
      const p = JSON.parse(text(v.passport.path));
      const refuted = Object.entries(v.passport.requirements).filter(([, s]) => s === "REFUTED").map(([id]) => id);
      const checked = (p.counterexamples as { requirement: string; kernel_checked: boolean; kernels: string[] }[]).filter((c) => c.kernel_checked);
      expect(checked.map((c) => c.requirement).sort()).toEqual(refuted.sort());
      expect(checked.every((c) => c.kernels.length === 6)).toBe(true);
      for (const id of refuted) expect(v.finding).toContain(id);
    }
  });

  it("the Muse repair's Passport is reproduced", () => {
    expect(text("results/balancer-1/repair-A2-1/verify.txt")).toMatch(/^reproduced$/m);
    expect(text("results/balancer-1/plus-one/verify.txt")).toMatch(/^reproduced$/m);
  });
});

describe("presets", () => {
  const witness = text(`${TASK}/witnesses/attack_batch.lean`);
  const lean = (name: string, end: string) =>
    [...witness.slice(witness.indexOf(name), witness.indexOf(end)).matchAll(/⟨\.givenOut, (\d), (\d), (\d+)⟩/g)].map((m) => ({
      kind: "out",
      in: Number(m[1]),
      out: Number(m[2]),
      amount: m[3],
    }));

  it("the attack presets are the witness file's batches", () => {
    const attack = PRESETS.find((p) => p.key === "attack")!;
    const chain = PRESETS.find((p) => p.key === "chain")!;
    expect(attack.batch.swaps).toEqual(lean("def batch", "theorem batch_runs"));
    expect(chain.batch.swaps).toEqual(lean("def attackSwaps", "def onChainAmountsIn"));
    expect(chain.batch.swaps).toHaveLength(90);
    expect(witness).toContain("stableMath 200000 2");
    expect(chain.batch.amp).toBe("200000");
    expect(text(`${TASK}/spec/BalancerSwap/Sanity.lean`)).toContain("1058132408689971699");
  });

  it("every preset passes the input checks and round-trips through the editor", () => {
    for (const p of PRESETS) {
      const back = batchFromFields(fieldsFromBatch(p.batch));
      expect(back.ok, p.key).toBe(true);
      if (back.ok) expect(back.value).toEqual(p.batch);
      expect(JSON.stringify(p.batch).length).toBeLessThan(20_000);
    }
  });
});

describe("input checks mirror the server", () => {
  it("whole numbers within limits", () => {
    expect(parseWhole("1,000", "x", 0n, 10n ** 30n)).toEqual({ ok: true, value: "1000" });
    expect(parseWhole("1e18", "x", 0n, 10n ** 30n).ok).toBe(false);
    expect(parseWhole("-1", "x", 0n, 10n).ok).toBe(false);
    expect(parseWhole("11", "x", 0n, 10n).ok).toBe(false);
    expect(parseWhole("0", "rate", 1n, 10n).ok).toBe(false);
  });

  it("swap lines", () => {
    expect(parseSwaps("out 0 1 17\n\n in 1 0 5 ")).toEqual({
      ok: true,
      value: [
        { kind: "out", in: 0, out: 1, amount: "17" },
        { kind: "in", in: 1, out: 0, amount: "5" },
      ],
    });
    expect(parseSwaps("").ok).toBe(false);
    expect(parseSwaps("out 0 0 1").ok).toBe(false);
    expect(parseSwaps("out 0 2 1").ok).toBe(false);
    expect(parseSwaps("swap 0 1 1").ok).toBe(false);
    expect(parseSwaps(Array(101).fill("out 0 1 1").join("\n")).ok).toBe(false);
    expect(parseSwaps(`out 0 1 1${"0".repeat(30)}1`).ok).toBe(false);
  });

  it("stable math needs an amplification within Balancer's range", () => {
    const f = fieldsFromBatch(PRESETS[1]!.batch);
    expect(batchFromFields({ ...f, amp: "0" }).ok).toBe(false);
    expect(batchFromFields({ ...f, amp: "5000001" }).ok).toBe(false);
    expect(batchFromFields({ ...f, math: "product" }).ok && !("amp" in (batchFromFields({ ...f, math: "product" }) as { value: object }).value)).toBe(true);
  });
});

describe("summaries", () => {
  // The deployed port on the four-round batch: the witness output recorded in its Passport.
  const port = JSON.parse(text("results/counterexamples-1/balancer-port/passport.json"));
  const w = port.requirements.find((r: { id: string }) => r.id === "REQ-BATCH-KEEPS-VALUE").witness;
  const result = strings(w.output) as SwapResultOut;

  it("the deployed code loses 93.74% of the pool's value on the attack batch", () => {
    expect(w.input.swaps).toEqual(PRESETS[0]!.batch.swaps.map((s) => ({ ...s, amount: Number(s.amount) })));
    const o = outcome(result);
    expect(o).toMatchObject({ ok: true, refusedAt: null, before: 4749898000n, after: 297229191n, ran: 12 });
    expect(o.changePct).toBeCloseTo(-93.74240, 4);
    expect(o.lowestPct).toBeCloseTo(6.25680, 4); // after swap 11
    const series = valueSeries(result, 12);
    expect(series[0]).toBe(100);
    expect(series[12]).toBeCloseTo(6.25758, 4);
  });

  it("a reverted batch keeps the starting value and marks the refused swap", () => {
    const reverted: SwapResultOut = {
      ok: false,
      value_before: "100",
      value_after: "100",
      balances_after: ["10", "10"],
      steps: [
        { quote: "5", ok: true, balances: ["15", "7"], value: "105" },
        { quote: null, ok: false, balances: ["15", "7"], value: "105" },
      ],
    };
    expect(outcome(reverted)).toMatchObject({ ok: false, refusedAt: 2, changePct: 0, lowestPct: 105, ran: 1 });
    expect(valueSeries(reverted, 3)).toEqual([100, 105, null, null]);
  });

  it("formatting", () => {
    expect(formatBig("4749898000")).toBe("4,749,898,000");
    expect(formatBig(-1234n)).toBe("-1,234");
    expect(formatPct(-93.7424, true)).toBe("-93.74%");
    expect(formatPct(0.0050, true)).toBe("+0.0050%");
    expect(formatPct(0.00000526, true)).toBe("+0.0000053%");
    expect(formatPct(0, true)).toBe("0.00%");
    expect(pct(1n, 3n)).toBe(33.33333333);
    expect(pct(-2n, 3n)).toBe(-66.66666666);
    expect(describeSwap({ kind: "out", in: 0, out: 1, amount: "17" }, ["WETH", "osETH"])).toBe("17 osETH out, paid in WETH");
    expect(describeSwap({ kind: "in", in: 1, out: 0, amount: "5000" }, ["WETH", "osETH"])).toBe("5,000 osETH in, for WETH");
  });
});

describe("measured comparison and requirements", () => {
  it("figures match results/library-1/README.md", () => {
    const readme = text(MEASURED.source);
    expect(readme).toContain(`| Muse alone (A0) | ${MEASURED.alone.verified} of ${MEASURED.alone.runs} | ${MEASURED.alone.usdTotal.toFixed(2)} | ${MEASURED.alone.usdPerVerified.toFixed(2)} |`);
    expect(readme).toContain(`| ${MEASURED.forge.verified} of ${MEASURED.forge.runs} | ${MEASURED.forge.usdTotal.toFixed(2)} | ${MEASURED.forge.usdPerVerified.toFixed(2)} |`);
    expect(readme).toContain(`p = ${MEASURED.fisherP}`);
    expect(readme).toContain(`$${MEASURED.capUsd} at standard list prices`);
    expect(readme).toContain("14,400 s of\nwall time");
  });

  it("the Muse-alone runs that did not verify proved no requirement", () => {
    for (const run of MEASURED.failedAlone) {
      const s = JSON.parse(text(`${run}/summary.json`));
      expect(s.arm).toBe("A0");
      expect(Object.values(s.final_status).every((x) => x === "SORRY")).toBe(true);
      const p = readPassport(`${run}/passport.json`);
      expect(p.recomputedSha256).toBe(p.sha256);
      expect(p.status).toBe("UNRESOLVED");
      expect(Object.values(p.requirements).every((x) => x === "UNRESOLVED")).toBe(true);
      expect(p.executableStatus).toBe("PASS");
      expect(p.propertyCases).toBe(MEASURED.failedAloneCases);
    }
  });

  it("requirement ids are the task's, in order", () => {
    const task = JSON.parse(text(`${TASK}/task.json`));
    expect(REQUIREMENTS.map((r) => r.id)).toEqual(task.requirements.map((r: [string, string]) => r[0]));
    const readme = text(`${TASK}/README.md`);
    for (const r of REQUIREMENTS) expect(readme).toContain(`| ${r.id} |`);
  });
});
