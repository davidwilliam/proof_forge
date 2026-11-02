import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { COMPARISON, aloneRuns, plannerRuns } from "../lib/contribution";
import { FEATURED, FLAGSHIPS } from "../lib/flagships";
import { COMPOUND_FRONTIER, caseTrail, compoundFrontier, compoundLead, countsOf, homeKpis, homeStrips, lossParts, matrixRows } from "../lib/home-view";
import { HEADLINE_IDS, pValue } from "../lib/wins";
import { WINS } from "../lib/wins-data";
import { ROOT, readPassport } from "../scripts/lib/results.mjs";

type LedgerArm = { verified: number; runs: number; list_usd_per_verified: number | null };
const ledger = JSON.parse(readFileSync(path.join(ROOT, "results/wins/ledger.json"), "utf8")) as {
  counts: Record<string, number>;
  comparisons: { id: string; alone: LedgerArm; proofforge: LedgerArm; test: { p: number } | null }[];
};
const lc = (id: string) => ledger.comparisons.find((c) => c.id === id)!;
const readme3 = readFileSync(path.join(ROOT, COMPOUND_FRONTIER.readme), "utf8");

describe("Compound Proposal 62 in frontier-3", () => {
  it("2 of 10 with ProofForge, 0 of 10 on its own, 0 of 20 pooled with frontier-2, as the ledger and the README state", () => {
    const l = lc(HEADLINE_IDS.compound);
    expect([l.alone.verified, l.alone.runs, l.proofforge.verified, l.proofforge.runs]).toEqual([0, 10, 2, 10]);
    const p = lc(HEADLINE_IDS.compoundPooled);
    expect([p.alone.verified, p.alone.runs]).toEqual([0, 20]);
    const f2 = lc("frontier-2/rw-compound-comp");
    expect([f2.alone.verified, f2.proofforge.verified]).toEqual([0, 0]);
    const { f3, pooled } = compoundFrontier(WINS);
    expect([f3.proofforge.verified, f3.alone.verified, pooled.alone.runs]).toEqual([2, 0, 20]);
    const flat = readme3.replace(/\s+/g, " ");
    expect(flat).toContain("Muse Code with ProofForge verified 2 of 10 runs; on its own it verified 0 of 10");
    expect(flat).toContain("These are the first verified repairs of this task in any measured run");
    expect(flat).toContain(`one-sided Fisher exact test: p = ${pValue(f3.test!.p)}`);
    expect(Number(pValue(pooled.test!.p))).toBe(0.1);
    expect(flat).toContain("one-sided Fisher exact p = 0.10");
  });

  it("names the two verified runs of the README", () => {
    const verified = readme3.split("\n").filter((r) => /^\| proofforge-full-\d+ \| VERIFIED \|/.test(r)).map((r) => r.split("|")[1]!.trim());
    expect(verified).toEqual([...COMPOUND_FRONTIER.verifiedRuns]);
    expect(compoundLead(WINS)).toBe(
      "On Compound, Muse Code (Muse Spark 1.3) with ProofForge verified 2 of 10 runs in frontier-3 (proofforge-full-5 and proofforge-full-9), the first verified repairs of this task in any measured run; on its own it verified 0 of 10, and 0 of 20 with the runs on its own of frontier-2 pooled.",
    );
  });
});

describe("the headline strips and the ledger's totals", () => {
  it("are the ledger's figures", () => {
    const k = homeKpis(WINS);
    expect(k.map((x) => x.value)).toEqual([
      ledger.counts.runs!.toLocaleString("en-US"),
      String(ledger.counts.comparisons),
      String(ledger.counts.wins_group_1),
      String(ledger.counts.wins_group_2),
      String(ledger.counts.wins_group_3),
    ]);
    const s = homeStrips(WINS);
    expect(s.map((x) => x.key)).toEqual(["oz", "compound", "vyper", "balancer", "open"]);
    const ids: Record<string, string> = { oz: HEADLINE_IDS.oz, compound: HEADLINE_IDS.compound, vyper: HEADLINE_IDS.vyper, balancer: HEADLINE_IDS.balancer, open: HEADLINE_IDS.openAll };
    for (const x of s) {
      const l = lc(ids[x.key]!);
      expect([x.alone.verified, x.alone.runs, x.proofforge.verified, x.proofforge.runs], x.key).toEqual([l.alone.verified, l.alone.runs, l.proofforge.verified, l.proofforge.runs]);
    }
    expect([s[0]!.figure, s[1]!.figure, s[2]!.figure]).toEqual(["0 → 10", "0 → 2", "10 → 14"]);
    const b = lc(HEADLINE_IDS.balancer);
    expect([b.proofforge.list_usd_per_verified, b.alone.list_usd_per_verified]).toEqual([3.06, 20.02]);
    expect(s[3]!.figure).toBe("$3.06");
    expect(s[3]!.figureAlt).toContain("$20.02");
  });
});

describe("the comparison matrix", () => {
  const rows = matrixRows(WINS, FLAGSHIPS);
  const sum = (gs: { verified: number; runs: number }[]) => gs.reduce((n, g) => ({ verified: n.verified + g.verified, runs: n.runs + g.runs }), { verified: 0, runs: 0 });

  it("draws every run of lib/contribution.ts once", () => {
    for (const row of COMPARISON) {
      const m = rows.find((r) => r.key === row.key)!;
      const notMuseCode = <T extends { key: string }>(gs: T[]) => gs.filter((g) => !/^f[23]-/.test(g.key));
      const a = aloneRuns(row);
      expect(sum(notMuseCode(m.alone)), row.key).toEqual({ verified: a.accepted, runs: a.runs.length });
      const planner = plannerRuns(row);
      const a1 = row.harness.filter((h) => h.arm === "A1");
      const expected = [...a1, ...(planner ? [planner] : [])];
      expect(sum(notMuseCode(m.proofforge)), row.key).toEqual({ verified: expected.reduce((n, r) => n + r.accepted, 0), runs: expected.reduce((n, r) => n + r.runs.length, 0) });
      expect(sum(m.spec)).toEqual({ verified: row.implement.accepted, runs: row.implement.runs.length });
      expect(m.refutations).toEqual(row.refutations.map((r) => ({ label: r.label, refuted: r.refuted, kernelChecked: r.kernelChecked })));
    }
  });

  it("leads the Compound row with frontier-3", () => {
    const c = rows.find((r) => r.key === "compound")!;
    expect(c.proofforge[0]).toMatchObject({ key: "f3-proofforge", verified: 2, runs: 10, lead: true });
    expect(c.proofforge[1]).toMatchObject({ key: "f2-proofforge", verified: 0, runs: 10 });
    expect(c.alone.slice(0, 2).map((g) => [g.verified, g.runs])).toEqual([
      [0, 10],
      [0, 10],
    ]);
    expect(c.proofforge[0]!.detail).toContain("proofforge-full-5 and proofforge-full-9");
    expect(rows.filter((r) => r.proofforge.some((g) => g.lead)).map((r) => r.key)).toEqual(["compound"]);
  });
});

describe("the incidents' verdict trails", () => {
  it("count each step's requirements from its Passport file", () => {
    for (const f of FLAGSHIPS) {
      const trail = caseTrail(f);
      expect(trail[trail.length - 1]!.verdict, f.key).toBe("VERIFIED");
      for (const s of trail) {
        expect(s.counts.refuted + s.counts.verified + s.counts.unresolved, `${f.key} ${s.key}`).toBe(s.total);
        if (s.passport) expect(s.counts, `${f.key} ${s.key}`).toEqual(countsOf(readPassport(s.passport.path).requirements));
      }
    }
    expect(caseTrail(FEATURED).map((s) => s.verdict)).toEqual(["REFUTED", "REFUTED", "VERIFIED", "VERIFIED"]);
    const hundred = caseTrail(FLAGSHIPS.find((f) => f.key === "hundred")!);
    expect(hundred[0]!.counts).toEqual({ refuted: 5, verified: 0, unresolved: 5 });
    const knight = caseTrail(FLAGSHIPS.find((f) => f.key === "knight")!);
    expect(knight.map((s) => s.verdict)).toEqual(["REFUTED", "UNRESOLVED", "UNRESOLVED", "UNRESOLVED", "VERIFIED"]);
    const knightFlagship = FLAGSHIPS.find((f) => f.key === "knight")!;
    expect(knight.slice(1, 4).map((s) => s.provedInSession)).toEqual(knightFlagship.unresolved.map((u) => u.proved));
  });

  it("splits a loss into its qualifier and figure without changing either", () => {
    expect(lossParts("about $223 million")).toEqual({ qualifier: "about", figure: "$223 million" });
    expect(lossParts("$460 million")).toEqual({ qualifier: "", figure: "$460 million" });
    for (const f of FLAGSHIPS) {
      const l = lossParts(f.loss.amount);
      expect(`${l.qualifier ? `${l.qualifier} ` : ""}${l.figure}`).toBe(f.loss.amount);
    }
  });
});
