import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { COMPARISON, aloneRuns, plannerRuns } from "../lib/contribution";
import { FEATURED, FLAGSHIPS } from "../lib/flagships";
import {
  COMPOUND_FRONTIER,
  caseTrail,
  compoundFrontier,
  compoundLead,
  compoundTabLoss,
  compoundTrail,
  countsOf,
  homeKpis,
  homeStrips,
  lossParts,
  matrixRows,
} from "../lib/home-view";
import { HEADLINE_IDS, pValue } from "../lib/wins";
import { WINS } from "../lib/wins-data";
import { ROOT, readPassport } from "../scripts/lib/results.mjs";

type LedgerArm = { verified: number; runs: number; list_usd_per_verified: number | null };
const ledger = JSON.parse(readFileSync(path.join(ROOT, "results/wins/ledger.json"), "utf8")) as {
  counts: Record<string, number>;
  comparisons: { id: string; alone: LedgerArm; proofforge: LedgerArm; test: { p: number } | null }[];
};
const lc = (id: string) => ledger.comparisons.find((c) => c.id === id)!;
const readme4 = readFileSync(path.join(ROOT, COMPOUND_FRONTIER.readme), "utf8");

describe("Compound Proposal 62 in frontier-4", () => {
  it("8 of 10 with ProofForge, 0 of 10 on its own, 0 of 30 pooled with frontier-2 and frontier-3, as the ledger and the README state", () => {
    const l = lc(HEADLINE_IDS.compound);
    expect([l.alone.verified, l.alone.runs, l.proofforge.verified, l.proofforge.runs]).toEqual([0, 10, 8, 10]);
    const p = lc(HEADLINE_IDS.compoundPooled);
    expect([p.alone.verified, p.alone.runs]).toEqual([0, 30]);
    const f3 = lc(HEADLINE_IDS.compoundFirst);
    expect([f3.alone.verified, f3.proofforge.verified]).toEqual([0, 2]);
    const { f4, pooled } = compoundFrontier(WINS);
    expect([f4.proofforge.verified, f4.alone.verified, pooled.alone.runs]).toEqual([8, 0, 30]);
    const flat = readme4.replace(/\s+/g, " ");
    expect(flat).toContain("Muse Code with ProofForge verified 8 of 10 runs; on its own it verified 0 of 10");
    expect(flat).toContain(`one-sided Fisher exact test: p = ${pValue(f4.test!.p)}`);
    expect(flat).toContain(`one-sided Fisher exact p = ${pValue(pooled.test!.p)}`);
    expect(flat).toContain(`p = ${pValue(f4.test!.secondary!.p)}`);
  });

  it("names the eight verified runs of the README", () => {
    const verified = readme4.split("\n").filter((r) => /^\| proofforge-full-\d+ \| VERIFIED \|/.test(r)).map((r) => r.split("|")[1]!.trim());
    expect(verified).toEqual([...COMPOUND_FRONTIER.verifiedRuns]);
    expect(compoundLead(WINS)).toBe(
      "On Compound, Muse Code (Muse Spark 1.3) with ProofForge verified 8 of 10 runs in frontier-4; on its own it verified 0 of 10, and 0 of 30 with the runs on its own of frontier-2 and frontier-3 pooled. The first verified repairs of this task in any measured run came in frontier-3, 2 of 10 runs with ProofForge.",
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
    expect([s[0]!.figure, s[1]!.figure, s[2]!.figure]).toEqual(["0 → 10", "0 → 8", "10 → 14"]);
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
      const notMuseCode = <T extends { key: string }>(gs: T[]) => gs.filter((g) => !/^f[234]-/.test(g.key));
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

  it("leads the Compound row with frontier-4", () => {
    const c = rows.find((r) => r.key === "compound")!;
    expect(c.proofforge[0]).toMatchObject({ key: "f4-proofforge", verified: 8, runs: 10, lead: true });
    expect(c.proofforge[1]).toMatchObject({ key: "f3-proofforge", verified: 2, runs: 10 });
    expect(c.proofforge[2]).toMatchObject({ key: "f2-proofforge", verified: 0, runs: 10 });
    expect(c.alone.slice(0, 3).map((g) => [g.verified, g.runs])).toEqual([
      [0, 10],
      [0, 10],
      [0, 10],
    ]);
    expect(c.proofforge[0]!.detail).toContain(COMPOUND_FRONTIER.verifiedRuns.join(", "));
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

  it("trace Compound Proposal 62 from the refuted port to the verified runs and the fix", () => {
    const trail = compoundTrail(WINS);
    expect(trail.map((s) => s.key)).toEqual(["p62", "alone", "proofforge", "p64"]);
    expect(trail.map((s) => s.verdict)).toEqual(["REFUTED", "UNRESOLVED", "VERIFIED", "VERIFIED"]);
    expect(trail.map((s) => s.author)).toEqual(["upstream", "muse", "muse", "upstream"]);
    for (const s of trail) {
      expect(s.total, s.key).toBe(COMPARISON.find((r) => r.key === "compound")!.requirements);
      expect(s.counts.refuted + s.counts.verified + s.counts.unresolved, s.key).toBe(s.total);
      if (s.passport) expect(s.counts, s.key).toEqual(countsOf(readPassport(s.passport.path).requirements));
    }
    expect(trail[0]!.counts).toEqual({ refuted: 5, verified: 0, unresolved: 3 });
    // results/frontier-4/README.md: 0 of 10 on its own, 0 of 30 with frontier-2 and frontier-3 pooled, 8 of 10 with ProofForge
    expect(trail[1]!.passport).toBeNull();
    expect(trail[1]!.runs).toMatchObject({ verified: 0, runs: 30 });
    expect(trail[2]!.runs).toMatchObject({ verified: 8, runs: 10 });
    expect(trail[2]!.passports!.map((p) => p.label)).toEqual([...COMPOUND_FRONTIER.verifiedRuns]);
    expect(trail[2]!.passports!.map((p) => p.passport.sha256.slice(0, 16))).toEqual([
      "79450c41fd0ea77c",
      "56fe74dd5031aa23",
      "dd8943d482bd33d6",
      "de111c83c26b493c",
      "d073ccf63cb75abf",
      "459f18db9b68f18b",
      "a381e7a35f97d951",
      "ad5c81f6774ea354",
    ]);
  });

  it("gives the Compound tab the dollar figure of the README's loss, with the words that bound it", () => {
    expect(compoundTabLoss()).toEqual({ qualifier: "at worst about", figure: "$80 million" });
    expect(() => compoundTabLoss("$80 million")).toThrow();
  });

  it("links the Compound row of the comparison to its case", () => {
    const rows = matrixRows(WINS, FLAGSHIPS);
    expect(rows.find((r) => r.key === "compound")!.href).toBe("#case-compound");
    for (const r of rows) expect(r.href, r.key).toBe(`#case-${r.key}`);
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
