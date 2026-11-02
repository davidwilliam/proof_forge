import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { E2 } from "../lib/evidence";
import { HEADLINE_IDS, countsSentence, headlines, pValue, testPhrase, winDetail, type WinsData } from "../lib/wins";
import { WINS } from "../lib/wins-data";
import { ROOT } from "../scripts/lib/results.mjs";

// The ledger as eval/wins.py writes it; every figure on the site is pinned to this file.
interface LedgerArm {
  arm: string;
  runs: number;
  verified: number;
  list_usd_per_verified: number | null;
  cap_stops: { usd: number; wall: number };
  caps: { usd: number; wall_s: number }[];
}
interface LedgerComparison {
  id: string;
  model: string;
  scope: string;
  experiment: string;
  alone: LedgerArm;
  proofforge: LedgerArm;
  classification: Record<string, string>;
  factors: { cost?: number; time?: number };
  test: { name: string; p: number; preregistered?: boolean; significant_at_0_05?: boolean; secondary?: { name: string; p: number } } | null;
}
interface Ledger {
  comparisons: LedgerComparison[];
  catches: { id: string; bad_cases: number; good_cases: number; bad_accepted: Record<string, number>; good_rejected: Record<string, number> }[];
  wins: Record<string, { id: string; sentence: string }[]>;
  counts: WinsData["counts"];
}

const ledger = JSON.parse(readFileSync(path.join(ROOT, "results/wins/ledger.json"), "utf8")) as Ledger;
const lc = (id: string) => ledger.comparisons.find((c) => c.id === id)!;
const H = Object.fromEntries(headlines(WINS).map((h) => [h.key, h]));
const all = (h: { figure: string; figureAlt: string; text: string; note: string }) => `${h.figure} ${h.figureAlt} ${h.text} ${h.note}`;

describe("the frontier, measured: Meta's models on their own and with ProofForge", () => {
  it("generated/wins.json is up to date with results/wins/ledger.json", () => {
    expect(() => execFileSync(process.execPath, [path.join(ROOT, "web/scripts/wins.mjs"), "--check"], { stdio: "pipe" })).not.toThrow();
  });

  it("keeps every comparison and every win of the ledger", () => {
    expect(WINS.counts).toEqual(ledger.counts);
    expect(WINS.comparisons.map((c) => c.id)).toEqual(ledger.comparisons.map((c) => c.id));
    const groups = ["1_alone_did_not_verify_proofforge_did", "2_both_verified_proofforge_faster_or_cheaper", "3_other"];
    groups.forEach((g, i) => {
      const ours = WINS.wins.filter((w) => w.group === i + 1);
      expect(ours.map((w) => [w.id, w.sentence])).toEqual(ledger.wins[g]!.map((w) => [w.id, w.sentence]));
    });
    expect([1, 2, 3].map((g) => WINS.wins.filter((w) => w.group === g).length)).toEqual([
      ledger.counts.wins_group_1,
      ledger.counts.wins_group_2,
      ledger.counts.wins_group_3,
    ]);
    for (const c of WINS.comparisons) {
      const l = lc(c.id);
      expect([c.alone.verified, c.alone.runs, c.proofforge.verified, c.proofforge.runs], c.id).toEqual([l.alone.verified, l.alone.runs, l.proofforge.verified, l.proofforge.runs]);
      expect([c.alone.usdPerVerified, c.proofforge.usdPerVerified], c.id).toEqual([l.alone.list_usd_per_verified, l.proofforge.list_usd_per_verified]);
      expect(c.classification, c.id).toEqual(l.classification);
    }
  });

  it("OpenZeppelin sqrt leads: 10 of 10 with ProofForge, 0 of 10 on its own, preregistered", () => {
    const l = lc(HEADLINE_IDS.oz);
    expect([l.alone.verified, l.alone.runs, l.proofforge.verified, l.proofforge.runs]).toEqual([0, 10, 10, 10]);
    expect(l.proofforge.list_usd_per_verified).toBe(1.99);
    expect(l.test).toMatchObject({ preregistered: true, significant_at_0_05: true });
    expect(l.test!.p).toBeCloseTo(5.413e-6, 9);
    const first = lc(HEADLINE_IDS.ozFirst);
    expect([first.alone.verified, first.proofforge.verified]).toEqual([0, 0]);
    expect(headlines(WINS)[0]!.key).toBe("oz");
    expect(H.oz!.lead).toBe(true);
    expect([H.oz!.figure, H.oz!.figureAlt]).toEqual(["0 → 10", "of 10"]);
    for (const s of ["10 of 10 runs with ProofForge", "0 of 10 on its own", "$1.99 per verified run", "$95.45", "Preregistered one-sided Fisher exact p = 0.0000054",
      "a task no measured run had verified before", "Newton's integer square root", "256-bit words"])
      expect(all(H.oz!)).toContain(s);
  });

  it("Compound Proposal 62: the first verified repairs, 2 of 10 with ProofForge, 0 of 10 on its own and 0 of 20 pooled", () => {
    const l = lc(HEADLINE_IDS.compound);
    expect([l.alone.verified, l.alone.runs, l.proofforge.verified, l.proofforge.runs]).toEqual([0, 10, 2, 10]);
    expect(l.proofforge.list_usd_per_verified).toBe(42.72);
    expect(l.test).toMatchObject({ p: 0.2368, preregistered: true, significant_at_0_05: false });
    const pooled = lc(HEADLINE_IDS.compoundPooled);
    expect([pooled.alone.verified, pooled.alone.runs, pooled.test!.p]).toEqual([0, 20, 0.1034]);
    const c = WINS.comparisons.find((x) => x.id === HEADLINE_IDS.compound)!;
    expect([c.alone.reqMean, c.proofforge.reqMean]).toEqual([2.2, 4.5]);
    expect(WINS.comparisons.filter((x) => x.task === "rw-compound-comp" && x.id !== HEADLINE_IDS.compound && x.id !== HEADLINE_IDS.compoundPooled).every((x) => x.alone.verified + x.proofforge.verified === 0)).toBe(true);
  });

  it("Vyper CVE-2025-26622: both preregistered experiments, 10 of 15 on its own, 14 of 15 with ProofForge, 2.1x cheaper", () => {
    const l = lc(HEADLINE_IDS.vyper);
    expect([l.alone.verified, l.alone.runs, l.proofforge.verified, l.proofforge.runs]).toEqual([10, 15, 14, 15]);
    expect([l.alone.list_usd_per_verified, l.proofforge.list_usd_per_verified, l.factors.cost]).toEqual([11.79, 5.62, 2.1]);
    expect(l.test).toMatchObject({ p: 0.08429, preregistered: true, significant_at_0_05: false });
    const first = lc(HEADLINE_IDS.vyperFirst);
    expect([first.alone.verified, first.proofforge.verified, first.test!.p]).toEqual([2, 5, 0.08333]);
    const rep = lc(HEADLINE_IDS.vyperReplication);
    expect([rep.alone.verified, rep.alone.runs, rep.proofforge.verified, rep.proofforge.runs, rep.test!.p]).toEqual([8, 10, 9, 10, 0.5]);
    expect(rep.test!.secondary!.p).toBeCloseTo(0.0216, 4);
    const t = all(H.vyper!);
    expect([H.vyper!.figure, H.vyper!.figureAlt]).toEqual(["10 → 14", "of 15"]);
    for (const s of ["14 of 15", "10 of 15", "two preregistered experiments", "First experiment 5 of 5 with ProofForge against 2 of 5",
      "replication 9 of 10 against 8 of 10", "preregistered one-sided Mann-Whitney U p = 0.022", "2.1x cheaper", "$5.62", "$11.79",
      `${l.factors.time!.toFixed(1)}x faster`, "error bound of Newton's method", "CVE-2025-26622"])
      expect(t).toContain(s);
  });

  it("Balancer: 6.5x cheaper per verified run, planner stated", () => {
    const l = lc(HEADLINE_IDS.balancer);
    expect([l.alone.verified, l.alone.runs, l.proofforge.verified, l.proofforge.runs]).toEqual([2, 5, 3, 3]);
    expect([l.alone.list_usd_per_verified, l.proofforge.list_usd_per_verified, l.factors.cost]).toEqual([20.02, 3.06, 6.54]);
    expect(l.test).toMatchObject({ p: 0.1786, significant_at_0_05: false });
    expect(l.test!.preregistered).toBeFalsy();
    const t = all(H.balancer!);
    for (const s of ["6.5x", "3 of 3", "2 of 5", "$3.06", "$20.02", "Muse Wonder 1.0", "two Meta models working together"]) expect(t).toContain(s);
    expect(t).not.toContain("preregistered");
  });

  it("Muse Spark Open: six test tasks verified only with ProofForge, 24 of 30 against 21", () => {
    const six = ledger.wins["1_alone_did_not_verify_proofforge_did"]!.filter((w) => w.id.startsWith("e1-test-open-1/") && lc(w.id).scope === "task");
    expect(six).toHaveLength(6);
    for (const w of six) {
      const c = lc(w.id);
      expect(c.model).toBe("meta-models/muse-spark-open-1026");
      expect([c.alone.verified, c.proofforge.verified, c.alone.cap_stops.usd + c.alone.cap_stops.wall]).toEqual([0, 1, 1]);
    }
    const agg = lc(HEADLINE_IDS.openAll);
    expect([agg.alone.verified, agg.proofforge.verified, agg.alone.runs]).toEqual([21, 24, 30]);
    expect(agg.test).toMatchObject({ p: 0.5078, significant_at_0_05: false });
    const t = all(H.open!);
    for (const s of ["6 tasks", "of 30", "24 verified with ProofForge, 21 on its own", "$3 cap"])
      expect(t).toContain(s);
  });

  it("E2: 233 of 247 seeded bad candidates accepted by ordinary checking, 0 by ProofForge", () => {
    const e = ledger.catches[0]!;
    expect([e.bad_cases, e.bad_accepted.ordinary, e.bad_accepted.rebuild_and_tests, e.bad_accepted.proofforge, e.good_cases, e.good_rejected.proofforge]).toEqual([
      247, 233, 1, 0, 239, 0,
    ]);
    const arm = (k: string) => E2.arms.find((a) => a.key === k)!;
    expect([E2.bad, arm("ordinary").badAccepted, arm("proofforge").badAccepted]).toEqual([e.bad_cases, e.bad_accepted.ordinary, e.bad_accepted.proofforge]);
    const t = all(H.catches!);
    for (const s of ["0 of 247", "vs 233", "rejected 0 of 239", "seeded attacks of the E2 suite"]) expect(t).toContain(s);
  });

  it("states each test as the ledger does, with a direction only below 0.05", () => {
    for (const c of ledger.comparisons.filter((x) => x.test)) {
      const t = c.test!;
      const phrase = testPhrase(
        { name: t.name, p: t.p, preregistered: t.preregistered === true, significant: t.significant_at_0_05 === true, statedIn: "" },
        c.classification.verification as never,
      );
      expect(phrase.startsWith("preregistered "), c.id).toBe(t.preregistered === true);
      expect(phrase, c.id).not.toMatch(/significan/i);
      expect(phrase, c.id).toContain(`p = ${pValue(t.p)}`);
      expect(phrase.includes("in favour of"), c.id).toBe(t.significant_at_0_05 === true && c.classification.verification !== "tie");
      if (t.significant_at_0_05) expect(phrase, c.id).toContain(c.classification.verification === "loss" ? "in favour of the model on its own" : "in favour of ProofForge");
    }
    expect(pValue(0.08333)).toBe("0.083");
    expect(pValue(0.007812)).toBe("0.0078");
    expect(pValue(1)).toBe("1");
  });

  it("links every win to its full comparison and to committed reports", () => {
    const readme = readFileSync(path.join(ROOT, WINS.readme), "utf8");
    const anchors = new Set(
      [...readme.matchAll(/^#+ (.+)$/gm)].map((m) => m[1]!.toLowerCase().replace(/[^a-z0-9 -]/g, "").replace(/ /g, "-")),
    );
    for (const c of [...WINS.comparisons, WINS.catches]) {
      const [file, anchor] = c.links.comparison.split("#");
      expect(file).toBe(WINS.readme);
      expect(anchors.has(anchor!), `${c.id}: #${anchor}`).toBe(true);
      for (const r of c.links.reports) expect(existsSync(path.join(ROOT, r)), r).toBe(true);
    }
    for (const w of WINS.wins) expect(winDetail(WINS, w).startsWith("`")).toBe(false);
  });

  it("no headline claims significance or uses an em or en dash", () => {
    for (const h of headlines(WINS)) {
      expect(all(h), h.key).not.toMatch(/significan/i);
      expect(all(h), h.key).not.toMatch(/[—–]/);
    }
  });

  it("the root README states the headline wins as the ledger does", () => {
    const readme = readFileSync(path.join(ROOT, "README.md"), "utf8");
    const v = lc(HEADLINE_IDS.vyper);
    const b = lc(HEADLINE_IDS.balancer);
    expect(readme).toContain(countsSentence(WINS));
    for (const s of [
      `${v.alone.verified} of ${v.alone.runs} on its own`,
      `${v.proofforge.verified} of ${v.proofforge.runs} with ProofForge`,
      `$${v.proofforge.list_usd_per_verified} against $${v.alone.list_usd_per_verified}`,
      `$${b.proofforge.list_usd_per_verified!.toFixed(2)} against $${b.alone.list_usd_per_verified!.toFixed(2)}`,
      `${b.factors.cost!.toFixed(1)}x cheaper`,
      `${ledger.catches[0]!.bad_accepted.ordinary} of ${ledger.catches[0]!.bad_cases}`,
      "p = 0.022",
      "results/wins/README.md",
    ])
      expect(readme).toContain(s);
  });
});
