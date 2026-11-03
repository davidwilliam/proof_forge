// The home page's figures below the hero, as views of the data the rest of the site reads: the wins
// ledger (generated/wins.json), the Muse comparison of lib/contribution.ts, the flagships of
// lib/flagships.ts and the library counts of generated/library.json. Nothing here is typed in by
// hand except the names of the two verified frontier-3 runs, which tests/home-view.test.ts pins to
// results/frontier-3/README.md along with every figure below, and the few words that describe each
// version of the Compound code in its case.

import type { Kpi, Strip } from "@/components/FrontierViz";
import { COMPARISON, COMPOUND, COMPOUND_CASE, aloneRuns, plannerRuns, type ComparisonRow, type Runs } from "@/lib/contribution";
import { githubFile, type Flagship, type PassportRef, type Verdict } from "@/lib/flagships";
import { HEADLINE_IDS, comparison, factor1, fmtInt, headlines, modelName, pValue, runsOf, usd, type Headline, type WinsData } from "@/lib/wins";

const reportLabel = (p: string) => p.replace(/^results\//, "").replace(/\/(README|e1|e2)\.md$/, "");
const hrefs = (h: Headline) => h.links.map((l) => ({ label: l.label, href: githubFile(l.path) }));

/** The ledger's totals, each linking to its part of /frontier. */
export function homeKpis(d: WinsData): Kpi[] {
  const c = d.counts;
  return [
    { value: fmtInt(c.runs), label: "measured runs", href: "/frontier#every-comparison" },
    { value: String(c.comparisons), label: "comparisons, same model and caps", href: "/frontier#every-comparison" },
    { value: String(c.wins_group_1), label: "verified only with ProofForge", href: "/frontier#group-1" },
    { value: String(c.wins_group_2), label: "verified either way, cheaper or faster with ProofForge", href: "/frontier#group-2" },
    { value: String(c.wins_group_3), label: "gains of other kinds", href: "/frontier#group-3" },
  ];
}

/** frontier-3 on Compound Proposal 62: Muse Code (Muse Spark 1.3) on its own and with ProofForge. */
export const COMPOUND_FRONTIER = {
  readme: "results/frontier-3/README.md",
  earlier: "results/frontier-2/README.md",
  gaps: "results/library-compound-gaps-1/README.md",
  // results/frontier-3/README.md, "Every run": the two runs whose Passport is VERIFIED
  verifiedRuns: ["proofforge-full-5", "proofforge-full-9"],
} as const;

export function compoundFrontier(d: WinsData) {
  const f3 = comparison(d, HEADLINE_IDS.compound);
  const pooled = comparison(d, HEADLINE_IDS.compoundPooled);
  const f2 = comparison(d, "frontier-2/rw-compound-comp");
  return { f3, f2, pooled, model: modelName(f3.model) };
}

/** The sentence every Compound passage of the home page leads with. */
export function compoundLead(d: WinsData): string {
  const { f3, pooled, model } = compoundFrontier(d);
  return `On Compound, Muse Code (${model}) with ProofForge verified ${runsOf(f3.proofforge)} runs in frontier-3 (${COMPOUND_FRONTIER.verifiedRuns.join(" and ")}), the first verified repairs of this task in any measured run; on its own it verified ${runsOf(f3.alone)}, and ${runsOf(pooled.alone)} with the runs on its own of frontier-2 pooled.`;
}

/** Compound Proposal 62 from frontier-3, as /frontier shows it. */
function compoundStrip(d: WinsData): Strip {
  const { f3: c, f2, pooled } = compoundFrontier(d);
  return {
    key: "compound",
    title: "Compound Proposal 62",
    context: `COMP reward distribution, a task no measured run of any arm had verified before. ${modelName(c.model)} in Muse Code.`,
    unit: "run",
    alone: c.alone,
    proofforge: c.proofforge,
    figure: `${c.alone.verified} → ${c.proofforge.verified}`,
    figureAlt: "runs verified",
    stats: [
      { value: `${c.alone.reqMean} → ${c.proofforge.reqMean}`, label: `requirements of ${c.proofforge.reqTotal} proved per run` },
      { value: `${runsOf(pooled.alone)}`, label: "verified on its own, frontier-2 and frontier-3 pooled" },
      { value: `${c.alone.capStops} to ${c.proofforge.capStops}`, label: "runs stopped by a cap" },
    ],
    text: `Compound Proposal 62, the COMP reward distribution: ${modelName(c.model)} in Muse Code verified ${runsOf(c.proofforge)} runs with ProofForge, at ${usd(c.proofforge.usdPerVerified)} per verified run, and ${runsOf(c.alone)} on its own after spending ${usd(c.alone.usdTotal)}. Both verified runs prove the three bounds over any sequence of operations (rewards, each account, no backdated rewards) that no earlier run of either arm proved.`,
    note: `Preregistered one-sided ${c.test!.name.replace(/^one-sided /, "")} p = ${pValue(c.test!.p)}; with the runs on its own of frontier-2 pooled, ${runsOf(c.proofforge)} against ${runsOf(pooled.alone)}, p = ${pValue(pooled.test!.p)}. ProofForgeFin now supplies Accumulator.Market, two-sided reward markets bounded from one case analysis, written after the frontier-2 runs stopped at 5 of 8 requirements (${runsOf(f2.proofforge)} and ${runsOf(f2.alone)} verified). Caps of $${c.alone.caps[0]!.usd} and ${c.alone.caps[0]!.seconds / 3600} hours per run, list prices.`,
    links: [
      { label: "Full comparison", href: githubFile(c.links.comparison) },
      ...[...new Set([...c.links.reports, ...f2.links.reports])].map((p) => ({ label: reportLabel(p), href: githubFile(p) })),
    ],
  };
}

/** The headline gains as run strips, the same five /frontier leads with; each keeps its card's sentence and conditions. */
export function homeStrips(d: WinsData): Strip[] {
  const hs = new Map(headlines(d).map((h) => [h.key, h]));
  const h = (k: string) => hs.get(k)!;
  const oz = comparison(d, HEADLINE_IDS.oz);
  const v = comparison(d, HEADLINE_IDS.vyper);
  const b = comparison(d, HEADLINE_IDS.balancer);
  const open = comparison(d, HEADLINE_IDS.openAll);
  const common = (k: string) => ({ key: k, figure: h(k).figure, text: h(k).text, note: h(k).note, links: hrefs(h(k)) });
  return [
    {
      ...common("oz"),
      title: "OpenZeppelin Math.sqrt",
      context: `Behind the Aerodrome first deposit, a task no measured run had verified before. ${modelName(oz.model)} in Muse Code.`,
      unit: "run",
      alone: oz.alone,
      proofforge: oz.proofforge,
      figureAlt: "runs verified",
      stats: [
        { value: usd(oz.proofforge.usdPerVerified), label: "per verified run with ProofForge" },
        { value: usd(oz.alone.usdTotal), label: "spent on its own, nothing verified" },
        { value: `p = ${pValue(oz.test!.p)}`, label: "preregistered one-sided Fisher exact" },
      ],
    },
    compoundStrip(d),
    {
      ...common("vyper"),
      title: "Vyper sqrt(), CVE-2025-26622",
      context: `Two preregistered experiments, pooled. ${modelName(v.model)} in Muse Code.`,
      unit: "run",
      alone: v.alone,
      proofforge: v.proofforge,
      figureAlt: "runs verified",
      stats: [
        { value: factor1(v.factors.cost!), label: `cheaper per verified run, ${usd(v.proofforge.usdPerVerified)} against ${usd(v.alone.usdPerVerified)}` },
        { value: factor1(v.factors.time!), label: "faster" },
        { value: `${v.alone.capStops} to ${v.proofforge.capStops}`, label: "runs stopped by a cap" },
      ],
    },
    {
      ...common("balancer"),
      title: "Balancer V2 rounding repair",
      context: `Muse Wonder 1.0 plans the lemmas and ${modelName(b.model)} proves them, on one budget.`,
      unit: "run",
      alone: b.alone,
      proofforge: b.proofforge,
      figure: `${usd(b.proofforge.usdPerVerified)}`,
      figureAlt: `per verified run, against ${usd(b.alone.usdPerVerified)} on its own`,
      stats: [
        { value: `${b.alone.verified} → ${b.proofforge.verified}`, label: `verified, of ${b.alone.runs} and ${b.proofforge.runs} runs` },
        { value: factor1(b.factors.cost!), label: "cheaper per verified run" },
        { value: factor1(b.factors.time!), label: "faster" },
      ],
    },
    {
      ...common("open"),
      title: `${modelName(open.model)}, Meta's open-weight model`,
      context: "The frozen E1 test tasks, one run per arm per task.",
      unit: "task",
      alone: open.alone,
      proofforge: open.proofforge,
      figureAlt: "verified only with ProofForge",
      stats: [
        { value: `${open.alone.verified} → ${open.proofforge.verified}`, label: `of ${open.alone.runs} tasks verified` },
        { value: factor1(open.factors.cost!), label: `cheaper per verified task, ${usd(open.proofforge.usdPerVerified)} against ${usd(open.alone.usdPerVerified)}` },
        { value: `${open.alone.capStops} to ${open.proofforge.capStops}`, label: "runs stopped by a cap" },
      ],
    },
  ];
}

/* The six real failures as a matrix: one group of dots per set of runs, filled when verified. */

export interface DotGroup {
  key: string;
  /** What the runs are, in a few words, under the dots. */
  label: string;
  verified: number;
  runs: number;
  /** The readout: what was run and where its records are. */
  detail: string;
  /** The frontier-3 result on Compound, drawn first and marked. */
  lead?: boolean;
}

export interface MatrixRow {
  key: string;
  incident: string;
  year: number;
  /** Anchor of the case on this page, when the failure has one. */
  href: string | null;
  loss: string;
  requirements: number;
  alone: DotGroup[];
  proofforge: DotGroup[];
  spec: DotGroup[];
  refutations: { label: string; refuted: number; kernelChecked: number }[];
}

const runList = (r: Runs) => r.runs.join(", ");
const group = (key: string, label: string, r: Runs, what: string): DotGroup => ({
  key,
  label,
  verified: r.accepted,
  runs: r.runs.length,
  detail: `${what}: ${r.accepted} of ${r.runs.length} ${r.runs.length === 1 ? "run" : "runs"} accepted. ${runList(r)}`,
});

const ARM_WHAT = {
  A0: "Muse Spark 1.3 alone, compile-and-retry with Lean's errors and the axiom audit",
  A1: "Muse Spark 1.3 with the ProofForge harness",
  A2: "Muse Spark 1.3 with the ProofForge harness and Muse Wonder 1.0 as lemma planner",
} as const;

function museCodeGroups(d: WinsData, side: "alone" | "proofforge"): DotGroup[] {
  const { f3, f2, pooled, model } = compoundFrontier(d);
  const who = side === "alone" ? `Muse Code (${model}) on its own` : `Muse Code (${model}) with ProofForge, the skill and ProofForgeFin`;
  const verifiedNote =
    side === "proofforge" ? ` Verified: ${COMPOUND_FRONTIER.verifiedRuns.join(" and ")}, both proving the three sequence bounds no earlier run proved.` : ` With frontier-2 pooled: ${runsOf(pooled.alone)}.`;
  return [
    {
      key: `f3-${side}`,
      label: side === "alone" ? "Muse Code, frontier-3" : "Muse Code with ProofForge, frontier-3",
      verified: f3[side].verified,
      runs: f3[side].runs,
      detail: `${who}, frontier-3 (preregistered, caps of $${f3[side].caps[0]!.usd} and ${f3[side].caps[0]!.seconds / 3600} hours): ${runsOf(f3[side])} runs verified.${verifiedNote} ${COMPOUND_FRONTIER.readme}`,
      lead: side === "proofforge",
    },
    {
      key: `f2-${side}`,
      label: side === "alone" ? "Muse Code, frontier-2" : "Muse Code with ProofForge, frontier-2",
      verified: f2[side].verified,
      runs: f2[side].runs,
      detail: `${who}, frontier-2, before ProofForgeFin.Accumulator.Market: ${runsOf(f2[side])} runs verified, ${f2[side].reqMean} of ${f2[side].reqTotal} requirements proved per run on average. ${COMPOUND_FRONTIER.earlier}`,
    },
  ];
}

export function matrixRows(d: WinsData, flagships: readonly Flagship[], rows: readonly ComparisonRow[] = COMPARISON): MatrixRow[] {
  return rows.map((row) => {
    const f = flagships.find((x) => x.key === row.key) ?? null;
    const isCompound = row.key === "compound";
    const alone: DotGroup[] = [group("a0", "baseline-flagships-1", row.alone, `${ARM_WHAT.A0}, baseline-flagships-1`)];
    if (row.library?.alone) alone.push(group("a0-lib", "library-1", row.library.alone, `${ARM_WHAT.A0}, library-1`));
    const pf: DotGroup[] = row.harness.map((h) => group(h.arm.toLowerCase(), h.arm === "A1" ? "harness" : "with Wonder planner", h, ARM_WHAT[h.arm]));
    if (row.library) {
      const lib: Runs = {
        arm: "A2",
        runs: [...row.library.withLibrary.runs, ...(row.library.topdown?.runs ?? [])],
        accepted: row.library.withLibrary.accepted + (row.library.topdown?.accepted ?? 0),
      };
      pf.push(group("a2-lib", "planner and library", lib, `${ARM_WHAT.A2}, importing ProofForgeFin, library-1`));
    }
    return {
      key: row.key,
      incident: row.incident,
      year: row.year,
      href: f || row.key === COMPOUND.key ? `#case-${row.key}` : null,
      loss: f ? `${f.loss.amount.charAt(0).toUpperCase()}${f.loss.amount.slice(1)} ${f.loss.short}` : "COMP rewards credited but never emitted",
      requirements: row.requirements,
      alone: isCompound ? [...museCodeGroups(d, "alone"), ...alone] : alone,
      proofforge: isCompound ? [...museCodeGroups(d, "proofforge"), ...pf] : pf,
      spec: [group("impl", row.implement.arm === "A2" ? "with the planner" : "harness", row.implement, `Implementation from a stub generated from the locked specification, arm ${row.implement.arm}`)],
      refutations: row.refutations.map((r) => ({ label: r.label, refuted: r.refuted, kernelChecked: r.kernelChecked })),
    };
  });
}

/** Totals per matrix row, the figures the table in the disclosure states. */
export const rowTotals = (row: ComparisonRow) => ({ alone: aloneRuns(row), planner: plannerRuns(row) });

/* The incidents: a verdict trail from the vulnerable code to the Muse repair. */

export interface TrailStep {
  key: string;
  title: string;
  detail: string;
  verdict: Verdict;
  /** Requirement statuses as counts, in the order drawn: refuted, verified, then not proved. */
  counts: { refuted: number; verified: number; unresolved: number };
  /** For an attempt without a Passport: required theorems it proved in its session (its Passport counts none of them VERIFIED). */
  provedInSession?: number;
  total: number;
  passport: PassportRef | null;
  /** Who wrote the version: upstream code (ported by the build team) or a Muse model; unset for a vulnerable port of a flagship. */
  author?: "upstream" | "muse";
  /** For a step that stands for a set of runs rather than one version: how many of them were verified. */
  runs?: { verified: number; runs: number; text: string };
  /** For a step of several verified runs: each run's Passport, `passport` being the first. */
  passports?: { label: string; passport: PassportRef }[];
}

export function countsOf(reqs: Record<string, string>) {
  const v = Object.values(reqs);
  return {
    refuted: v.filter((s) => s === "REFUTED").length,
    verified: v.filter((s) => s === "VERIFIED").length,
    unresolved: v.filter((s) => s !== "REFUTED" && s !== "VERIFIED").length,
  };
}

/** The versions of an incident's code and their verdicts: the upstream timeline for the featured case, else the vulnerable port, earlier attempts and the repair. */
export function caseTrail(f: Flagship, rows: readonly ComparisonRow[] = COMPARISON): TrailStep[] {
  const total = Object.keys(f.repair.passport.requirements).length;
  if (f.timeline.length) {
    return f.timeline.map((v) => ({ key: v.key, title: v.title, detail: v.detail, verdict: v.verdict, counts: countsOf(v.passport.requirements), total, passport: v.passport }));
  }
  const row = rows.find((r) => r.key === f.key);
  const refuted = row ? row.refutations.reduce((n, r) => n + r.refuted, 0) : 0;
  const vulnerable: TrailStep = {
    key: "vulnerable",
    title: "Vulnerable code",
    detail: f.vulnerable.label,
    verdict: "REFUTED",
    counts: f.vulnerable.passport ? countsOf(f.vulnerable.passport.requirements) : { refuted, verified: 0, unresolved: total - refuted },
    total,
    passport: f.vulnerable.passport,
  };
  const earlier: TrailStep[] = f.unresolved.map((u) => ({
    key: u.run,
    title: "Earlier attempt",
    detail: `${u.label}, stopped by its ${u.stop}`,
    verdict: "UNRESOLVED",
    counts: countsOf(u.passport.requirements),
    provedInSession: u.proved,
    total,
    passport: u.passport,
  }));
  const repair: TrailStep = {
    key: "repair",
    title: "Muse repair",
    detail: `${f.repair.model}${f.repair.planner ? `, planned by ${f.repair.planner}` : ""}, attempt ${f.repair.attempt}`,
    verdict: "VERIFIED",
    counts: countsOf(f.repair.passport.requirements),
    total,
    passport: f.repair.passport,
  };
  return [vulnerable, ...earlier, repair];
}

/**
 * Compound Proposal 62 as a case: the Proposal 62 port, Muse Code on its own and with ProofForge
 * (frontier-2 and frontier-3, from the wins ledger), and the Proposal 64 fix, all against the same
 * locked requirements.
 */
export function compoundTrail(d: WinsData): TrailStep[] {
  const { f3, f2, pooled, model } = compoundFrontier(d);
  const C = COMPOUND_CASE;
  const total = Object.keys(C.fix.requirements).length;
  const first = C.repairs[0];
  return [
    {
      key: "p62",
      title: COMPOUND.vulnerable.label,
      detail: "the upgrade's reward code, ported to Lean by the build team",
      verdict: "REFUTED",
      counts: countsOf(C.port.requirements),
      total,
      passport: C.port,
      author: "upstream",
    },
    {
      key: "alone",
      title: "Muse Code on its own",
      detail: `${model} in Muse Code with Lean only, frontier-2 and frontier-3`,
      verdict: "UNRESOLVED",
      counts: { refuted: 0, verified: 0, unresolved: total },
      total,
      passport: null,
      author: "muse",
      runs: {
        verified: pooled.alone.verified,
        runs: pooled.alone.runs,
        text: `${runsOf(f2.alone)} in frontier-2 and ${runsOf(f3.alone)} in frontier-3; no Passport VERIFIED.`,
      },
    },
    {
      key: "proofforge",
      title: "Muse Code with ProofForge",
      detail: `${model} in Muse Code with ProofForge, frontier-3`,
      verdict: "VERIFIED",
      counts: countsOf(first!.passport.requirements),
      total,
      passport: first!.passport,
      author: "muse",
      runs: { verified: f3.proofforge.verified, runs: f3.proofforge.runs, text: `Verified: ${C.repairs.map((r) => r.run).join(" and ")}.` },
      passports: C.repairs.map((r) => ({ label: r.run, passport: r.passport })),
    },
    {
      key: "p64",
      title: "Proposal 64 fix",
      detail: "the fix that shipped, ported to Lean by the build team",
      verdict: "VERIFIED",
      counts: countsOf(C.fix.requirements),
      total,
      passport: C.fix,
      author: "upstream",
    },
  ];
}

/** The Compound loss for its tab: the dollar figure of COMPOUND.loss.amount, with the words that bound it. */
export function compoundTabLoss(amount: string = COMPOUND.loss.amount): { qualifier: string; figure: string } {
  const m = /^(at worst) .+?, (about) (\$\d+ (?:million|billion)) at the time$/.exec(amount);
  if (!m) throw new Error(`unexpected Compound loss: ${amount}`);
  return { qualifier: `${m[1]} ${m[2]}`, figure: m[3]! };
}

/** "about $223 million" as a qualifier and a figure, so the figure can be drawn large; the words are the README's. */
export function lossParts(amount: string): { qualifier: string; figure: string } {
  const m = /^(about|more than|over)\s+(.*)$/.exec(amount);
  return m ? { qualifier: m[1]!, figure: m[2]! } : { qualifier: "", figure: amount };
}
