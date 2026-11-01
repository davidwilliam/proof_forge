// The wins of ProofForge over a Meta model alone, from results/wins/ledger.json (eval/wins.py) as
// copied by scripts/wins.mjs into generated/wins.json. Every figure is the ledger's; this module
// only selects and words them. tests/wins.test.ts checks each headline against the ledger.
//
// This module has no runtime imports, so scripts/evidence.mjs can load it on its own; pages read
// the data through lib/wins-data.ts.

export type Outcome = "win" | "tie" | "loss" | "n/a";
export type Dimension = "verification" | "cost" | "time" | "requirements" | "cap_stops";
export type Kind = "real-world" | "benchmark" | "catches";

export interface Arm {
  arm: string;
  label: string;
  runs: number;
  verified: number;
  /** All list dollars of the arm divided by its verified runs; null when no run verified. */
  usdPerVerified: number | null;
  usdTotal: number;
  priceBasis: string;
  caps: { usd: number; seconds: number }[];
  capStops: number;
  reqMean: number;
  reqTotal: number;
  passports: string[];
  judgeRecords: number;
}

export interface Test {
  name: string;
  p: number;
  preregistered: boolean;
  significant: boolean;
  statedIn: string;
  /** A preregistered secondary test, reported without a confirmatory claim. */
  secondary?: { name: string; p: number };
}

export interface Comparison {
  id: string;
  experiment: string;
  task: string;
  model: string;
  scope: "task" | "aggregate";
  kind: Kind;
  alone: Arm;
  proofforge: Arm;
  equalCaps: boolean;
  time: { alone: number | null; proofforge: number | null; basis: string };
  classification: Record<Dimension, Outcome>;
  factors: { cost: number | null; time: number | null };
  test: Test | null;
  flags: string[];
  /** Indexes into WinsData.caveats. */
  caveats: number[];
  links: { comparison: string; reports: string[] };
}

export interface Catches {
  id: string;
  experiment: string;
  task: string;
  kind: "catches";
  badCases: number;
  badCasesWithCompleteProofs: number;
  goodCases: number;
  badAccepted: { ordinary: number; rebuildAndTests: number; proofforge: number };
  goodRejected: { ordinary: number; rebuildAndTests: number; proofforge: number };
  passedRebuildAndTests: string[];
  caveats: string[];
  links: { comparison: string; reports: string[] };
}

export interface Win {
  /** 1: the model alone did not verify and ProofForge did; 2: both verified, ProofForge cheaper or faster; 3: other kinds. */
  group: 1 | 2 | 3;
  id: string;
  kind: string | null;
  costFactor: number | null;
  timeFactor: number | null;
  /** The ledger's sentence, as in results/wins/README.md. */
  sentence: string;
}

export interface WinsData {
  source: string;
  readme: string;
  generator: string;
  rules: Record<string, string>;
  counts: {
    comparisons: number;
    runs: number;
    wins_group_1: number;
    wins_group_2: number;
    wins_group_3: number;
    classification: Record<Dimension, Record<Outcome, number>>;
    claims_checked: number;
    claims_differing: number;
  };
  optionalSources: Record<string, { source: string; found: boolean; note?: string; on_branch?: boolean }>;
  notComparisons: { source: string; why: string }[];
  caveats: string[];
  comparisons: Comparison[];
  catches: Catches;
  wins: Win[];
}

export const DIMENSIONS: { key: Dimension; letter: string; label: string }[] = [
  { key: "verification", letter: "V", label: "Verification" },
  { key: "cost", letter: "C", label: "Cost" },
  { key: "time", letter: "T", label: "Time" },
  { key: "requirements", letter: "R", label: "Requirements" },
  { key: "cap_stops", letter: "S", label: "Cap stops" },
];

export const GROUPS: { group: 1 | 2 | 3; title: string; text: string }[] = [
  {
    group: 1,
    title: "Verified only with ProofForge",
    text: "Task-level comparisons and aggregates where no run of the model on its own verified and at least one run with ProofForge did. In E1 there is one run per arm per task.",
  },
  {
    group: 2,
    title: "Verified either way, cheaper or faster with ProofForge",
    text: "The factor is the model's value on its own divided by its value with ProofForge: list dollars per verified run, or the mean wall time of the verified runs. A difference under 5% is a tie and not listed.",
  },
  {
    group: 3,
    title: "Other gains",
    text: "Verified more often where the model on its own also verified some runs; more requirements proved or fewer runs stopped by a cap where verification did not differ; bad candidates caught that ordinary checking accepted.",
  },
];

/** Display names of the Meta models in the ledger. */
const MODELS: Record<string, string> = {
  "muse-spark-1.3-contributor": "Muse Spark 1.3",
  "meta-models/muse-spark-open-1026": "Muse Spark Open",
  "glimmer/muse-glimmer-30b": "Muse Glimmer 30B",
};
export const modelName = (id: string) => MODELS[id] ?? id;

export const fmtInt = (n: number) => n.toLocaleString("en-US");
export const usd = (n: number | null) => (n === null ? "n/a" : `$${n.toLocaleString("en-US", { minimumFractionDigits: 2, maximumFractionDigits: 2 })}`);
export const seconds = (n: number | null) => (n === null ? "n/a" : `${fmtInt(Math.round(n))} s`);
/** A factor of the ledger (two decimals) to one decimal: 4.18 becomes "4.2x". */
export const factor1 = (x: number) => `${x.toFixed(1)}x`;
export const factor2 = (x: number) => `${x.toFixed(2)}x`;
/** p as stated in the reports: at most two significant digits below 0.1, else two decimals. */
export function pValue(p: number): string {
  if (p >= 1) return "1";
  if (p >= 0.1) return String(Number(p.toFixed(2)));
  return String(Number(p.toPrecision(2)));
}

/** The test of a comparison in words, never stronger than the ledger: preregistered only when it was, significant only when it was. */
export function testPhrase(t: Test, outcome?: Outcome): string {
  const pre = t.preregistered ? "preregistered " : "";
  if (!t.significant) return `${pre}${t.name} p = ${pValue(t.p)}, not significant at 0.05`;
  const dir = outcome === "win" ? " for ProofForge" : outcome === "loss" ? " against ProofForge" : "";
  return `${pre}${t.name} p = ${pValue(t.p)}, significant at 0.05${dir}`;
}

const capital = (s: string) => s.charAt(0).toUpperCase() + s.slice(1);

export const runsOf = (a: Arm) => `${a.verified} of ${a.runs}`;

export function comparison(d: WinsData, id: string): Comparison {
  const c = d.comparisons.find((x) => x.id === id);
  if (!c) throw new Error(`${id}: not in ${d.source}`);
  return c;
}

/** The ledger sentence without its leading comparison ID, model and arms, which the page shows on their own. */
export function winDetail(d: WinsData, w: Win): string {
  const prefix = `\`${w.id}\`: `;
  let s = w.sentence.startsWith(prefix) ? w.sentence.slice(prefix.length) : w.sentence;
  const c = d.comparisons.find((x) => x.id === w.id);
  if (c) {
    const head = `${c.model}, ${c.alone.arm} against ${c.proofforge.arm}: `;
    if (s.startsWith(head)) s = s.slice(head.length);
  }
  return s.charAt(0).toUpperCase() + s.slice(1);
}

export const kindOf = (d: WinsData, w: Win): Kind => (w.id === d.catches.id ? "catches" : comparison(d, w.id).kind);

export const KIND_LABEL: Record<Kind, string> = {
  "real-world": "Real-world tasks",
  benchmark: "E1 benchmark",
  catches: "E2 catches",
};

/** IDs of the headline wins, hardest real-world tasks first. */
export const HEADLINE_IDS = {
  vyper: "vyper-replication-1/rw-vyper-sqrt+hard-task-1",
  vyperFirst: "hard-task-1/rw-vyper-sqrt",
  vyperReplication: "vyper-replication-1/rw-vyper-sqrt",
  balancer: "library-1/rw-balancer-upscale/all-measured/A2-vs-A0",
  openAll: "e1-test-open-1/all/A1-vs-A0",
  openExperiment: "e1-test-open-1",
} as const;

export interface Headline {
  key: string;
  figure: string;
  figureAlt: string;
  text: string;
  note: string;
  /** Repository paths: the full comparison in results/wins/README.md, then the reports. */
  links: { label: string; path: string }[];
}

const reportLinks = (paths: string[]) => paths.map((p) => ({ label: p.replace(/\/(README|e1|e2)\.md$/, "").replace(/^results\//, ""), path: p }));

/** The four strongest wins, each with its significance stated as the ledger states it. */
export function headlines(d: WinsData): Headline[] {
  const v = comparison(d, HEADLINE_IDS.vyper);
  const v1 = comparison(d, HEADLINE_IDS.vyperFirst);
  const v2 = comparison(d, HEADLINE_IDS.vyperReplication);
  const b = comparison(d, HEADLINE_IDS.balancer);
  const openAll = comparison(d, HEADLINE_IDS.openAll);
  const openWins = d.wins.filter((w) => w.group === 1 && w.id.startsWith(`${HEADLINE_IDS.openExperiment}/`) && comparison(d, w.id).scope === "task");
  const openRuns = openWins.map((w) => comparison(d, w.id));
  const openLosses = d.comparisons.filter((c) => c.experiment === HEADLINE_IDS.openExperiment && c.scope === "task" && c.classification.verification === "loss");
  const openCapped = openRuns.filter((c) => c.alone.capStops === c.alone.runs).length;
  const openCap = openAll.alone.caps[0]!;
  const vCap = v.alone.caps[0]!;
  const bCap = b.alone.caps[0]!;
  const e = d.catches;
  return [
    {
      key: "vyper",
      figure: `${v.alone.verified} → ${v.proofforge.verified}`,
      figureAlt: `of ${v.proofforge.runs}`,
      text: `Vyper sqrt(), CVE-2025-26622, over two preregistered experiments: ${modelName(v.model)} in Muse Code verified ${runsOf(v.proofforge)} runs with ProofForge and ${runsOf(v.alone)} on its own, ${factor1(v.factors.cost!)} cheaper per verified run (${usd(v.proofforge.usdPerVerified)} against ${usd(v.alone.usdPerVerified)}) and ${factor1(v.factors.time!)} faster.`,
      note: `First experiment ${runsOf(v1.proofforge)} against ${runsOf(v1.alone)} (p = ${pValue(v1.test!.p)}); replication ${runsOf(v2.proofforge)} against ${runsOf(v2.alone)} (p = ${pValue(v2.test!.p)}), where ProofForge runs spent fewer list dollars (${v2.test!.secondary!.name.replace(/, ProofForge.*$/, "")} p = ${pValue(v2.test!.secondary!.p)}, a preregistered secondary test). Pooled, ${testPhrase({ ...v.test!, name: "one-sided Fisher exact", preregistered: false })}; the pool includes the runs that motivated the replication. List prices, caps of $${vCap.usd} and ${vCap.seconds / 3600} hours per run. The ProofForgeFin square-root module was written by the build team knowing the task.`,
      links: [{ label: "Full comparison", path: v.links.comparison }, ...reportLinks([...new Set([...v1.links.reports, ...v2.links.reports])])],
    },
    {
      key: "balancer",
      figure: factor1(b.factors.cost!),
      figureAlt: "cheaper",
      text: `Per verified Balancer V2 repair: ${modelName(b.model)} verified ${runsOf(b.proofforge)} runs with ProofForge at ${usd(b.proofforge.usdPerVerified)} each and ${runsOf(b.alone)} on its own at ${usd(b.alone.usdPerVerified)}, ${factor1(b.factors.time!)} faster.`,
      note: `Caps of $${bCap.usd} and ${bCap.seconds / 3600} hours per run, list prices. The ProofForge arm adds Muse Wonder 1.0 as lemma planner, a second Meta model on the same budget, and the runs are pooled from three experiments. On the verification rate, ${testPhrase(b.test!)}${b.test!.preregistered ? "" : "; the test was not preregistered"}.`,
      links: [{ label: "Full comparison", path: b.links.comparison }, ...reportLinks(b.links.reports)],
    },
    {
      key: "open",
      figure: `${openWins.length} tasks`,
      figureAlt: `of ${openAll.alone.runs}`,
      text: `Where ${modelName(openAll.model)}, Meta's open-weight model, did not verify on its own and verified with ProofForge, on the frozen test tasks; on its own, ${openCapped === openWins.length ? `each of those ${openWins.length} runs` : `${openCapped} of those ${openWins.length} runs`} stopped at the $${openCap.usd} cap.`,
      note: `Over all ${openAll.alone.runs} tasks: ${openAll.proofforge.verified} verified with ProofForge, ${openAll.alone.verified} on its own, and on ${openLosses.length} tasks only the model on its own verified; ${testPhrase(openAll.test!)}.`,
      links: [{ label: "Full comparison", path: comparison(d, openWins[0]!.id).links.comparison }, ...reportLinks(openAll.links.reports)],
    },
    {
      key: "catches",
      figure: `${e.badAccepted.proofforge} of ${e.badCases}`,
      figureAlt: `vs ${e.badAccepted.ordinary}`,
      text: `Seeded bad candidates accepted by ProofForge; ordinary checking (the build passes, the theorem names exist, the axioms are clean) accepted ${e.badAccepted.ordinary}, the rebuild with property tests ${e.badAccepted.rebuildAndTests}.`,
      note: `ProofForge rejected ${e.goodRejected.proofforge} of ${e.goodCases} good candidates. No model is involved, and the bad cases were written by the build team, so the counts describe this suite.`,
      links: [{ label: "Full comparison", path: e.links.comparison }, ...reportLinks(e.links.reports)],
    },
  ];
}

/** One sentence with the counts of the ledger, for the home page, the README and llms.txt. */
export function countsSentence(d: WinsData): string {
  const c = d.counts;
  return `${fmtInt(c.comparisons)} comparisons over ${fmtInt(c.runs)} runs: on ${c.wins_group_1} the model verified only with ProofForge, on ${c.wins_group_2} it verified either way and ProofForge made it cheaper or faster, and ${c.wins_group_3} are gains of other kinds.`;
}
