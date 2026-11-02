// The preregistered experiments as the /methods page reads them: generated/methods.json, written by
// scripts/methods.mjs from results/*/PREREGISTRATION.md, the experiments' READMEs and the wins
// ledger. tests/methods.test.ts pins every field to those files.

import data from "@/generated/methods.json";
import { REPO_URL } from "./flagships";
import { factor1, modelName, pValue, usd } from "./wins";

export interface MethodsArm {
  verified: number;
  runs: number;
  usdPerVerified: number | null;
  usdTotal: number | null;
  capStops: number;
  reqMean: number;
  reqTotal: number;
}

export interface MethodsComparison {
  id: string;
  task: string;
  model: string;
  alone: MethodsArm;
  proofforge: MethodsArm;
  test: { name: string; p: number; secondary?: { name: string; p: number } } | null;
  factors: { cost: number | null; time: number | null };
}

export type MethodsStatus = "finished" | "running" | "queued";

export interface Preregistration {
  id: string;
  prereg: string;
  readme: string | null;
  written: string;
  commit: string;
  commitFull: string;
  commitDate: string;
  question: string;
  questionMore: string[];
  runs: number;
  runsText: string;
  testName: string;
  primaryTest: string;
  addenda: string[];
  status: MethodsStatus;
  label: string;
  note: string;
  tasks: MethodsComparison[];
  pooled: MethodsComparison[];
}

export interface MethodsData {
  source: string;
  ledger: string;
  generator: string;
  asOf: string;
  entries: Preregistration[];
}

export const METHODS = data as unknown as MethodsData;

export const commitUrl = (full: string) => `${REPO_URL}/commit/${full}`;

/** Task comparisons with the largest gain for ProofForge first. */
export const byGain = (cs: MethodsComparison[]) =>
  [...cs].sort((a, b) => b.proofforge.verified - b.alone.verified - (a.proofforge.verified - a.alone.verified));

const of = (a: MethodsArm) => `${a.verified} of ${a.runs}`;

/** The figures of one comparison, effect first: runs verified, cost, time, then p as a number. */
export function resultSentence(c: MethodsComparison): string {
  const parts = [`${of(c.proofforge)} runs verified with ProofForge, ${of(c.alone)} on its own`];
  const pf = c.proofforge.usdPerVerified;
  const al = c.alone.usdPerVerified;
  if (pf !== null && al !== null) {
    const f = c.factors.cost !== null && c.factors.cost >= 1.05 ? `, ${factor1(c.factors.cost)} cheaper` : "";
    parts.push(`${usd(pf)} per verified run against ${usd(al)}${f}`);
  } else if (pf !== null) {
    parts.push(`${usd(pf)} per verified run with ProofForge`);
  }
  if (c.factors.time !== null && c.factors.time >= 1.05) parts.push(`verified runs ${factor1(c.factors.time)} faster`);
  let s = parts.join("; ");
  if (c.test) {
    s += ` (${c.test.name} p = ${pValue(c.test.p)}`;
    if (c.test.secondary) s += `; ${c.test.secondary.name}, p = ${pValue(c.test.secondary.p)}`;
    s += ")";
  }
  return `${s}.`;
}

/** A pooled comparison of an experiment, as one sentence. */
export function pooledSentence(c: MethodsComparison): string {
  const t = c.test ? `, ${c.test.name} p = ${pValue(c.test.p)}` : "";
  return `${of(c.proofforge)} with ProofForge against ${of(c.alone)} on its own${t}.`;
}

export const taskModel = (c: MethodsComparison) => modelName(c.model);

/** Counts for the summary strip. */
export function methodsCounts(d: MethodsData) {
  const n = (s: MethodsStatus) => d.entries.filter((e) => e.status === s).length;
  return {
    plans: d.entries.length,
    runs: d.entries.reduce((t, e) => t + e.runs, 0),
    finished: n("finished"),
    running: n("running"),
    queued: n("queued"),
  };
}
