// The hidden challenge as the /challenge page reads it: generated/challenge.json, written by
// scripts/challenge.mjs from hidden/*/task.json and validation.json, server/app.py and
// reports/reliability/*.json. tests/challenge.test.ts fails when the generated file is stale.

import data from "@/generated/challenge.json";

export interface ChallengeVariant {
  id: string;
  family: string;
  lib: string;
  definitions: string[];
  requirements: string[];
  exe: string;
  source: string;
  validation: {
    source: string;
    checks: { check: string; passed: boolean }[];
    references: { file: string; judge: string; judgeMs: number; binary: string }[];
    start: { judge: string; binary: string };
  };
}

export interface RecordedCall {
  session: number;
  refuted: boolean;
  seconds: number;
}

export interface ReliabilityRun {
  source: string;
  recordedAt: string;
  api: string;
  calls: RecordedCall[];
}

export interface ChallengeData {
  generator: string;
  server: { source: string; propertyCases: number; deadlineS: number };
  variants: ChallengeVariant[];
  reliability: { runner: string; variant: string; refutedMeans: string; runs: ReliabilityRun[] };
}

export const CHALLENGE = data as ChallengeData;

/** The page's target for a witness, in milliseconds. */
export const TARGET_MS = 20000;

export function median(xs: number[]): number {
  const s = [...xs].sort((a, b) => a - b);
  const m = s.length >> 1;
  return s.length % 2 ? s[m]! : (s[m - 1]! + s[m]!) / 2;
}

/** The figures of the page's KPI strip, every one counted from generated/challenge.json. */
export function challengeFacts(d: ChallengeData = CHALLENGE) {
  const calls = d.reliability.runs.flatMap((r) => r.calls);
  const secs = calls.map((c) => c.seconds);
  const refs = d.variants.flatMap((v) => v.validation.references);
  return {
    variants: d.variants.length,
    calls: calls.length,
    refuted: calls.filter((c) => c.refuted).length,
    medianSeconds: secs.length ? median(secs) : null,
    maxSeconds: secs.length ? Math.max(...secs) : null,
    minSeconds: secs.length ? Math.min(...secs) : null,
    references: refs.length,
    referencesAccepted: refs.filter((r) => r.judge === "ACCEPT" && r.binary === "PASS").length,
    startsRefuted: d.variants.filter((v) => v.validation.start.binary === "REFUTED").length,
    propertyCases: d.server.propertyCases,
  };
}

/** "2026-10-28T02:15:47-0400" as "2026-10-28 02:15", the recorder's local time as written. */
export const recordedLabel = (s: string) => s.replace("T", " ").slice(0, 16);

// A payout witness as the payout sidecar reads and writes it (oracle.py of the payout tasks).

export interface PayoutState {
  balances: [number, number][];
  auth: [number, number][];
  applied: number[];
}

export interface PayoutWitness {
  state: PayoutState;
  request: { txId: number; requester: number; source: number; recipients: number[]; amount: number };
  outcome: string;
  after: PayoutState | null;
}

const isPairs = (x: unknown): x is [number, number][] =>
  Array.isArray(x) && x.every((p) => Array.isArray(p) && p.length === 2 && p.every((n) => typeof n === "number"));
const isNums = (x: unknown): x is number[] => Array.isArray(x) && x.every((n) => typeof n === "number");
const isState = (x: unknown): x is PayoutState => {
  const s = x as PayoutState | null;
  return !!s && typeof s === "object" && isPairs(s.balances) && isPairs(s.auth) && isNums(s.applied);
};

/** The witness as a payout, or null when its input and output are not payout-shaped. */
export function payoutWitness(input: unknown, output: unknown): PayoutWitness | null {
  const i = input as { state?: unknown; request?: PayoutWitness["request"] } | null;
  const o = output as { outcome?: unknown; state?: unknown } | null;
  if (!i || typeof i !== "object" || !isState(i.state)) return null;
  const r = i.request;
  if (!r || typeof r !== "object" || ![r.txId, r.requester, r.source, r.amount].every((n) => typeof n === "number") || !isNums(r.recipients)) return null;
  if (!o || typeof o !== "object" || typeof o.outcome !== "string") return null;
  return { state: i.state, request: r, outcome: o.outcome, after: isState(o.state) ? o.state : null };
}

export interface BalanceRow {
  account: number;
  before: number | null;
  after: number | null;
  delta: number | null;
  role: string;
}

/** Every account of the witness, before and after, with its role in the request. */
export function balanceRows(w: PayoutWitness): BalanceRow[] {
  const before = new Map(w.state.balances);
  const after = new Map(w.after?.balances ?? []);
  const accounts = [...new Set([...before.keys(), ...after.keys()])];
  const role = (a: number) => {
    const r: string[] = [];
    if (a === w.request.source) r.push("source");
    if (a === w.request.requester) r.push("requester");
    if (w.request.recipients.includes(a)) r.push("recipient");
    return r.join(", ");
  };
  return accounts.map((a) => {
    const b = before.get(a) ?? null;
    const f = w.after ? (after.get(a) ?? null) : null;
    return { account: a, before: b, after: f, delta: b != null && f != null ? f - b : null, role: role(a) };
  });
}
