// The Balancer V2 rounding exploit replay (/app): the versions of the swap wrapper, the preset
// batches, input checks that mirror POST /api/swap, and the summaries the page shows.
// Every figure here is copied from a committed file named beside it; tests/swap.test.ts checks
// the Passport hashes and statuses, the preset batches against the witness file, the
// requirement ids against the task, and the measured figures against results/library-1/README.md.
// Pure functions only; amounts are decimal strings or bigint because they exceed 2^53.

export const TASK = "realworld/tasks/rw-balancer-upscale";

export type VersionKey = "deployed" | "plus_one" | "repaired";
export type Verdict = "REFUTED" | "VERIFIED";

export interface VersionInfo {
  key: VersionKey;
  /** Card title. */
  name: string;
  /** Column label in the replay. */
  short: string;
  /** Who wrote it, in one sentence. */
  origin: string;
  verdict: Verdict;
  /** The lines that differ between the versions; lines starting with -- are comments added here. */
  code: string[];
  /** What the check found, in one or two sentences. */
  finding: string;
  source: string;
  passport: { path: string; sha256: string; status: Verdict; requirements: Record<string, string> };
  /** Kernel-checked counterexample files, when REFUTED. */
  counterexamples: { label: string; path: string }[];
}

const ALL_REQ = [
  "REQ-GIVEN-IN-SUCCEEDS",
  "REQ-GIVEN-OUT-SUCCEEDS",
  "REQ-GIVEN-IN-PAYS-AT-MOST",
  "REQ-GIVEN-IN-PAYS-AT-LEAST",
  "REQ-GIVEN-OUT-CHARGES-AT-LEAST",
  "REQ-GIVEN-OUT-CHARGES-AT-MOST",
  "REQ-SWAP-KEEPS-VALUE",
  "REQ-BATCH-KEEPS-VALUE",
] as const;

const statuses = (refuted: string[], rest: string): Record<string, string> =>
  Object.fromEntries(ALL_REQ.map((id) => [id, refuted.includes(id) ? "REFUTED" : rest]));

export const VERSIONS: VersionInfo[] = [
  {
    key: "deployed",
    name: "Deployed code",
    short: "Deployed",
    origin: "A Lean port of the swap path of the osETH/WETH pool as deployed; it charges exactly the logged amount of all 90 attack swaps.",
    verdict: "REFUTED",
    // attacks/balancer_port.lean, swapGivenOut
    code: ["-- rounds the amount out down (mulDown)", "let amount :=", "  upscale s.amount (p.rate s.tokenOut)", "if balances s.tokenOut < amount then none"],
    // witnesses/attack_batch.lean, part 1; results/counterexamples-1/balancer-port
    finding:
      "Four rounds of the attack's three swaps lower the pool's value from 4,749,898,000 to 297,229,191. Kernel-checked counterexamples refute REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE and REQ-BATCH-KEEPS-VALUE.",
    source: `${TASK}/attacks/balancer_port.lean`,
    passport: {
      path: "results/counterexamples-1/balancer-port/passport.json",
      sha256: "12f25046108e6eb18ff33592d46938080c2f9d2d04c90c5e21c9bdce752c033c",
      status: "REFUTED",
      requirements: statuses(["REQ-GIVEN-OUT-CHARGES-AT-LEAST", "REQ-SWAP-KEEPS-VALUE", "REQ-BATCH-KEEPS-VALUE"], "UNRESOLVED"),
    },
    counterexamples: [
      { label: "batch refutation", path: "results/counterexamples-1/balancer-port/cex/cex_req_batch_keeps_value.lean" },
      { label: "attack witness", path: `${TASK}/witnesses/attack_batch.lean` },
    ],
  },
  {
    key: "plus_one",
    name: "Plus-one hotfix",
    short: "Plus-one",
    origin: "The obvious patch: round down as before, then add one unit. It is not a release of any project.",
    verdict: "REFUTED",
    // attacks/plus_one.lean, swapGivenOut
    code: ["-- rounds down, then adds one unit", "let amount :=", "  upscale s.amount (p.rate s.tokenOut) + 1", "if balances s.tokenOut ≤ amount then none"],
    // results/balancer-1/plus-one/passport.json, counterexamples
    finding:
      "It never undercharges, but a whole amount is priced one unit high: 20 wei worth exactly 22 units is priced as 23. It also refuses swaps the pool can pay. Kernel-checked counterexamples refute REQ-GIVEN-OUT-CHARGES-AT-MOST and REQ-GIVEN-OUT-SUCCEEDS.",
    source: `${TASK}/attacks/plus_one.lean`,
    passport: {
      path: "results/balancer-1/plus-one/passport.json",
      sha256: "8cf3ba86f71e644d47407a11931d3ceead4b5ca5239f9a34279e5a546b98cf53",
      status: "REFUTED",
      requirements: statuses(["REQ-GIVEN-OUT-SUCCEEDS", "REQ-GIVEN-OUT-CHARGES-AT-MOST"], "UNRESOLVED"),
    },
    counterexamples: [
      { label: "overcharge refutation", path: "results/balancer-1/plus-one/cex/cex_req_given_out_charges_at_most.lean" },
      { label: "refusal refutation", path: "results/balancer-1/plus-one/cex/cex_req_given_out_succeeds.lean" },
    ],
  },
  {
    key: "repaired",
    name: "Muse repair",
    short: "Muse repair",
    origin: "Written by Muse Spark 1.3 with the Muse Wonder planner inside ProofForge, in 2,344 s at $2.51 list.",
    verdict: "VERIFIED",
    // results/balancer-1/repair-A2-1/final.lean, swapGivenOut
    code: ["-- rounds the amount out up", "let amount :=", "  upscaleUp s.amount (p.rate s.tokenOut)", "if amount < balances s.tokenOut then", "  -- price it; otherwise refuse"],
    // results/balancer-1/repair-A2-1/check.txt
    finding: "All eight requirements are proved for any pool math meeting the stated contract, checked by six kernels, and its executable passes 2,001 property cases.",
    source: "results/balancer-1/repair-A2-1/final.lean",
    passport: {
      path: "results/balancer-1/repair-A2-1/passport.json",
      sha256: "48930efdd4d67460bfd22bb15dfa9625caafc36cd6fca3a8fee444d5f3b204ba",
      status: "VERIFIED",
      requirements: statuses([], "VERIFIED"),
    },
    counterexamples: [],
  },
];

export const versionInfo = (k: VersionKey): VersionInfo => VERSIONS.find((v) => v.key === k)!;

/** The requirements the Muse repair proves, as the task README states them (spec/BalancerSwap/Challenge.lean). */
export const REQUIREMENTS: { id: (typeof ALL_REQ)[number]; text: string }[] = [
  { id: "REQ-GIVEN-IN-SUCCEEDS", text: "A given-in swap between two tokens of the pool goes through when the token out has a positive scaling factor and the fee is below 100%." },
  { id: "REQ-GIVEN-OUT-SUCCEEDS", text: "A given-out swap goes through when the exact amount out, rounded up, is below the pool's scaled balance of that token, the token in has a positive scaling factor and the fee is below 100%." },
  { id: "REQ-GIVEN-IN-PAYS-AT-MOST", text: "The trader receives at most what the math prices the exact amount in, net of the fee, rounded down." },
  { id: "REQ-GIVEN-IN-PAYS-AT-LEAST", text: "And at least what the math prices one raw unit less, less one raw unit out." },
  { id: "REQ-GIVEN-OUT-CHARGES-AT-LEAST", text: "The charge, after the fee, is at least what the math prices the exact amount out rounded up to a whole 18-decimal unit." },
  { id: "REQ-GIVEN-OUT-CHARGES-AT-MOST", text: "One raw unit less than the charge is below that price plus one raw unit: at most one unit for the conversion back and one for the fee." },
  { id: "REQ-SWAP-KEEPS-VALUE", text: "A swap that goes through never lowers the pool's value." },
  { id: "REQ-BATCH-KEEPS-VALUE", text: "Any batch of swaps of either kind, of any length, that goes through never lowers the pool's value." },
];

/** results/library-1/README.md, "Balancer across all measured runs". */
export const MEASURED = {
  source: "results/library-1/README.md",
  alone: { verified: 2, runs: 5, usdTotal: 40.04, usdPerVerified: 20.02 },
  forge: { verified: 3, runs: 3, usdTotal: 9.18, usdPerVerified: 3.06 },
  capUsd: 10,
  capHours: 4,
  fisherP: 0.18,
  /** The three Muse-alone runs that did not verify (checked again with bin/proofforge check). */
  failedAlone: [
    "results/library-1/rw-balancer-upscale/A0-1",
    "results/library-1/rw-balancer-upscale/A0-2",
    "results/baseline-flagships-1/rw-balancer-upscale/A0-1",
  ],
  failedAloneCases: 2001,
};

// Batches

export interface SwapSpec {
  kind: "in" | "out";
  in: number;
  out: number;
  amount: string;
}

export interface SwapBatch {
  math: "product" | "stable";
  amp?: string;
  pool: { balances: [string, string]; rates: [string, string]; fee: string };
  swaps: SwapSpec[];
}

export interface Preset {
  key: string;
  title: string;
  /** What the batch is and what to look for, in one or two sentences. */
  summary: string;
  tokens: [string, string];
  batch: SwapBatch;
}

const E18 = "1000000000000000000";
/** The osETH scaling factor during the attack (task README, "Read from chain data"). */
export const OSETH_RATE = "1058132408689971699";
/** 0.01%, the osETH/WETH pool's swap fee. */
const POOL_FEE = "100000000000000";

const out = (i: number, o: number, amount: number | string): SwapSpec => ({ kind: "out", in: i, out: o, amount: String(amount) });

/** witnesses/attack_batch.lean, part 1, `batch`: four rounds in the attack's shape. */
const FOUR_ROUNDS: SwapSpec[] = (
  [
    [66982, 2375365494],
    [66982, 1188037286],
    [66982, 594195912],
    [66978, 297187558],
  ] as const
).flatMap(([a, w]) => [out(0, 1, a), out(0, 1, 17), out(1, 0, w)]);

/** witnesses/attack_batch.lean, part 2, `attackSwaps`: Swap events 23 to 112 of the transaction. */
const ATTACK_SWAPS: SwapSpec[] = (
  [
    [66982, 891000], [5165, 666000], [9016, 495000], [12206, 369000], [17532, 270000], [14434, 198000],
    [11377, 160000], [22554, 120000], [17663, 89100], [12038, 67500], [10414, 52200], [9007, 40500],
    [7867, 31500], [6554, 24300], [5472, 19800], [4749, 16200], [4397, 12600], [3442, 10800],
    [3296, 9000], [2886, 7371], [2286, 6480], [2124, 6075], [2014, 5589], [1902, 4779],
    [1730, 4455], [1664, 3969], [1562, 3726], [1492, 3645], [1484, 3564], [1444, 3564],
  ] as const
).flatMap(([a, w]) => [out(0, 1, a), out(0, 1, 17), out(1, 0, w)]);

export const PRESETS: Preset[] = [
  {
    key: "attack",
    title: "The attack, four rounds",
    summary:
      "From 67,000 wei of each token, the attack's three swaps four times: osETH out down to 18 wei, 17 wei of osETH out, then WETH out paid with osETH. Constant-product math, which is proved to meet the requirements' contract, so the numbers are a counterexample, not a test.",
    tokens: ["WETH", "osETH"],
    batch: { math: "product", pool: { balances: ["67000", "67000"], rates: [E18, OSETH_RATE], fee: POOL_FEE }, swaps: FOUR_ROUNDS },
  },
  {
    key: "chain",
    title: "The attack's 90 swaps on chain",
    summary:
      "The 90 swaps the attack made on the osETH/WETH pool, with a port of Balancer's StableMath (amplification 200). The deployed code charges exactly the amounts the transaction logged. StableMath is not proved to meet the contract, so these results are tested, not proved.",
    tokens: ["WETH", "osETH"],
    batch: { math: "stable", amp: "200000", pool: { balances: ["67000", "67000"], rates: [E18, OSETH_RATE], fee: POOL_FEE }, swaps: ATTACK_SWAPS },
  },
  {
    key: "small",
    title: "A trade against a small balance",
    summary:
      "50 of the 100 units of token 1 out of a pool, tokens without a rate. The amount is whole, so the plus-one hotfix prices 51 units and charges about 4% more than the price.",
    tokens: ["token 0", "token 1"],
    batch: { math: "product", pool: { balances: ["1000000", "100"], rates: [E18, E18], fee: POOL_FEE }, swaps: [out(0, 1, 50)] },
  },
  {
    key: "refuse",
    title: "A valid swap the hotfix refuses",
    summary:
      "9 of the 10 units of token 1 out of a pool. The pool can pay it and the other two versions accept it; the plus-one hotfix asks the math for 10 of 10 and refuses.",
    tokens: ["token 0", "token 1"],
    batch: { math: "product", pool: { balances: ["1000000", "10"], rates: [E18, E18], fee: POOL_FEE }, swaps: [out(0, 1, 9)] },
  },
  {
    key: "ordinary",
    title: "An ordinary trade",
    summary:
      "Balancer's own regular-swap test: 0.1 token out of a stable pool holding 1 and 0.9, amplification 200, fee 0.0001%. The hotfix charges 1 wei more than the repair, which the one-unit allowance of REQ-GIVEN-OUT-CHARGES-AT-MOST permits; on a small balance the same extra unit costs far more.",
    tokens: ["token 0", "token 1"],
    batch: {
      math: "stable",
      amp: "200000",
      pool: { balances: ["1000000000000000000", "900000000000000000"], rates: [E18, E18], fee: "1000000000000" },
      swaps: [out(0, 1, "100000000000000000")],
    },
  },
];

// Limits, as in server/app.py

export const LIMITS = {
  swaps: 100,
  amount: 10n ** 30n,
  rate: 10n ** 24n,
  fee: 10n ** 17n,
  amp: 5_000_000n,
};

export type Checked<T> = { ok: true; value: T } | { ok: false; error: string };

export function parseWhole(text: string, name: string, lo: bigint, hi: bigint): Checked<string> {
  const t = text.trim().replace(/[,_]/g, "");
  if (!/^\d{1,40}$/.test(t)) return { ok: false, error: `${name} must be a whole number` };
  const v = BigInt(t);
  if (v < lo || v > hi) return { ok: false, error: `${name} must be from ${formatBig(lo)} to ${formatBig(hi)}` };
  return { ok: true, value: v.toString() };
}

/** One swap per line: `out 0 1 17` is 17 of token 1 out, paid with token 0; `in 1 0 5` is 5 of token 1 in for token 0. */
export function swapsToText(swaps: SwapSpec[]): string {
  return swaps.map((s) => `${s.kind} ${s.in} ${s.out} ${s.amount}`).join("\n");
}

export function parseSwaps(text: string): Checked<SwapSpec[]> {
  const lines = text
    .split("\n")
    .map((l) => l.trim())
    .filter((l) => l.length > 0);
  if (lines.length === 0) return { ok: false, error: "the batch has no swaps" };
  if (lines.length > LIMITS.swaps) return { ok: false, error: `a batch has at most ${LIMITS.swaps} swaps` };
  const swaps: SwapSpec[] = [];
  for (const [i, l] of lines.entries()) {
    const m = /^(in|out)\s+([01])\s+([01])\s+(\S+)$/.exec(l);
    if (!m) return { ok: false, error: `line ${i + 1}: write kind, token in, token out, amount, for example "out 0 1 17"` };
    const [, kind, a, b, amt] = m;
    if (a === b) return { ok: false, error: `line ${i + 1}: token in and token out differ` };
    const amount = parseWhole(amt!, `line ${i + 1}: amount`, 0n, LIMITS.amount);
    if (!amount.ok) return { ok: false, error: amount.error };
    swaps.push({ kind: kind as "in" | "out", in: Number(a), out: Number(b), amount: amount.value });
  }
  return { ok: true, value: swaps };
}

export interface BatchFields {
  math: "product" | "stable";
  amp: string;
  balances: [string, string];
  rates: [string, string];
  fee: string;
  swaps: string;
}

export function fieldsFromBatch(b: SwapBatch): BatchFields {
  return { math: b.math, amp: b.amp ?? "200000", balances: [...b.pool.balances], rates: [...b.pool.rates], fee: b.pool.fee, swaps: swapsToText(b.swaps) };
}

export function batchFromFields(f: BatchFields): Checked<SwapBatch> {
  const checks = [
    parseWhole(f.balances[0], "balance of token 0", 0n, LIMITS.amount),
    parseWhole(f.balances[1], "balance of token 1", 0n, LIMITS.amount),
    parseWhole(f.rates[0], "rate of token 0", 1n, LIMITS.rate),
    parseWhole(f.rates[1], "rate of token 1", 1n, LIMITS.rate),
    parseWhole(f.fee, "fee", 0n, LIMITS.fee),
  ];
  for (const c of checks) if (!c.ok) return { ok: false, error: c.error };
  const [b0, b1, r0, r1, fee] = checks.map((c) => (c as { value: string }).value) as [string, string, string, string, string];
  const swaps = parseSwaps(f.swaps);
  if (!swaps.ok) return { ok: false, error: swaps.error };
  const batch: SwapBatch = { math: f.math, pool: { balances: [b0, b1], rates: [r0, r1], fee }, swaps: swaps.value };
  if (f.math === "stable") {
    const amp = parseWhole(f.amp, "amplification", 1n, LIMITS.amp);
    if (!amp.ok) return { ok: false, error: amp.error };
    batch.amp = amp.value;
  }
  return { ok: true, value: batch };
}

// API response (POST /api/swap); whole numbers are decimal strings

export interface SwapStepOut {
  quote: string | null;
  ok: boolean;
  balances: string[];
  value: string | null;
}

export interface SwapResultOut {
  steps: SwapStepOut[];
  ok: boolean;
  value_before: string | null;
  balances_after: string[];
  value_after: string | null;
}

export interface SwapVersionOut {
  version: VersionKey;
  source: string;
  solution_sha256: string;
  executable_sha256: string;
  passport: { passport_sha256: string; status: string; path: string; requirements: Record<string, string> } | null;
  result: SwapResultOut;
  elapsed_ms: number;
}

export interface SwapResponse {
  input: SwapBatch;
  versions: SwapVersionOut[];
  elapsed_ms: number;
}

// Summaries

export interface Outcome {
  /** The batch went through. */
  ok: boolean;
  /** 1-based index of the swap that was refused, when the batch reverted. */
  refusedAt: number | null;
  before: bigint | null;
  /** Value after the batch; the starting value when it reverted. */
  after: bigint | null;
  /** Change of the value over the batch, in percent of the start. */
  changePct: number | null;
  /** Lowest value reached at any step, in percent of the start (before a revert undoes it). */
  lowestPct: number | null;
  /** Steps that ran (went through), and the total charged or paid on them. */
  ran: number;
}

const big = (s: string | null | undefined): bigint | null => (s == null ? null : BigInt(s));

/** a / b as a percentage, truncated to eight decimals, computed exactly in bigint. */
export function pct(a: bigint, b: bigint): number {
  if (b === 0n) return a === 0n ? 100 : Infinity;
  return Number((a * 10_000_000_000n) / b) / 100_000_000;
}

export function outcome(r: SwapResultOut): Outcome {
  const before = big(r.value_before);
  const after = big(r.value_after);
  const failed = r.steps.findIndex((s) => !s.ok);
  const values = r.steps.filter((s) => s.ok && s.value != null).map((s) => BigInt(s.value!));
  const lowest = values.length ? values.reduce((m, v) => (v < m ? v : m)) : null;
  return {
    ok: r.ok,
    refusedAt: failed >= 0 ? failed + 1 : null,
    before,
    after,
    changePct: before != null && after != null && before > 0n ? pct(after - before, before) : null,
    lowestPct: before != null && lowest != null && before > 0n ? pct(lowest, before) : null,
    ran: r.steps.filter((s) => s.ok).length,
  };
}

/** Pool value at each step, in percent of the start; index 0 is the start. Null after a refused step. */
export function valueSeries(r: SwapResultOut, steps: number): (number | null)[] {
  const before = big(r.value_before);
  const out: (number | null)[] = [before != null && before > 0n ? 100 : null];
  for (let i = 0; i < steps; i++) {
    const s = r.steps[i];
    out.push(s && s.ok && s.value != null && before != null && before > 0n ? pct(BigInt(s.value), before) : null);
  }
  return out;
}

// Formatting

export function formatBig(v: bigint | string | null | undefined): string {
  if (v == null) return "none";
  const s = typeof v === "bigint" ? v.toString() : v;
  const neg = s.startsWith("-");
  const d = neg ? s.slice(1) : s;
  return (neg ? "-" : "") + d.replace(/\B(?=(\d{3})+(?!\d))/g, ",");
}

export function formatPct(p: number | null, signed = false): string {
  if (p == null || !Number.isFinite(p)) return "none";
  const abs = Math.abs(p);
  // two decimals, or two significant digits for a change smaller than 0.01%
  const digits = abs === 0 || abs >= 0.01 ? 2 : Math.min(8, 1 - Math.floor(Math.log10(abs)));
  const s = abs.toFixed(digits);
  if (!signed) return `${s}%`;
  return p > 0 ? `+${s}%` : p < 0 ? `-${s}%` : `${s}%`;
}

export function describeSwap(s: SwapSpec, tokens: [string, string]): string {
  const a = formatBig(s.amount);
  const tin = tokens[s.in] ?? `token ${s.in}`;
  const tout = tokens[s.out] ?? `token ${s.out}`;
  return s.kind === "out" ? `${a} ${tout} out, paid in ${tin}` : `${a} ${tin} in, for ${tout}`;
}
