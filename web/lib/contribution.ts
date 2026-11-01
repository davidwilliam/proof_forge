// What ProofForge contributes beyond the Muse models, as measured in results/. Every figure is
// copied from the committed file named beside it; tests/contribution.test.ts recomputes each one
// from those files, and scripts/evidence.mjs publishes the same data in public/evidence.json and
// public/llms.txt.
//
// This module has no runtime imports, so scripts/evidence.mjs can load it on its own.

/** A set of agent runs on one task, all under the same caps. */
export interface Runs {
  /** A0 compile-and-retry, A1 the ProofForge harness, A2 the harness with Muse Wonder 1.0 as planner. */
  arm: "A0" | "A1" | "A2";
  /** Run directories, each with summary.json; an accepted run also has a VERIFIED passport.json. */
  runs: string[];
  /** Runs whose final candidate the judge accepted (summary.json accepted_in_session, Passport VERIFIED). */
  accepted: number;
}

export interface Refutation {
  /** results/counterexamples-1/<target>/passport.json */
  target: string;
  label: string;
  /** Requirements the rebuilt executable refuted. */
  refuted: number;
  /** Of those, refuted by a Lean theorem accepted by the six kernels and leanchecker. */
  kernelChecked: number;
}

/** results/library-1: Muse with ProofForge and the ProofForgeFin library against Muse alone. */
export interface LibraryResult {
  source: string;
  /** Muse Spark alone (A0) under the same caps, run in the same window; null where library-1 has none. */
  alone: Runs | null;
  /** Muse with the ProofForge harness, the Muse Wonder planner and the library (A2, orchestrated loop). */
  withLibrary: Runs;
  /** A2 with the library on the top-down loop (`--loop topdown`); null where library-1 has none. */
  topdown: Runs | null;
}

export interface ComparisonRow {
  /** Flagship key in lib/flagships.ts, or "compound". */
  key: string;
  task: string;
  incident: string;
  year: number;
  requirements: number;
  /** Muse Spark 1.3 alone: compile-and-retry with Lean's errors and the axiom audit (results/baseline-flagships-1). */
  alone: Runs;
  /** Muse Spark 1.3 with the ProofForge harness (A1), and with Muse Wonder 1.0 as planner (A2). */
  harness: Runs[];
  /** Implement mode: Muse starts from a stub generated from the locked specification. */
  implement: Runs;
  refutations: Refutation[];
  /** results/library-1 on Compound, Knight and Balancer; null for the tasks it did not run. */
  library: LibraryResult | null;
}

export const BASELINE_SOURCE = "results/baseline-flagships-1";
export const COUNTEREXAMPLE_SOURCE = "results/counterexamples-1";

/** Caps of every run in the comparison: $10 at list prices and 14,400 s (baseline-flagships-1/README.md). */
export const RUN_CAPS = { usdList: 10, seconds: 14400 } as const;

// results/baseline-flagships-1/README.md table; results/*/README.md run tables for the other arms;
// results/counterexamples-1/summary.json for the refutations.
export const COMPARISON: ComparisonRow[] = [
  {
    key: "cetus",
    task: "rw-cetus-shlw",
    incident: "Cetus",
    year: 2025,
    requirements: 5,
    alone: { arm: "A0", runs: ["results/baseline-flagships-1/rw-cetus-shlw/A0-1", "results/baseline-flagships-1/rw-cetus-shlw/A0-2"], accepted: 2 },
    harness: [{ arm: "A1", runs: ["results/cetus-1/repair-A1-1"], accepted: 1 }],
    implement: { arm: "A1", runs: ["results/implement-flagships-1/rw-cetus-shlw"], accepted: 1 },
    refutations: [
      { target: "cetus-original-port", label: "original code", refuted: 2, kernelChecked: 2 },
      { target: "cetus-pr6-port", label: "same-day hotfix", refuted: 1, kernelChecked: 1 },
    ],
    library: null,
  },
  {
    key: "euler",
    task: "rw-euler-donate",
    incident: "Euler Finance",
    year: 2023,
    requirements: 6,
    alone: { arm: "A0", runs: ["results/baseline-flagships-1/rw-euler-donate/A0-1", "results/baseline-flagships-1/rw-euler-donate/A0-2"], accepted: 2 },
    harness: [{ arm: "A1", runs: ["results/euler-1/rw-euler-donate/repair-A1-1"], accepted: 1 }],
    implement: { arm: "A1", runs: ["results/implement-flagships-1/rw-euler-donate"], accepted: 1 },
    refutations: [{ target: "euler-port", label: "vulnerable port", refuted: 3, kernelChecked: 3 }],
    library: null,
  },
  {
    key: "hundred",
    task: "rw-hundred-vault",
    incident: "Hundred Finance",
    year: 2023,
    requirements: 10,
    alone: { arm: "A0", runs: ["results/baseline-flagships-1/rw-hundred-vault/A0-1", "results/baseline-flagships-1/rw-hundred-vault/A0-2"], accepted: 2 },
    harness: [{ arm: "A1", runs: ["results/vault-1/repair-A1-1"], accepted: 1 }],
    implement: { arm: "A1", runs: ["results/implement-flagships-1/rw-hundred-vault"], accepted: 1 },
    // counterexamples-1/README.md: the other three need a proof about the candidate's code, not an evaluation
    refutations: [{ target: "rw-hundred-vault-start", label: "vulnerable port", refuted: 5, kernelChecked: 2 }],
    library: null,
  },
  {
    key: "balancer",
    task: "rw-balancer-upscale",
    incident: "Balancer V2",
    year: 2025,
    requirements: 8,
    alone: { arm: "A0", runs: ["results/baseline-flagships-1/rw-balancer-upscale/A0-1", "results/baseline-flagships-1/rw-balancer-upscale/A0-2"], accepted: 1 },
    harness: [
      { arm: "A1", runs: ["results/balancer-1/repair-A1-1", "results/balancer-1/repair-A1-2"], accepted: 1 },
      { arm: "A2", runs: ["results/balancer-1/repair-A2-1"], accepted: 1 },
    ],
    implement: { arm: "A1", runs: ["results/balancer-1/implement-1", "results/balancer-1/implement-2"], accepted: 1 },
    refutations: [{ target: "balancer-port", label: "deployed swap path", refuted: 3, kernelChecked: 3 }],
    library: {
      source: "results/library-1",
      alone: {
        arm: "A0",
        runs: ["results/library-1/rw-balancer-upscale/A0-1", "results/library-1/rw-balancer-upscale/A0-2", "results/library-1/rw-balancer-upscale/A0-3"],
        accepted: 1,
      },
      withLibrary: { arm: "A2", runs: ["results/library-1/rw-balancer-upscale/A2-1", "results/library-1/rw-balancer-upscale/A2-2"], accepted: 2 },
      topdown: null,
    },
  },
  {
    key: "knight",
    task: "rc-knight-router",
    incident: "Knight Capital",
    year: 2012,
    requirements: 6,
    alone: { arm: "A0", runs: ["results/baseline-flagships-1/rc-knight-router/A0-1", "results/baseline-flagships-1/rc-knight-router/A0-2"], accepted: 1 },
    harness: [
      { arm: "A1", runs: ["results/knight-1/A1-1", "results/knight-1/A1-2"], accepted: 0 },
      { arm: "A2", runs: ["results/knight-1/A2-1", "results/knight-1/A2-2"], accepted: 1 },
    ],
    implement: { arm: "A2", runs: ["results/implement-flagships-1/rc-knight-router-A2-1"], accepted: 1 },
    refutations: [{ target: "knight-start", label: "reconstructed router", refuted: 6, kernelChecked: 6 }],
    library: {
      source: "results/library-1",
      alone: null,
      withLibrary: { arm: "A2", runs: ["results/library-1/rc-knight-router/A2-1", "results/library-1/rc-knight-router/A2-2"], accepted: 2 },
      topdown: null,
    },
  },
  {
    key: "compound",
    task: "rw-compound-comp",
    incident: "Compound Proposal 62",
    year: 2021,
    requirements: 8,
    // baseline-flagships-1/README.md: both of its runs ended early on a per-call timeout treated as a
    // wall stop; the two library-1 runs ran the full 14,400 s
    alone: { arm: "A0", runs: ["results/baseline-flagships-1/rw-compound-comp/A0-1", "results/baseline-flagships-1/rw-compound-comp/A0-2"], accepted: 0 },
    harness: [
      { arm: "A1", runs: ["results/compound-1/repair-A1-1", "results/compound-1/repair-A1-2"], accepted: 0 },
      { arm: "A2", runs: ["results/compound-1/repair-A2-1", "results/compound-1/repair-A2-2"], accepted: 0 },
    ],
    implement: { arm: "A1", runs: ["results/compound-1/implement-1", "results/compound-1/implement-2"], accepted: 0 },
    refutations: [{ target: "compound-p62-port", label: "Proposal 62 port", refuted: 5, kernelChecked: 5 }],
    library: {
      source: "results/library-1",
      alone: { arm: "A0", runs: ["results/library-1/rw-compound-comp/A0-1", "results/library-1/rw-compound-comp/A0-2"], accepted: 0 },
      withLibrary: { arm: "A2", runs: ["results/library-1/rw-compound-comp/A2-1", "results/library-1/rw-compound-comp/A2-2"], accepted: 0 },
      topdown: {
        arm: "A2",
        runs: ["results/library-1/rw-compound-comp/A2-topdown-1", "results/library-1/rw-compound-comp/A2-topdown-2", "results/library-1/rw-compound-comp/A2-topdown-3"],
        accepted: 0,
      },
    },
  },
];

/** The library comparison; its runs are in the `library` field of the COMPARISON rows for these tasks. */
export const LIBRARY_RUN = {
  source: "results/library-1",
  tasks: ["rw-compound-comp", "rc-knight-router", "rw-balancer-upscale"],
  what: "Muse with ProofForge and the ProofForgeFin library against Muse alone",
} as const;

/**
 * The library-1 runs with the library on Compound (orchestrated and top-down): the most requirements
 * any final snapshot proved (summary.json final_status), and how many of them proved one of the three
 * sequence bounds that the build team's library proof closes.
 */
export const LIBRARY_COMPOUND = {
  bestProved: 4,
  bounds: ["req_rewards_bounded", "req_account_bounded", "req_no_backdated"],
  runsProvingABound: 0,
} as const;

/** Every Muse-alone run of a COMPARISON row: baseline-flagships-1 and library-1. */
export const aloneRuns = (row: ComparisonRow): Runs => merge("A0", [row.alone, row.library?.alone ?? null]);

/** Every run with the Muse Wonder planner (A2) of a COMPARISON row, with and without the library, on either loop. */
export const plannerRuns = (row: ComparisonRow): Runs | null => {
  const parts = [...row.harness.filter((h) => h.arm === "A2"), row.library?.withLibrary ?? null, row.library?.topdown ?? null];
  return parts.some((p) => p) ? merge("A2", parts) : null;
};

function merge(arm: Runs["arm"], parts: (Runs | null)[]): Runs {
  const xs = parts.filter((p): p is Runs => p !== null);
  return { arm, runs: xs.flatMap((p) => p.runs), accepted: xs.reduce((n, p) => n + p.accepted, 0) };
}

/**
 * Muse alone against Muse with ProofForge and the Muse Wonder planner, on the tasks where both were
 * accepted at least once, over every measured run at the same caps (aloneRuns and plannerRuns).
 * List dollars are summary.json budget.usd_list summed over all runs, verified or not, and divided
 * by the verified runs; tests/contribution.test.ts recomputes every figure, including the
 * one-sided Fisher exact test on the verification rate.
 */
export const COST_PER_VERIFIED = [
  // results/library-1/README.md, "Balancer across all measured runs"
  {
    key: "balancer",
    incident: "Balancer",
    alone: { verified: 2, runs: 5, usdList: 40.04, usdPerVerified: 20.02 },
    planner: { verified: 3, runs: 3, usdList: 9.18, usdPerVerified: 3.06 },
    fisherOneSidedP: 0.18,
  },
  {
    key: "knight",
    incident: "Knight Capital",
    alone: { verified: 1, runs: 2, usdList: 16.22, usdPerVerified: 16.22 },
    planner: { verified: 3, runs: 4, usdList: 26.54, usdPerVerified: 8.85 },
    fisherOneSidedP: 0.6,
  },
] as const;

/** results/spec-strength-1/summary.json total; docs/SPEC_STRENGTH.md describes the gate. */
export const SPEC_STRENGTH = {
  source: "results/spec-strength-1",
  doc: "docs/SPEC_STRENGTH.md",
  // summary.json: one task per locked specification
  specifications: 25,
  // README: "the 25 runs cover all 68 tasks"
  tasksCovered: 68,
  mutants: 1676,
  compiled: 1114,
  rejected: 999,
  kernelChecked: 730,
  // survivors whose outputs differ from the reference's while the property tests accept them
  survivedDiffers: 10,
  survivedSame: 105,
} as const;

/** results/counterexamples-1/summary.json and README.md. */
export const COUNTEREXAMPLES = {
  source: "results/counterexamples-1/summary.json",
  candidates: 33,
  refuted: 85,
  kernelChecked: 82,
  // README: "took 6.6 s to 17.4 s, median 11.4 s"
  medianSeconds: 11.4,
} as const;

/** The same-day Cetus hotfix and its kernel-checked counterexample (results/counterexamples-1/cetus-pr6-port). */
export const CETUS_HOTFIX = {
  passport: "results/counterexamples-1/cetus-pr6-port/passport.json",
  requirement: "REQ-SHLW-EXACT",
  // cex input n, which is 2^192
  input: "6277101735386680763835789423207666416102355444464034512896",
  statement: "¬ (ShlwExact checkedShlw)",
  kernels: 6,
} as const;

/** Open-weight Muse models on the 30 frozen E1 test tasks, arms A0 and A1, $3 and 3,600 s per run. */
export interface OpenWeightRun {
  key: string;
  model: string;
  serving: string;
  source: string;
  /** Tasks with both arms scored. */
  paired: number;
  a0: { completed: number; n: number };
  a1: { completed: number; n: number };
  /** Runs whose rebuilt executable passed the property tests. */
  binaryPass: { a0: number; a1: number };
  /** 95% interval of the A1 minus A0 completion rate, bootstrap over base specifications. */
  ci95: [number, number];
  mcnemarP: number;
  complete: boolean;
  /** For an incomplete run: runs ended by the outage, excluded from the README's counts. */
  outage: { runs: string[]; a1Completed: number; a1N: number } | null;
}

export const OPEN_WEIGHTS: OpenWeightRun[] = [
  {
    key: "spark-open",
    model: "Muse Spark Open",
    serving: "meta-models/muse-spark-open-1026 on Baseten Model APIs",
    source: "results/e1-test-open-1/e1.json",
    paired: 30,
    a0: { completed: 21, n: 30 },
    a1: { completed: 24, n: 30 },
    binaryPass: { a0: 21, a1: 30 },
    ci95: [-0.172, 0.379],
    mcnemarP: 0.51,
    complete: true,
    outage: null,
  },
  {
    key: "glimmer",
    model: "Muse Glimmer 30B",
    serving: "self-hosted with vLLM on one Modal H100",
    source: "results/e1-test-glimmer-1/e1.json",
    paired: 15,
    a0: { completed: 0, n: 15 },
    a1: { completed: 3, n: 16 },
    binaryPass: { a0: 0, a1: 15 },
    ci95: [0, 0.389],
    mcnemarP: 0.25,
    complete: false,
    // e1-test-glimmer-1/README.md: three A1 runs ended by the Modal outage
    outage: { runs: ["permissions-grants-b1/A1", "permissions-grants-b2/A1", "permissions-grants-b3/A1"], a1Completed: 3, a1N: 13 },
  },
];

/** Muse Wonder 1.0 as lemma planner (arm A2) against the harness alone (A1) on the two hardest tasks. */
export const PLANNER = [
  // compound-1/README.md: A1 runs proved 0 of 8, A2 runs 5 of 8 (the five per-call requirements)
  { task: "rw-compound-comp", incident: "Compound", requirements: 8, a1: [0, 0], a2: [5, 5], a2Accepted: 0 },
  // knight-1/README.md: A1 1 of 6 twice; A2 5 of 6, then 6 of 6 VERIFIED
  { task: "rc-knight-router", incident: "Knight Capital", requirements: 6, a1: [1, 1], a2: [5, 6], a2Accepted: 1 },
] as const;

/** ProofForgeFin (lib/), counted from the sources; lib/README.md states the kernel check. */
export const LIBRARY = {
  // declarations in lib/ProofForgeFin/**/*.lean, comments excluded (tests/contribution.test.ts recounts)
  files: 74,
  theorems: 1869,
  definitions: 449,
  // lib/ProofForgeFinDemo/**/*.lean
  demoTheorems: 329,
  // lib/README.md: "all 10,128 safe constants of the library and the demonstrations ... pass all six kernels"
  constantsChecked: 10128,
  modulesReplayed: 87,
  // tests/fixtures/library/compound_lib.lean: implementation and per-call proofs from the reference
  // solution, the three sequence bounds from lib/ProofForgeFinDemo/DeFi/Compound.lean
  compoundFixture: "tests/fixtures/library/compound_lib.lean",
  compoundFixtureSha256: "aa13206eeb42f4f19646a742efe4c2dc79c3b2c6dcc3f0418eeb02942feffb54",
  // Issued by the deployed judge (POST /api/verify) and committed with its candidate in results/library-live-1.
  compoundLivePassport: "b654d456e1a5eec1057ee259be2c2726fee3a4d3b89d1373dcc3bcbf1c4b7f59",
  compoundLivePassportFile: "results/library-live-1/passport.json",
} as const;

/** ORIGIN.md and the first commit of the repository (535b942, 2026-10-26 19:43 -04:00). */
export const HACKATHON = {
  event: "Meta Global AI Developer Hackathon",
  firstCommit: "2026-10-26",
  submissionsDue: "2026-11-04",
} as const;

export const SCOPE =
  "ProofForge proves the logic of code against a written specification. It does not protect keys, servers, oracles, bridges or other infrastructure, and it does not prove the deployed Solidity or Move bytecode itself.";

/** Sum over runs. */
export const total = (xs: readonly Runs[]) => xs.reduce((n, r) => ({ accepted: n.accepted + r.accepted, runs: n.runs + r.runs.length }), { accepted: 0, runs: 0 });
