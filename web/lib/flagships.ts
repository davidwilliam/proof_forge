// The real incidents shown on the home page. Every figure is copied from the committed file
// named beside it: loss figures and their citations from the task README, everything else
// from result JSON. tests/flagships.test.ts recomputes every machine-derivable figure (Passport
// hashes and statuses, requirement statuses, reproduction commands, run costs, input and
// sequence counts, violation counts, attack amounts) from those files, and
// scripts/evidence.mjs publishes the same data as public/evidence.json and public/llms.txt.
//
// This module has no runtime imports, so scripts/evidence.mjs can load it on its own.
// A further incident is added by appending a Flagship to FLAGSHIPS; the home page, the
// scoreboard and the published evidence pick it up without code changes.

export type Verdict = "VERIFIED" | "REFUTED" | "UNRESOLVED";

export const REPO_URL = "https://github.com/davidwilliam/proof_forge";
/** A committed file on GitHub. The API serves only Passports issued by the live service, not these. */
export const githubFile = (rel: string) => `${REPO_URL}/blob/main/${rel}`;

export interface Citation {
  label: string;
  url: string;
}

export interface PassportRef {
  /** Repository-relative path of the Passport JSON. */
  path: string;
  /** passport_sha256 as recorded; the test recomputes it from the file. */
  sha256: string;
  status: Verdict;
  /** Requirement id to status, as recorded in the Passport. */
  requirements: Record<string, string>;
  /** The Passport's "reproduce" field. */
  reproduce: string;
}

export interface CodeVersion {
  key: string;
  /** Who wrote this version and when, in a few words. */
  title: string;
  detail: string;
  /** Upstream commit, or null for a version that is not upstream code. */
  commit: string | null;
  /** When the version was merged upstream (ISO 8601), if it was. */
  merged: string | null;
  /** The deciding lines, as the task README quotes them. */
  code: string[];
  verdict: Verdict;
  passport: PassportRef;
  /** What the kernel-checked counterexample or proof shows, in one or two sentences. */
  finding: string;
  /** The finding in one short sentence, for the first screen. */
  short: string;
}

export interface AttackStep {
  text: string;
  /** State after the step, when the model tracks it. */
  after?: string;
}

export interface RealCodeRow {
  label: string;
  /** Upstream commit, or null for a local variant. */
  commit: string | null;
  /** Inputs or sequences on which this code breaks a requirement. */
  violating: number;
  /** Inputs or sequences on which this code's output equals its Lean port's (null when not compared). */
  sameAsPort: number | null;
  /** Inputs or sequences on which this code's output equals the proved Muse repair's. */
  sameAsProved: number | null;
  note: string;
}

export interface UnresolvedRun {
  /** Run directory with summary.json and passport.json. */
  run: string;
  label: string;
  /** Required theorems proved in the session, of the task's total. */
  proved: number;
  /** What stopped the run. */
  stop: string;
  passport: PassportRef;
}

export interface Flagship {
  key: string;
  /** Task directory. */
  task: string;
  incident: string;
  year: number;
  date: string;
  /** What was attacked, in a few words. */
  system: string;
  /** Domain, in two or three words, for the overview table. */
  domain: string;
  /** Language of the real code; null when the code is not public. */
  language: "Move" | "Solidity" | null;
  loss: {
    /** As the task README states it. */
    amount: string;
    /** The amount in millions of US dollars, rounded down; the total on the home page sums these. */
    usdMillions: number;
    /** What the amount measures, in two or three words; reads after the amount. */
    short: string;
    /** What the amount measures and who reports it; reads after the amount. */
    basis: string;
    citations: Citation[];
  };
  /** The bug in one sentence. */
  bug: string;
  /** The main property proved, in one plain sentence. */
  property: string;
  propertyId: string;
  vulnerable: {
    label: string;
    verdict: "REFUTED";
    /** Passport of the vulnerable port, when one was issued. */
    passport: PassportRef | null;
    /** Kernel-checked counterexample file. */
    witness: string;
    finding: string;
  };
  repair: {
    model: "Muse Spark 1.3";
    /** Repair arm and tier, as the run records them. A2 adds Muse Wonder 1.0 as planner. */
    arm: "A1" | "A2";
    planner: "Muse Wonder 1.0" | null;
    tier: "Contributor";
    /** Attempt on which the repair was accepted. */
    attempt: number;
    verdict: "VERIFIED";
    passport: PassportRef;
    /** Run directory with summary.json. */
    run: string;
    seconds: number;
    usdList: number;
    usdCharged: number;
    calls: number;
    /** Output of bin/proofforge verify on the Passport. */
    verifyLog: string;
    kernels: number;
    propertyCases: number;
    change: string;
  };
  /** Earlier attempts on the same task that ended without a Passport. */
  unresolved: UnresolvedRun[];
  /** Null when the real code is not public. */
  realCode: {
    /** One line for the scoreboard: what real code ran, on how much. */
    short: string;
    /** The outcome in a few words; every number in it is a row figure or the total. */
    result: string;
    report: string;
    unit: "inputs" | "sequences" | "batches";
    total: number;
    how: string;
    rows: RealCodeRow[];
    confirmedInLean: { goals: number; checked: number };
  } | null;
  /** The attack as a numbered sequence, for incidents told as cards. */
  attack: AttackStep[];
  /** What the kernel checks about the attack on the vulnerable port. */
  outcome: string;
  /** One sourced sentence of context for the case card, or null. */
  context: string | null;
  /** Versions of the code with their verdicts, for the featured incident. */
  timeline: CodeVersion[];
  /** A theorem relating the Muse repair to the upstream fix, when one was proved. */
  equivalence: { file: string; theorem: string; axioms: string; output: string } | null;
  /** What this incident's evidence does not establish. */
  limits: string[];
  /** Additional limit shown in the claims block, for example how the incident was reconstructed. */
  reconstruction: string | null;
}

const CETUS_TASK = "realworld/tasks/rw-cetus-shlw";
const EULER_TASK = "realworld/tasks/rw-euler-donate";
const HUNDRED_TASK = "realworld/tasks/rw-hundred-vault";
const BALANCER_TASK = "realworld/tasks/rw-balancer-upscale";
const KNIGHT_TASK = "realworld/tasks/rc-knight-router";

// realworld/tasks/rw-cetus-shlw/README.md, results/cetus-1/
const cetus: Flagship = {
  key: "cetus",
  task: CETUS_TASK,
  incident: "Cetus",
  year: 2025,
  // README: "On 2025-05-22 an attacker drained the concentrated-liquidity pools of Cetus, a DEX on Sui."
  date: "2025-05-22",
  system: "concentrated-liquidity pools of Cetus, a DEX on Sui",
  domain: "DEX liquidity math",
  language: "Move",
  loss: {
    // README: "The Block reports, from Cetus's incident report, that about $223 million was taken"
    amount: "about $223 million",
    usdMillions: 223,
    short: "taken",
    basis: "taken, as The Block reports from Cetus's incident report",
    citations: [
      { label: "The Block", url: "https://www.theblock.co/post/355795/sui-dex-cetus-open-source-library-flaw-smart-contract-223-million-usd-exploit" },
      { label: "Dedaub", url: "https://dedaub.com/blog/the-cetus-amm-200m-hack-how-a-flawed-overflow-check-led-to-catastrophic-loss/" },
    ],
  },
  bug: "The overflow check in checked_shlw tested against a 256-bit limit instead of a 192-bit limit, so a shift that lost bits reported no overflow.",
  property: "The overflow check never loses a bit, so a deposit is always charged at least the exact amount it owes.",
  propertyId: "REQ-DELTA-A-COVERS",
  vulnerable: {
    label: "Original checked_shlw",
    verdict: "REFUTED",
    passport: {
      path: "results/cetus-1/passports/original-port.json",
      sha256: "b79e965381258ef8a287983b492911da0c4dc7b7437bfc538c14ad196aadfad3",
      status: "REFUTED",
      requirements: {
        "REQ-SHLW-COMPLETE": "UNRESOLVED",
        "REQ-SHLW-EXACT": "REFUTED",
        "REQ-DELTA-A-FLOOR": "UNRESOLVED",
        "REQ-DELTA-A-TIGHT": "UNRESOLVED",
        "REQ-DELTA-A-COVERS": "REFUTED",
      },
      reproduce: "bin/proofforge verify results/cetus-1/passports/original-port.json --candidate realworld/tasks/rw-cetus-shlw/attacks/buggy_original.lean",
    },
    witness: `${CETUS_TASK}/witnesses/buggy_original.lean`,
    // results/cetus-1/real-code/report.json versions.original.witnesses[0].message
    finding: "On the attack deposit it charges 1 unit of token A; the exact amount owed, rounded up, is 31572840708638430117170542 units.",
  },
  repair: {
    model: "Muse Spark 1.3",
    arm: "A1",
    planner: null,
    tier: "Contributor",
    attempt: 1,
    verdict: "VERIFIED",
    passport: {
      path: "results/cetus-1/repair-A1-1/passport.json",
      sha256: "9131dfdfd3e27da8145cd70972c65748a5447585ce2c625dee404b1506239852",
      status: "VERIFIED",
      requirements: {
        "REQ-SHLW-COMPLETE": "VERIFIED",
        "REQ-SHLW-EXACT": "VERIFIED",
        "REQ-DELTA-A-FLOOR": "VERIFIED",
        "REQ-DELTA-A-TIGHT": "VERIFIED",
        "REQ-DELTA-A-COVERS": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/cetus-1/repair-A1-1/passport.json --candidate results/cetus-1/repair-A1-1/final.lean",
    },
    run: "results/cetus-1/repair-A1-1",
    // results/cetus-1/repair-A1-1/summary.json budget: elapsed_s 427.7, usd_list 0.1871, usd_actual 0.0111, 23 calls
    seconds: 428,
    usdList: 0.19,
    usdCharged: 0.011,
    calls: 23,
    verifyLog: "results/cetus-1/repair-A1-1/verify.txt",
    kernels: 6,
    propertyCases: 2001,
    // README: "Its fix tests `n.toNat * 2 ^ 64 < 2 ^ 256` directly"
    change: "tests n * 2^64 < 2^256 directly",
  },
  unresolved: [],
  realCode: {
    short: "real Move code at 3 pinned commits, 2,007 inputs",
    result: "658 break a requirement on the original, 0 on the final fix",
    report: "results/cetus-1/real-code/report.json",
    unit: "inputs",
    total: 2007,
    // README: "run with Sui CLI 1.83.0 (`sui move test`) on 2007 inputs, the 7 documented values plus 2000 generated"
    how: "The real checked_shlw and get_delta_a, unmodified at each pinned commit, ran with Sui CLI 1.83.0 (sui move test) on 2,007 inputs: 7 documented values and 2,000 generated by the task oracle.",
    rows: [
      { label: "Original", commit: "4d09c8ba0527274983c6664a5d5def2e784d4692", violating: 658, sameAsPort: 2007, sameAsProved: 1317, note: "the attack deposit returns 1" },
      { label: "Pull request 6", commit: "fc84a51c29fabfbfbdb8ed76506b61a07493d492", violating: 33, sameAsPort: 2007, sameAsProved: 1974, note: "32 of them at n = 2^192" },
      { label: "Pull request 7", commit: "06660f704c4ac1d443ab62346a46b5b60d49df33", violating: 0, sameAsPort: 2007, sameAsProved: 2007, note: "identical to the Muse repair on every input" },
    ],
    confirmedInLean: { goals: 9, checked: 9 },
  },
  attack: [],
  outcome: "",
  context: null,
  timeline: [
    {
      key: "original",
      title: "Original code",
      detail: "integer-mate at 4d09c8b, the last commit before the fixes",
      commit: "4d09c8ba0527274983c6664a5d5def2e784d4692",
      merged: null,
      code: ["mask = 0xffffffffffffffff << 192", "n > mask"],
      verdict: "REFUTED",
      passport: {
        path: "results/cetus-1/passports/original-port.json",
        sha256: "b79e965381258ef8a287983b492911da0c4dc7b7437bfc538c14ad196aadfad3",
        status: "REFUTED",
        requirements: {
          "REQ-SHLW-COMPLETE": "UNRESOLVED",
          "REQ-SHLW-EXACT": "REFUTED",
          "REQ-DELTA-A-FLOOR": "UNRESOLVED",
          "REQ-DELTA-A-TIGHT": "UNRESOLVED",
          "REQ-DELTA-A-COVERS": "REFUTED",
        },
        reproduce: "bin/proofforge verify results/cetus-1/passports/original-port.json --candidate realworld/tasks/rw-cetus-shlw/attacks/buggy_original.lean",
      },
      finding: "The attack deposit is charged 1 unit of token A. The exact amount owed, rounded up, is 31572840708638430117170542 units, about 3.16 × 10^25.",
      short: "Charges the attack deposit 1 unit of token A; it owed about 3.16 × 10^25.",
    },
    {
      key: "pr6",
      title: "Same-day hotfix",
      // results/cetus-1/real-code/report.json versions.pr6.note: "merged 2025-05-22T14:37:30Z"
      detail: "pull request 6, merged 14:37 UTC",
      commit: "fc84a51c29fabfbfbdb8ed76506b61a07493d492",
      merged: "2025-05-22T14:37:30Z",
      code: ["mask = 1 << 192", "n > mask"],
      verdict: "REFUTED",
      passport: {
        path: "results/cetus-1/passports/pr6-port.json",
        sha256: "d489c01595c307394d75579753303817724f7d586cffd2b7bb3b8cfe83f5e3e2",
        status: "REFUTED",
        requirements: {
          "REQ-SHLW-COMPLETE": "UNRESOLVED",
          "REQ-SHLW-EXACT": "REFUTED",
          "REQ-DELTA-A-FLOOR": "UNRESOLVED",
          "REQ-DELTA-A-TIGHT": "UNRESOLVED",
          "REQ-DELTA-A-COVERS": "UNRESOLVED",
        },
        reproduce: "bin/proofforge verify results/cetus-1/passports/pr6-port.json --candidate realworld/tasks/rw-cetus-shlw/attacks/pr6_mask_only.lean",
      },
      finding: "It refuses the attack deposit, but checkedShlw(2^192) = (0, false): 2^192 shifted left by 64 bits wraps to 0 and no overflow is reported. A deposit with liquidity × price difference = 2^192 is charged 0.",
      short: "Stops the attack input, but checkedShlw(2^192) = (0, false): the shift wraps to 0 and reports no overflow.",
    },
    {
      key: "pr7",
      title: "Final fix",
      // results/cetus-1/real-code/report.json versions.pr7.note: "merged 2025-05-22T16:09:27Z"
      detail: "pull request 7, merged 16:09 UTC",
      commit: "06660f704c4ac1d443ab62346a46b5b60d49df33",
      merged: "2025-05-22T16:09:27Z",
      code: ["mask = 1 << 192", "n >= mask"],
      verdict: "VERIFIED",
      passport: {
        path: "results/cetus-1/passports/pr7-port.json",
        sha256: "37d236fb45a80f418f9cfd7b63296b25c6326bb4a8517b86f8b7e806cdfa5e48",
        status: "VERIFIED",
        requirements: {
          "REQ-SHLW-COMPLETE": "VERIFIED",
          "REQ-SHLW-EXACT": "VERIFIED",
          "REQ-DELTA-A-FLOOR": "VERIFIED",
          "REQ-DELTA-A-TIGHT": "VERIFIED",
          "REQ-DELTA-A-COVERS": "VERIFIED",
        },
        reproduce: "bin/proofforge verify results/cetus-1/passports/pr7-port.json --candidate realworld/tasks/rw-cetus-shlw/reference/SolutionA.lean",
      },
      finding: "All five requirements proved for every 256-bit input and every u128 price and liquidity.",
      short: "All five requirements proved for every 256-bit input.",
    },
    {
      key: "muse",
      title: "Muse Spark repair",
      detail: "from the original code, accepted on the first attempt",
      commit: null,
      merged: null,
      code: ["n * 2^64 < 2^256"],
      verdict: "VERIFIED",
      passport: {
        path: "results/cetus-1/repair-A1-1/passport.json",
        sha256: "9131dfdfd3e27da8145cd70972c65748a5447585ce2c625dee404b1506239852",
        status: "VERIFIED",
        requirements: {
          "REQ-SHLW-COMPLETE": "VERIFIED",
          "REQ-SHLW-EXACT": "VERIFIED",
          "REQ-DELTA-A-FLOOR": "VERIFIED",
          "REQ-DELTA-A-TIGHT": "VERIFIED",
          "REQ-DELTA-A-COVERS": "VERIFIED",
        },
        reproduce: "bin/proofforge verify results/cetus-1/repair-A1-1/passport.json --candidate results/cetus-1/repair-A1-1/final.lean",
      },
      // results/cetus-1/repair-A1-1/Equivalence.lean, theorem muse_eq_pr7; Equivalence.out.txt
      finding: "All five requirements proved. A separate theorem, muse_eq_pr7, proves it returns the same value and overflow flag as the final fix on every 256-bit input.",
      short: "All five proved, and proved equal to pull request 7 on every 256-bit input.",
    },
  ],
  // results/cetus-1/repair-A1-1/Equivalence.lean and Equivalence.out.txt
  equivalence: {
    file: "results/cetus-1/repair-A1-1/Equivalence.lean",
    theorem: "theorem muse_eq_pr7 : ∀ n : BitVec 256, museShlw n = pr7Shlw n",
    axioms: "propext, Quot.sound",
    output: "results/cetus-1/repair-A1-1/Equivalence.out.txt",
  },
  limits: [
    "The Move code is run on 2,007 inputs and compared with the Lean ports and the proved component; it is not itself proved.",
    "get_delta_b, the tick math and the rest of the pool (positions, swaps, fees) are not specified.",
  ],
  reconstruction: null,
};

// realworld/tasks/rw-euler-donate/README.md, results/euler-1/rw-euler-donate/
const euler: Flagship = {
  key: "euler",
  task: EULER_TASK,
  incident: "Euler Finance",
  year: 2023,
  // README: "On 13 March 2023 an attacker took about $197M in net profit from Euler Finance v1 (Cyfrin)"
  date: "2023-03-13",
  system: "Euler Finance v1 lending market",
  domain: "lending solvency",
  language: "Solidity",
  loss: {
    amount: "about $197 million",
    usdMillions: 197,
    short: "in net profit to the attacker",
    basis: "in net profit to the attacker, as Cyfrin reports; CoinDesk later reported that all recoverable funds were returned",
    citations: [
      { label: "Cyfrin", url: "https://www.cyfrin.io/blog/how-did-the-euler-finance-hack-happen-hack-analysis" },
      { label: "Zellic", url: "https://www.zellic.io/blog/euler-finance-exploit-analysis" },
      { label: "CoinDesk", url: "https://www.coindesk.com/business/2023/04/03/euler-says-all-recoverable-funds-stolen-in-200m-hack-have-been-returned" },
    ],
  },
  bug: "donateToReserves moved an account's collateral to the reserves without the liquidity check that withdraw, mint and transfer perform.",
  property: "No sequence of operations leaves any account with more debt than its risk-adjusted collateral.",
  propertyId: "REQ-NO-BAD-DEBT",
  vulnerable: {
    label: "Euler v1 at b1ee326",
    verdict: "REFUTED",
    passport: {
      path: "results/euler-1/rw-euler-donate/passports/port.json",
      sha256: "cec7d847f1d0b6a6f9cdb0e46fd149430807f86e14ce746054484ccee3a3a050",
      status: "REFUTED",
      requirements: {
        "REQ-HONEST-FLOW": "UNRESOLVED",
        "REQ-ALLOWED-SUCCEEDS": "UNRESOLVED",
        "REQ-EFFECTS": "UNRESOLVED",
        "REQ-ACTOR-HEALTHY": "REFUTED",
        "REQ-STAYS-HEALTHY": "REFUTED",
        "REQ-NO-BAD-DEBT": "REFUTED",
      },
      reproduce: "bin/proofforge verify results/euler-1/rw-euler-donate/passports/port.json --candidate realworld/tasks/rw-euler-donate/candidate/Solution.lean",
    },
    witness: `${EULER_TASK}/witnesses/buggy_original.lean`,
    finding: "The attack sequence leaves 134,000,000 of debt with no collateral behind it.",
  },
  repair: {
    model: "Muse Spark 1.3",
    arm: "A1",
    planner: null,
    tier: "Contributor",
    attempt: 1,
    verdict: "VERIFIED",
    passport: {
      path: "results/euler-1/rw-euler-donate/repair-A1-1/passport.json",
      sha256: "6de7bb94c38cf23a31ba08174d7505b4b8d54dddc9ffbd6d177dde4981b82002",
      status: "VERIFIED",
      requirements: {
        "REQ-HONEST-FLOW": "VERIFIED",
        "REQ-ALLOWED-SUCCEEDS": "VERIFIED",
        "REQ-EFFECTS": "VERIFIED",
        "REQ-ACTOR-HEALTHY": "VERIFIED",
        "REQ-STAYS-HEALTHY": "VERIFIED",
        "REQ-NO-BAD-DEBT": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/euler-1/rw-euler-donate/repair-A1-1/passport.json --candidate results/euler-1/rw-euler-donate/repair-A1-1/final.lean",
    },
    run: "results/euler-1/rw-euler-donate/repair-A1-1",
    // results/euler-1/rw-euler-donate/repair-A1-1/summary.json budget: elapsed_s 1681.9, usd_list 0.8324, usd_actual 0.0489, 40 calls
    seconds: 1682,
    usdList: 0.83,
    usdCharged: 0.05,
    calls: 40,
    verifyLog: "results/euler-1/rw-euler-donate/repair-A1-1/verify.txt",
    kernels: 6,
    propertyCases: 2001,
    // README: "The repair adds `Healthy a` to the donation guard, the same check as the reference"
    change: "adds the health check to the donation guard",
  },
  unresolved: [],
  realCode: {
    short: "real Solidity contracts at the pinned commit, 1,004 sequences",
    result: "57 break a requirement unmodified, 0 with the missing check added",
    report: "results/euler-1/rw-euler-donate/real-code/report.json",
    unit: "sequences",
    total: 1004,
    how: "The unmodified contracts at b1ee326 were deployed in a local Foundry test and run on the attack, Euler's three donate test scenarios and 1,000 generated sequences, then compared after every operation with the requirements, with Euler's own liquidity computation and with the Muse repair.",
    rows: [
      { label: "Euler v1 at b1ee326, unmodified", commit: "b1ee3265853628d5a529081d7908c38404201b4e", violating: 57, sameAsPort: null, sameAsProved: 947, note: "Euler's own liquidity check also reports collateral below liability in 57" },
      { label: "The same with checkLiquidity(account) added", commit: null, violating: 0, sameAsPort: null, sameAsProved: 1004, note: "a local copy, not an upstream release" },
    ],
    confirmedInLean: { goals: 2, checked: 2 },
  },
  // README table "The vulnerable port and its refutation"; amounts in whole DAI at an exchange rate of 1
  attack: [
    { text: "A lender deposits 8,904,507." },
    { text: "The violator deposits 20,000,000, then mints 200,000,000, repays 10,000,000 and mints 200,000,000.", after: "collateral 420,000,000, debt 390,000,000: healthy" },
    { text: "The violator donates 100,000,000 eTokens to the reserves. No liquidity check runs.", after: "collateral 320,000,000, debt 390,000,000: unhealthy" },
    { text: "A second attacker account liquidates 256,000,000 of the debt at the 20% maximum discount.", after: "violator: collateral 0, debt 134,000,000" },
    { text: "The liquidator withdraws the whole pool, 38,904,507: the lender's entire deposit." },
  ],
  context: null,
  outcome: "The kernel checks every state above and that NoBadDebt, StaysHealthy and ActorHealthy are false for the port: 134,000,000 of debt is left with no collateral behind it.",
  timeline: [],
  equivalence: null,
  limits: [
    "One asset priced at 1, an eToken exchange rate fixed at 1 and no interest; flash loans, sub-accounts and multiple collateral assets are not modeled.",
    "The contracts are run on 1,004 sequences and compared with the requirements and the proved component; they are not themselves proved.",
  ],
  reconstruction: null,
};

// realworld/tasks/rw-hundred-vault/README.md, results/vault-1/
const hundred: Flagship = {
  key: "hundred",
  task: HUNDRED_TASK,
  incident: "Hundred Finance",
  year: 2023,
  // README: "its hWBTC market on Optimism was drained on 2023-04-15"
  date: "2023-04-15",
  system: "hWBTC market of Hundred Finance, a Compound v2 fork on Optimism",
  domain: "vault share accounting",
  language: "Solidity",
  loss: {
    // README: "Reported losses are about $7 million (rekt.news gives $7.4M; this figure was not checked here)."
    amount: "about $7 million",
    usdMillions: 7,
    short: "in reported losses",
    basis: "in reported losses (rekt.news gives $7.4M; this figure was not checked here)",
    citations: [
      { label: "rekt.news", url: "https://rekt.news/hundred-rekt2" },
      { label: "BlockSec", url: "https://blocksec.com/blog/6-hundred-finance-incident-catalyzing-the-wave-of-precision-related-exploits-in-vulnerable-forked-protocols" },
    ],
  },
  bug: "redeemUnderlying rounded the shares burned down, so a withdrawal worth 1.99999999992 share units burned 1.",
  property: "No sequence of operations, donations included, lowers the value of a share while shares are outstanding.",
  propertyId: "REQ-SHARE-VALUE",
  vulnerable: {
    label: "Hundred hToken share accounting",
    verdict: "REFUTED",
    // No Passport was issued for the port: harness/validate_task.py records the judge rejecting it and
    // its binary REFUTED (realworld/tasks/rw-hundred-vault/validation.json checks.start), and
    // results/vault-1/real-code/report.json records port.kernel_refutation_checked.
    passport: null,
    witness: `${HUNDRED_TASK}/witnesses/hundred_attack.lean`,
    finding: "After the attack's own amounts, the last share unit is backed by 2 satoshi.",
  },
  repair: {
    model: "Muse Spark 1.3",
    arm: "A1",
    planner: null,
    tier: "Contributor",
    attempt: 1,
    verdict: "VERIFIED",
    passport: {
      path: "results/vault-1/repair-A1-1/passport.json",
      sha256: "08fe86f17f27c49d60bda786d1498200d333c1c8d63d2f858ab668cd4f7fe7c4",
      status: "VERIFIED",
      requirements: {
        "REQ-DEPOSIT-SUCCEEDS": "VERIFIED",
        "REQ-REDEEM-SUCCEEDS": "VERIFIED",
        "REQ-WITHDRAW-SUCCEEDS": "VERIFIED",
        "REQ-DEPOSIT-EFFECTS": "VERIFIED",
        "REQ-REDEEM-EFFECTS": "VERIFIED",
        "REQ-WITHDRAW-EFFECTS": "VERIFIED",
        "REQ-DEPOSIT-ROUNDS-DOWN": "VERIFIED",
        "REQ-REDEEM-ROUNDS-DOWN": "VERIFIED",
        "REQ-WITHDRAW-ROUNDS-UP": "VERIFIED",
        "REQ-SHARE-VALUE": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/vault-1/repair-A1-1/passport.json --candidate results/vault-1/repair-A1-1/final.lean",
    },
    run: "results/vault-1/repair-A1-1",
    // results/vault-1/repair-A1-1/summary.json budget: elapsed_s 1199.9, usd_list 0.6513, usd_actual 0.037, 67 calls
    seconds: 1200,
    usdList: 0.65,
    usdCharged: 0.037,
    calls: 67,
    verifyLog: "results/vault-1/repair-A1-1/verify.txt",
    kernels: 6,
    propertyCases: 2001,
    // results/vault-1/README.md: "Muse replaced the truncated exchange rate with exact `assets / supply` pricing"
    change: "prices shares from the exact ratio of assets to supply and rounds the shares burned up",
  },
  unresolved: [],
  realCode: {
    short: "deployed bytecode on an Optimism fork, 501 sequences",
    result: "matches the Lean port on all 501; 292 break a requirement",
    report: "results/vault-1/real-code/report.json",
    unit: "sequences",
    total: 501,
    how: "On a fork of Optimism at block 90761917, the hWBTC market was emptied as in the attack, and 501 sequences (the attack and 500 generated) ran on the deployed CErc20Delegate bytecode, on the Lean port and on the Muse repair.",
    rows: [
      { label: "Deployed hWBTC contract", commit: null, violating: 292, sameAsPort: 501, sameAsProved: 209, note: "identical to the Lean port after every operation of all 501" },
      { label: "Muse repair", commit: null, violating: 0, sameAsPort: null, sameAsProved: null, note: "the proved component, on the same 501 sequences" },
    ],
    confirmedInLean: { goals: 5, checked: 5 },
  },
  // README "What happened" and "What refutes the port"; satoshi of WBTC
  attack: [
    { text: "The market is emptied: no shares outstanding, 1 satoshi of cash." },
    { text: "The attacker deposits 400,000,000 satoshi (4 WBTC).", after: "20,000,000,000 share units" },
    { text: "It redeems 19,999,999,998 share units.", after: "2 share units backed by 1 satoshi" },
    { text: "It sends 50,030,063,816 satoshi straight to the market, so each unit is worth about 250 WBTC, and borrows ETH against its 2 units. Borrowing is not modeled.", after: "2 share units backed by 50,030,063,817 satoshi" },
    { text: "It withdraws 50,030,063,815 satoshi, worth 1.99999999992 share units. The contract burns 1.", after: "1 share unit backed by 2 satoshi" },
  ],
  context: null,
  outcome: "The kernel checks that the port breaks REQ-SHARE-VALUE (a share falls from 50,030,063,817 / 2 satoshi to 2) and REQ-WITHDRAW-ROUNDS-UP. The Muse repair burns both share units.",
  timeline: [],
  equivalence: null,
  limits: [
    "Only share accounting is modeled; the comptroller, borrowing, liquidation, interest and reserves are not. The specification states the share-value property the borrow relied on.",
    "The deployed contract is run on 501 sequences on a fork and compared with the port and the requirements; it is not itself proved.",
  ],
  reconstruction: null,
};

// realworld/tasks/rw-balancer-upscale/README.md, results/balancer-1/
const balancer: Flagship = {
  key: "balancer",
  task: BALANCER_TASK,
  incident: "Balancer V2",
  year: 2025,
  // README: "On 2025-11-03 attackers drained Balancer V2 Composable Stable Pools and forks of them on several chains."
  date: "2025-11-03",
  system: "Composable Stable Pools of Balancer V2 and its forks",
  domain: "AMM swap rounding",
  language: "Solidity",
  loss: {
    // README: OpenZeppelin puts the loss at "$120+ million across Balancer and its forks"
    amount: "more than $120 million",
    usdMillions: 120,
    short: "across Balancer and its forks",
    basis: "across Balancer and its forks, as OpenZeppelin reports; The Block reports estimates of over $128 million",
    citations: [
      { label: "OpenZeppelin", url: "https://www.openzeppelin.com/news/understanding-the-balancer-v2-exploit" },
      { label: "The Block", url: "https://www.theblock.co/post/377863/balancer-identifies-rounding-error-as-root-cause-of-multi-chain-defi-exploit" },
      { label: "Certora", url: "https://www.certora.com/blog/breaking-down-the-balancer-hack" },
    ],
  },
  bug: "A swap for an exact amount out rounded that amount down before pricing it, so 17 wei of osETH, worth 17.988 of the pool's units, was priced as 17.",
  property: "For any pool math meeting the stated contract, no batch of swaps of any length lowers the pool's value.",
  propertyId: "REQ-BATCH-KEEPS-VALUE",
  vulnerable: {
    label: "Deployed swap path of the osETH/WETH pool",
    verdict: "REFUTED",
    passport: {
      path: "results/balancer-1/passports/port.json",
      sha256: "d65bd405a13bfd4feaef838e4cc60dea2560bc47ff78cad8dfda591aaf26cb71",
      status: "REFUTED",
      requirements: {
        "REQ-GIVEN-IN-SUCCEEDS": "UNRESOLVED",
        "REQ-GIVEN-OUT-SUCCEEDS": "UNRESOLVED",
        "REQ-GIVEN-IN-PAYS-AT-MOST": "UNRESOLVED",
        "REQ-GIVEN-IN-PAYS-AT-LEAST": "UNRESOLVED",
        "REQ-GIVEN-OUT-CHARGES-AT-LEAST": "REFUTED",
        "REQ-GIVEN-OUT-CHARGES-AT-MOST": "UNRESOLVED",
        "REQ-SWAP-KEEPS-VALUE": "REFUTED",
        "REQ-BATCH-KEEPS-VALUE": "REFUTED",
      },
      reproduce: "bin/proofforge verify results/balancer-1/passports/port.json --candidate realworld/tasks/rw-balancer-upscale/attacks/balancer_port.lean",
    },
    witness: `${BALANCER_TASK}/witnesses/attack_batch.lean`,
    // README "What refutes the port": four rounds, value 4,749,898,000 to 297,229,191
    finding: "Four rounds of the attack's three swaps lower the pool's value from 4,749,898,000 to 297,229,191.",
  },
  repair: {
    model: "Muse Spark 1.3",
    arm: "A2",
    planner: "Muse Wonder 1.0",
    tier: "Contributor",
    attempt: 1,
    verdict: "VERIFIED",
    passport: {
      path: "results/balancer-1/repair-A2-1/passport.json",
      sha256: "48930efdd4d67460bfd22bb15dfa9625caafc36cd6fca3a8fee444d5f3b204ba",
      status: "VERIFIED",
      requirements: {
        "REQ-GIVEN-IN-SUCCEEDS": "VERIFIED",
        "REQ-GIVEN-OUT-SUCCEEDS": "VERIFIED",
        "REQ-GIVEN-IN-PAYS-AT-MOST": "VERIFIED",
        "REQ-GIVEN-IN-PAYS-AT-LEAST": "VERIFIED",
        "REQ-GIVEN-OUT-CHARGES-AT-LEAST": "VERIFIED",
        "REQ-GIVEN-OUT-CHARGES-AT-MOST": "VERIFIED",
        "REQ-SWAP-KEEPS-VALUE": "VERIFIED",
        "REQ-BATCH-KEEPS-VALUE": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/balancer-1/repair-A2-1/passport.json --candidate results/balancer-1/repair-A2-1/final.lean",
    },
    run: "results/balancer-1/repair-A2-1",
    // results/balancer-1/repair-A2-1/summary.json budget: elapsed_s 2344.1, usd_list 2.5115, usd_actual 0.4087, 151 calls
    seconds: 2344,
    usdList: 2.51,
    usdCharged: 0.41,
    calls: 151,
    verifyLog: "results/balancer-1/repair-A2-1/verify.txt",
    kernels: 6,
    propertyCases: 2001,
    // README: "the amount out is upscaled rounding up and the swap is refused unless that amount is below the scaled balance"
    change: "rounds the amount out up before pricing it and refuses the swap unless that amount is below the pool's balance",
  },
  unresolved: [],
  realCode: {
    short: "deployed Vault and pool on an Ethereum fork, 501 batches",
    result: "identical to the Lean port on all 501; the pool's value falls in 56, never with the Muse repair",
    report: "results/balancer-1/real-code/report.json",
    unit: "batches",
    total: 501,
    how: "On a fork of Ethereum taken just before the attack transaction, the attack's first 22 swaps brought the deployed pool to 67,000 wei of each token, as on chain. Then 501 batches (the attack's 90 swaps and 500 generated, 10,385 swaps in all) ran through the deployed Vault, the Lean port and the Muse repair.",
    rows: [
      { label: "Deployed Vault and osETH/WETH pool", commit: null, violating: 56, sameAsPort: 501, sameAsProved: 194, note: "the pool's invariant falls in 56 batches, and its BPT price with it" },
      { label: "Muse repair", commit: null, violating: 0, sameAsPort: null, sameAsProved: null, note: "the proved component on the same 501 batches" },
    ],
    confirmedInLean: { goals: 6, checked: 6 },
  },
  // README "What happened", from chain data; wei of each token
  attack: [
    { text: "The attacker sells BPT for the pool's tokens, 22 swaps in one batch. BPT swaps, joins and exits are not modeled.", after: "67,000 wei of WETH and 67,000 of osETH" },
    { text: "It takes osETH out until 18 wei are left." },
    { text: "It takes 17 wei of osETH out. At the cached osETH rate that is 17.988 of the pool's units; the pool rounds it down and prices 17." },
    { text: "It takes WETH out, paid with osETH, and repeats the three swaps, 30 rounds in all.", after: "889 wei of WETH and 1,472 of osETH" },
    { text: "It buys BPT back at the collapsed price. This step is not modeled; the specification states the property it relied on." },
  ],
  outcome: "The kernel checks that four rounds of these swaps lower the pool's value from 4,749,898,000 to 297,229,191, and that the port, run with a port of StableMath, charges exactly the logged amount of all 90 swaps of the attack.",
  context: "Certora writes that its 2022 verified properties of these pools “did not constrain the relationship between individual swaps or rounding behavior”. The locked requirements here are about exactly that.",
  timeline: [],
  equivalence: null,
  limits: [
    "The requirements hold for any pool math meeting a stated contract; a constant-product pool is proved to meet it, StableMath is not, so results with StableMath are tested.",
    "BPT swaps, joins and exits are not modeled. The deployed contracts are run on 501 batches on a fork; they are not themselves proved.",
  ],
  reconstruction: null,
};

// realworld/tasks/rc-knight-router/README.md, results/knight-1/
const knight: Flagship = {
  key: "knight",
  task: KNIGHT_TASK,
  incident: "Knight Capital",
  year: 2012,
  // witnesses/buggy_original.lean: "The deployment of August 1, 2012 as the order describes it"
  date: "2012-08-01",
  system: "SMARS, Knight Capital's equity order router",
  domain: "equity order routing",
  language: null,
  loss: {
    // README, paragraph 17: "Knight realized a $460 million loss"
    amount: "$460 million",
    usdMillions: 460,
    short: "realized loss",
    basis: "realized loss, as the SEC order states",
    citations: [
      { label: "SEC order 34-70694", url: "https://www.sec.gov/files/litigation/admin/2013/34-70694.pdf" },
      { label: "archived copy", url: "https://web.archive.org/web/20201212052325/https://www.sec.gov/litigation/admin/2013/34-70694.pdf" },
    ],
  },
  bug: "New code was not copied to one of eight servers. There, orders carrying a repurposed flag ran dead Power Peg code, which kept sending child orders without counting the executions.",
  property: "On every server and code version, after any sequence of events, the shares sent for an order never exceed its quantity.",
  propertyId: "REQ-NEVER-OVERROUTE",
  vulnerable: {
    label: "Reconstructed Power Peg router",
    verdict: "REFUTED",
    passport: {
      path: "results/knight-1/start/passport.json",
      sha256: "ca3e7312fe7af22f53f52fbd08f53dfc85bde86ebe49a96e0e9751e4f365a6b8",
      status: "REFUTED",
      requirements: {
        "REQ-NORMAL-ORDER-ROUTED": "REFUTED",
        "REQ-ROUTES-AVAILABLE": "REFUTED",
        "REQ-NEVER-OVERROUTE": "REFUTED",
        "REQ-STOP-WHEN-FILLED": "REFUTED",
        "REQ-NO-EXCESS-EXECUTION": "REFUTED",
        "REQ-FILL-ACCOUNTING": "REFUTED",
      },
      reproduce: "bin/proofforge verify results/knight-1/start/passport.json --candidate realworld/tasks/rc-knight-router/candidate/Solution.lean",
    },
    witness: `${KNIGHT_TASK}/witnesses/buggy_original.lean`,
    finding: "For every n, n rounds of a 100-share routing opportunity and a fill send n child orders and 100 × n shares for one 100-share order.",
  },
  repair: {
    model: "Muse Spark 1.3",
    arm: "A2",
    planner: "Muse Wonder 1.0",
    tier: "Contributor",
    attempt: 2,
    verdict: "VERIFIED",
    passport: {
      path: "results/knight-1/A2-2/passport.json",
      sha256: "98cfed64ae1ec596e517299b422a5fb0beac571cdce89c18ea2e5660845bc178",
      status: "VERIFIED",
      requirements: {
        "REQ-NORMAL-ORDER-ROUTED": "VERIFIED",
        "REQ-ROUTES-AVAILABLE": "VERIFIED",
        "REQ-NEVER-OVERROUTE": "VERIFIED",
        "REQ-STOP-WHEN-FILLED": "VERIFIED",
        "REQ-NO-EXCESS-EXECUTION": "VERIFIED",
        "REQ-FILL-ACCOUNTING": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/knight-1/A2-2/passport.json --candidate results/knight-1/A2-2/final.lean",
    },
    run: "results/knight-1/A2-2",
    // results/knight-1/A2-2/summary.json budget: elapsed_s 4078.9, usd_list 4.96, usd_actual 0.9788, 256 calls
    seconds: 4079,
    usdList: 4.96,
    usdCharged: 0.98,
    calls: 256,
    verifyLog: "results/knight-1/A2-2/verify.log",
    kernels: 6,
    propertyCases: 2001,
    // results/knight-1/README.md: "removes the Power Peg path"
    change: "removes the Power Peg path, so every build routes by the shares not yet sent and every fill advances the executed count",
  },
  // results/knight-1/README.md run table
  unresolved: [
    {
      run: "results/knight-1/A1-1",
      label: "A1, attempt 1",
      proved: 1,
      stop: "wall-clock cap",
      passport: {
        path: "results/knight-1/A1-1/passport.json",
        sha256: "4fddc1683956e92f1f0a7e97eb48bdc238e233b55b9e430dda47062bfaac5e74",
        status: "UNRESOLVED",
        requirements: {
          "REQ-NORMAL-ORDER-ROUTED": "UNRESOLVED",
          "REQ-ROUTES-AVAILABLE": "UNRESOLVED",
          "REQ-NEVER-OVERROUTE": "UNRESOLVED",
          "REQ-STOP-WHEN-FILLED": "UNRESOLVED",
          "REQ-NO-EXCESS-EXECUTION": "UNRESOLVED",
          "REQ-FILL-ACCOUNTING": "UNRESOLVED",
        },
        reproduce: "bin/proofforge verify results/knight-1/A1-1/passport.json --candidate results/knight-1/A1-1/final.lean",
      },
    },
    {
      run: "results/knight-1/A1-2",
      label: "A1, attempt 2",
      proved: 1,
      stop: "dollar cap",
      passport: {
        path: "results/knight-1/A1-2/passport.json",
        sha256: "27f4c83221ed220ea8e52e955a82a45bd73f9d8eed2d0136081096a4b09afb6c",
        status: "UNRESOLVED",
        requirements: {
          "REQ-NORMAL-ORDER-ROUTED": "UNRESOLVED",
          "REQ-ROUTES-AVAILABLE": "UNRESOLVED",
          "REQ-NEVER-OVERROUTE": "UNRESOLVED",
          "REQ-STOP-WHEN-FILLED": "UNRESOLVED",
          "REQ-NO-EXCESS-EXECUTION": "UNRESOLVED",
          "REQ-FILL-ACCOUNTING": "UNRESOLVED",
        },
        reproduce: "bin/proofforge verify results/knight-1/A1-2/passport.json --candidate results/knight-1/A1-2/final.lean",
      },
    },
    {
      run: "results/knight-1/A2-1",
      label: "A2, attempt 1",
      proved: 5,
      stop: "dollar cap",
      passport: {
        path: "results/knight-1/A2-1/passport.json",
        sha256: "edc4ec8cd40a2db0fb8b77a2c959e5d9e4cb236403e5ce4e3cb2778bd5279c9b",
        status: "UNRESOLVED",
        requirements: {
          "REQ-NORMAL-ORDER-ROUTED": "UNRESOLVED",
          "REQ-ROUTES-AVAILABLE": "UNRESOLVED",
          "REQ-NEVER-OVERROUTE": "UNRESOLVED",
          "REQ-STOP-WHEN-FILLED": "UNRESOLVED",
          "REQ-NO-EXCESS-EXECUTION": "UNRESOLVED",
          "REQ-FILL-ACCOUNTING": "UNRESOLVED",
        },
        reproduce: "bin/proofforge verify results/knight-1/A2-1/passport.json --candidate results/knight-1/A2-1/final.lean",
      },
    },
  ],
  realCode: null,
  // README "What the order says" and "What was proved"
  attack: [
    { text: "Seven of eight servers run the new code; the eighth still runs the old code (paragraph 15)." },
    { text: "A parent order for 100 shares arrives with the repurposed flag, which on the eighth server activates Power Peg (paragraphs 13 and 16)." },
    { text: "A routing opportunity for 100 shares arrives. The router sends a 100-share child order, and it is filled.", after: "100 of 100 shares executed" },
    { text: "Power Peg's count never sees the fill, so the next opportunity sends another 100 shares, and so on for every opportunity.", after: "after n rounds: n child orders, 100 × n shares executed" },
  ],
  outcome: "The kernel proves by induction that the reconstructed router sends n child orders for one 100-share order, for every n, while the new code sends exactly one on the same events. It also refutes the obvious patch: counting fills again still sends 200 shares for a 100-share order when two opportunities arrive before a fill.",
  // README, paragraph 17
  context: "The SEC order reports millions of child orders for 212 parent orders: 4 million executions in 154 stocks, more than 397 million shares, in about 45 minutes.",
  timeline: [],
  equivalence: null,
  limits: [
    "The mechanism by which fills stopped reaching Power Peg's count is one interpretation of paragraphs 14 and 16 of the order; other mechanisms with the same outcome are possible.",
    "Prices, venues, order types, timing and cancellations are not modeled. The executable wrapper is tested, not proved.",
  ],
  reconstruction: "Knight Capital is reconstructed from the SEC's findings (Release No. 34-70694) because Knight's code is not public; nothing in the task is Knight's code, and every Knight Passport says so.",
};

/** Display order. The first is the featured case. */
export const FLAGSHIPS: Flagship[] = [cetus, balancer, euler, knight, hundred];
export const FEATURED = cetus;

/** A Muse implement-from-specification figure; shown when present. */
export interface ImplementsFigure {
  label: string;
  value: number;
  of: number;
  detail: string;
  source: string;
}
// results/implement-1/implement.json: 30 of 30 frozen E1 test tasks accepted in implement mode
export const IMPLEMENTS: ImplementsFigure | null = {
  label: "test tasks implemented from the specification alone",
  value: 30,
  of: 30,
  detail: "9 base specifications in ledgers, permissions and queues; the variants differ only in code implement mode never sees",
  source: "results/implement-1/implement.json",
};

/** Implement mode on the flagships: Muse starts from a stub generated from the locked challenge. */
export interface ImplementedFlagship {
  key: Flagship["key"];
  run: string;
  passport: PassportRef;
}
export const IMPLEMENTED_FLAGSHIPS: ImplementedFlagship[] = [
  {
    key: "cetus",
    // results/implement-flagships-1/rw-cetus-shlw/passport.json and summary.json
    run: "results/implement-flagships-1/rw-cetus-shlw",
    passport: {
      path: "results/implement-flagships-1/rw-cetus-shlw/passport.json",
      sha256: "b2cf6c2de4f91b8ea0f1505463e5301f28783d87a103c0a3e7d1d3f791a7dd7a",
      status: "VERIFIED",
      requirements: {
      "REQ-SHLW-COMPLETE": "VERIFIED",
      "REQ-SHLW-EXACT": "VERIFIED",
      "REQ-DELTA-A-FLOOR": "VERIFIED",
      "REQ-DELTA-A-TIGHT": "VERIFIED",
      "REQ-DELTA-A-COVERS": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/implement-flagships-1/rw-cetus-shlw/passport.json --candidate results/implement-flagships-1/rw-cetus-shlw/final.lean",
    },
  },
  {
    key: "euler",
    // results/implement-flagships-1/rw-euler-donate/passport.json and summary.json
    run: "results/implement-flagships-1/rw-euler-donate",
    passport: {
      path: "results/implement-flagships-1/rw-euler-donate/passport.json",
      sha256: "27d4ec2838e9bbfc938278e29e8eac89570d1f14a9468de15b03514cbdd4286e",
      status: "VERIFIED",
      requirements: {
      "REQ-HONEST-FLOW": "VERIFIED",
      "REQ-ALLOWED-SUCCEEDS": "VERIFIED",
      "REQ-EFFECTS": "VERIFIED",
      "REQ-ACTOR-HEALTHY": "VERIFIED",
      "REQ-STAYS-HEALTHY": "VERIFIED",
      "REQ-NO-BAD-DEBT": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/implement-flagships-1/rw-euler-donate/passport.json --candidate results/implement-flagships-1/rw-euler-donate/final.lean",
    },
  },
  {
    key: "hundred",
    // results/implement-flagships-1/rw-hundred-vault/passport.json and summary.json
    run: "results/implement-flagships-1/rw-hundred-vault",
    passport: {
      path: "results/implement-flagships-1/rw-hundred-vault/passport.json",
      sha256: "eee7e2cdbedf658d81afc95f07966d5d37a9e6f7a27cabbccd6dd0dc5ba6e3c6",
      status: "VERIFIED",
      requirements: {
      "REQ-DEPOSIT-SUCCEEDS": "VERIFIED",
      "REQ-REDEEM-SUCCEEDS": "VERIFIED",
      "REQ-WITHDRAW-SUCCEEDS": "VERIFIED",
      "REQ-DEPOSIT-EFFECTS": "VERIFIED",
      "REQ-REDEEM-EFFECTS": "VERIFIED",
      "REQ-WITHDRAW-EFFECTS": "VERIFIED",
      "REQ-DEPOSIT-ROUNDS-DOWN": "VERIFIED",
      "REQ-REDEEM-ROUNDS-DOWN": "VERIFIED",
      "REQ-WITHDRAW-ROUNDS-UP": "VERIFIED",
      "REQ-SHARE-VALUE": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/implement-flagships-1/rw-hundred-vault/passport.json --candidate results/implement-flagships-1/rw-hundred-vault/final.lean",
    },
  },
  {
    key: "balancer",
    // results/balancer-1/implement-2/passport.json and summary.json; the first implement attempt reached its cap
    run: "results/balancer-1/implement-2",
    passport: {
      path: "results/balancer-1/implement-2/passport.json",
      sha256: "65d5a81fef2352eb67a72f032ade091fd051b30ebf44c310b1d0c6dcb1b84d3d",
      status: "VERIFIED",
      requirements: {
        "REQ-GIVEN-IN-SUCCEEDS": "VERIFIED",
        "REQ-GIVEN-OUT-SUCCEEDS": "VERIFIED",
        "REQ-GIVEN-IN-PAYS-AT-MOST": "VERIFIED",
        "REQ-GIVEN-IN-PAYS-AT-LEAST": "VERIFIED",
        "REQ-GIVEN-OUT-CHARGES-AT-LEAST": "VERIFIED",
        "REQ-GIVEN-OUT-CHARGES-AT-MOST": "VERIFIED",
        "REQ-SWAP-KEEPS-VALUE": "VERIFIED",
        "REQ-BATCH-KEEPS-VALUE": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/balancer-1/implement-2/passport.json --candidate results/balancer-1/implement-2/final.lean",
    },
  },  {
    key: "knight",
    // results/implement-flagships-1/rc-knight-router-A2-1/passport.json and summary.json; arm A2, Muse Wonder 1.0 as planner
    run: "results/implement-flagships-1/rc-knight-router-A2-1",
    passport: {
      path: "results/implement-flagships-1/rc-knight-router-A2-1/passport.json",
      sha256: "80721c043007d8408614e403852651ec45a4bc4ed0dd2ede71f8900bc28b73ae",
      status: "VERIFIED",
      requirements: {
        "REQ-NORMAL-ORDER-ROUTED": "VERIFIED",
        "REQ-ROUTES-AVAILABLE": "VERIFIED",
        "REQ-NEVER-OVERROUTE": "VERIFIED",
        "REQ-STOP-WHEN-FILLED": "VERIFIED",
        "REQ-NO-EXCESS-EXECUTION": "VERIFIED",
        "REQ-FILL-ACCOUNTING": "VERIFIED",
      },
      reproduce: "bin/proofforge verify results/implement-flagships-1/rc-knight-router-A2-1/passport.json --candidate results/implement-flagships-1/rc-knight-router-A2-1/final.lean",
    },
  },
];

/** The benchmark beyond the incidents (tasks/ and formal/). */
export const BENCHMARK = {
  // tasks/*/task.json plus formal/task.json
  tasks: 59,
  splits: { dev: 23, val: 6, test: 30 },
  families: [
    { key: "payouts", label: "Payouts", tasks: 9 },
    { key: "ledgers", label: "Ledgers", tasks: 10 },
    { key: "transfers", label: "Transfer batches", tasks: 10 },
    { key: "permissions", label: "Permissions", tasks: 10 },
    { key: "rate-limiters", label: "Rate limiters", tasks: 10 },
    { key: "queues", label: "Queues", tasks: 10 },
  ],
} as const;

/** Lowest and highest list price of the flagship repairs. */
export function repairCosts(fs: readonly Flagship[] = FLAGSHIPS) {
  const list = fs.map((f) => f.repair.usdList);
  return { minList: Math.min(...list), maxList: Math.max(...list) };
}

export const requirementCount = (p: PassportRef) => Object.keys(p.requirements).length;
export const verifiedCount = (p: PassportRef) => Object.values(p.requirements).filter((s) => s === "VERIFIED").length;

/** "a, b and c" */
export function andList(words: readonly string[]): string {
  if (words.length <= 1) return words.join("");
  return `${words.slice(0, -1).join(", ")} and ${words[words.length - 1]}`;
}

/** One sentence naming the incidents, for meta tags and the machine-readable summary. */
export function incidentsSentence(fs: readonly Flagship[] = FLAGSHIPS): string {
  return andList(fs.map((f) => `${f.incident} (${f.year}, ${f.loss.amount})`));
}

/** Sum of the incidents' loss figures, in millions of US dollars (each rounded down). */
export const lossTotalMillions = (fs: readonly Flagship[] = FLAGSHIPS) => fs.reduce((n, f) => n + f.loss.usdMillions, 0);

/** "more than $1 billion" or "more than $450 million", from the rounded-down total. */
export function lossTotalPhrase(lead: "more than" | "over" = "more than", fs: readonly Flagship[] = FLAGSHIPS): string {
  const m = lossTotalMillions(fs);
  return m >= 1000 ? `${lead} $${Math.floor(m / 1000)} billion` : `${lead} $${Math.floor(m / 10) * 10} million`;
}

export const HEADLINE = "ProofForge turns Meta's Muse models into provers of financial code.";
export const SUMMARY =
  "Each task states what financial code must guarantee as locked Lean 4 requirements. ProofForge refutes code that breaks one with a counterexample the Lean kernel checks, and accepts a fix, written by Muse Spark or by people, only when six independent kernels check its proof. Every verdict is a Passport, bound by hash to the specification, the source and the executable, that anyone can re-run.";
