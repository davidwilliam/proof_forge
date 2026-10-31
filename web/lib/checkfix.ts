// The "Check a fix" panel on the home page: real-world tasks and candidate files a visitor can
// submit to POST /api/verify, with the committed Passport of each exact file as the recorded
// result shown when the API is slow or down.
//
// scripts/check-fixes.mjs copies each candidate to public/check/<task>/<key>.lean and writes the
// recorded result to public/check/<task>/<key>.json; it refuses a recorded Passport that did not
// check the same bytes. tests/checkfix.test.ts fails when those files are stale.
//
// This module has no runtime imports, so scripts/check-fixes.mjs can load it on its own.

export type CandidateAuthor = "upstream" | "muse" | "port" | "reference";

export interface FixCandidate {
  /** File stem under public/check/<task>/. */
  key: string;
  label: string;
  author: CandidateAuthor;
  /** One sentence: what this file is. */
  detail: string;
  /** Repository path of the Lean candidate. */
  source: string;
  /** Repository path of the committed Passport that checked this exact file. */
  recorded: string;
}

export interface FixTarget {
  /** Flagship key in lib/flagships.ts, or "compound". */
  key: string;
  task: string;
  incident: string;
  candidates: FixCandidate[];
}

export const FIX_TARGETS: FixTarget[] = [
  {
    key: "cetus",
    task: "rw-cetus-shlw",
    incident: "Cetus",
    candidates: [
      {
        key: "pr6-hotfix",
        label: "Same-day hotfix, pull request 6",
        author: "upstream",
        detail: "Merged 14:37 UTC on the day of the attack: mask = 1 << 192, test n > mask.",
        source: "realworld/tasks/rw-cetus-shlw/attacks/pr6_mask_only.lean",
        recorded: "results/counterexamples-1/cetus-pr6-port/passport.json",
      },
      {
        key: "original",
        label: "Original code",
        author: "port",
        detail: "integer-mate at 4d09c8b, before the fixes: a 256-bit mask in the overflow check.",
        source: "realworld/tasks/rw-cetus-shlw/attacks/buggy_original.lean",
        recorded: "results/counterexamples-1/cetus-original-port/passport.json",
      },
      {
        key: "pr7-final-fix",
        label: "Final fix, pull request 7",
        author: "upstream",
        detail: "Merged 16:09 UTC: the test changed from n > mask to n >= mask.",
        source: "realworld/tasks/rw-cetus-shlw/reference/SolutionA.lean",
        recorded: "results/cetus-1/passports/pr7-port.json",
      },
      {
        key: "muse-repair",
        label: "Muse Spark repair",
        author: "muse",
        detail: "Written by Muse Spark 1.3 from the original code, first attempt (results/cetus-1/repair-A1-1).",
        source: "results/cetus-1/repair-A1-1/final.lean",
        recorded: "results/cetus-1/repair-A1-1/passport.json",
      },
    ],
  },
  {
    key: "euler",
    task: "rw-euler-donate",
    incident: "Euler Finance",
    candidates: [
      {
        key: "original",
        label: "Euler v1 at b1ee326",
        author: "port",
        detail: "donateToReserves without the liquidity check that withdraw, mint and transfer perform.",
        source: "realworld/tasks/rw-euler-donate/candidate/Solution.lean",
        recorded: "results/counterexamples-1/euler-port/passport.json",
      },
      {
        key: "muse-repair",
        label: "Muse Spark repair",
        author: "muse",
        detail: "Adds the health check to the donation guard (results/euler-1/rw-euler-donate/repair-A1-1).",
        source: "results/euler-1/rw-euler-donate/repair-A1-1/final.lean",
        recorded: "results/euler-1/rw-euler-donate/repair-A1-1/passport.json",
      },
    ],
  },
  {
    key: "balancer",
    task: "rw-balancer-upscale",
    incident: "Balancer V2",
    candidates: [
      {
        key: "original",
        label: "Deployed swap path",
        author: "port",
        detail: "The osETH/WETH pool's swap given out: the amount out is rounded down before pricing.",
        source: "realworld/tasks/rw-balancer-upscale/attacks/balancer_port.lean",
        recorded: "results/counterexamples-1/balancer-port/passport.json",
      },
      {
        key: "muse-repair",
        label: "Muse Spark repair, planned by Muse Wonder",
        author: "muse",
        detail: "Rounds the amount out up before pricing it and refuses the swap unless that amount is below the pool's balance (results/balancer-1/repair-A2-1).",
        source: "results/balancer-1/repair-A2-1/final.lean",
        recorded: "results/balancer-1/repair-A2-1/passport.json",
      },
    ],
  },
  {
    key: "knight",
    task: "rc-knight-router",
    incident: "Knight Capital",
    candidates: [
      {
        key: "original",
        label: "Reconstructed Power Peg router",
        author: "port",
        detail: "Reconstructed from the SEC order, not Knight's code: orders with the repurposed flag run the dead Power Peg code on the server that kept the old version.",
        source: "realworld/tasks/rc-knight-router/candidate/Solution.lean",
        recorded: "results/counterexamples-1/knight-start/passport.json",
      },
      {
        key: "muse-repair",
        label: "Muse Spark repair, planned by Muse Wonder",
        author: "muse",
        detail: "Removes the Power Peg path (results/knight-1/A2-2).",
        source: "results/knight-1/A2-2/final.lean",
        recorded: "results/knight-1/A2-2/passport.json",
      },
    ],
  },
  {
    key: "hundred",
    task: "rw-hundred-vault",
    incident: "Hundred Finance",
    candidates: [
      {
        key: "original",
        label: "hToken share accounting",
        author: "port",
        detail: "redeemUnderlying rounds the shares burned down.",
        source: "realworld/tasks/rw-hundred-vault/candidate/Solution.lean",
        recorded: "results/counterexamples-1/rw-hundred-vault-start/passport.json",
      },
      {
        key: "muse-repair",
        label: "Muse Spark repair",
        author: "muse",
        detail: "Prices shares from the exact ratio and rounds the shares burned up (results/vault-1/repair-A1-1).",
        source: "results/vault-1/repair-A1-1/final.lean",
        recorded: "results/vault-1/repair-A1-1/passport.json",
      },
    ],
  },
  {
    key: "compound",
    task: "rw-compound-comp",
    incident: "Compound Proposal 62",
    candidates: [
      {
        key: "original",
        label: "Proposal 62 Comptroller",
        author: "port",
        detail: "The upgrade set reward indices still at 0 to 1e36, so an account with no recorded index was credited COMP that had never been emitted.",
        source: "realworld/tasks/rw-compound-comp/candidate/Solution.lean",
        recorded: "results/counterexamples-1/compound-p62-port/passport.json",
      },
      {
        key: "p64-fix",
        label: "Fix shipped by Proposal 64",
        author: "reference",
        detail: "The fix Proposal 64 shipped and Proposal 65 kept, ported and proved by the build team; no Muse run proved this task.",
        source: "realworld/tasks/rw-compound-comp/reference/SolutionA.lean",
        recorded: "results/compound-1/passports/reference.json",
      },
    ],
  },
];

export const checkPath = (task: string, key: string, ext: "lean" | "json") => `/check/${task}/${key}.${ext}`;

export interface CheckRequirement {
  id: string;
  /** The requirement's doc string, without the leading "ID: ". */
  text: string | null;
  status: string;
  /** The property-test witness message, when the executable refuted it. */
  witness: string | null;
}

export interface CheckCounterexample {
  requirement: string;
  kernelChecked: boolean;
  kernels: number;
  /** The Lean statement proved: the negation of the requirement for the candidate's definitions. */
  statement: string | null;
  message: string | null;
  reason: string | null;
}

export interface CheckSummary {
  status: string;
  passportSha256: string;
  generated: string | null;
  kernels: number;
  propertyCases: number | null;
  executable: string | null;
  requirements: CheckRequirement[];
  /** Null when the counterexample stage did not run. */
  counterexamples: CheckCounterexample[] | null;
  reasons: string[];
}

export interface RecordedCheck extends CheckSummary {
  task: string;
  candidate: string;
  source: string;
  sourceSha256: string;
  passportPath: string;
}

/** The parts of a Passport (harness/passport.py) the panel reads. */
export interface PassportLike {
  status: string;
  passport_sha256: string;
  generated?: string;
  proof_check?: { reasons?: string[] };
  requirements: { id: string; text?: string | null; status: string; witness?: { message?: string } | null }[];
  checks?: { comparator_kernels?: string[]; property_tests?: { cases?: number } };
  executable?: { status?: string };
  counterexamples?: { requirement: string; kernel_checked: boolean; kernels?: string[]; statement?: string | null; message?: string | null; reason?: string | null }[];
}

/** What the panel shows of a Passport, live from the API or recorded. */
export function summarizePassport(p: PassportLike): CheckSummary {
  return {
    status: p.status,
    passportSha256: p.passport_sha256,
    generated: p.generated ?? null,
    kernels: p.checks?.comparator_kernels?.length ?? 0,
    propertyCases: p.checks?.property_tests?.cases ?? null,
    executable: p.executable?.status ?? null,
    requirements: p.requirements.map((r) => ({
      id: r.id,
      text: r.text ? r.text.replace(new RegExp(`^${r.id}:\\s*`), "") : null,
      status: r.status,
      witness: r.witness?.message ?? null,
    })),
    counterexamples: p.counterexamples
      ? p.counterexamples.map((c) => ({
          requirement: c.requirement,
          kernelChecked: c.kernel_checked,
          kernels: c.kernels?.length ?? 0,
          statement: c.statement ?? null,
          message: c.message ?? null,
          reason: c.reason ?? null,
        }))
      : null,
    reasons: p.proof_check?.reasons ?? [],
  };
}

/** Requirement ids whose status differs between two checks of the same file. */
export function statusDifferences(a: CheckSummary, b: CheckSummary): string[] {
  const other = new Map(b.requirements.map((r) => [r.id, r.status]));
  const ids = new Set([...a.requirements.map((r) => r.id), ...other.keys()]);
  return [...ids].filter((id) => a.requirements.find((r) => r.id === id)?.status !== other.get(id));
}
