// What the /about page states about the project's origin and what it builds on. Every entry is
// copied from ORIGIN.md or README.md; tests/about.test.ts checks each against those files.

/** ORIGIN.md and README.md, "Built during the hackathon". */
export const ORIGIN = {
  kickoff: "2026-10-26 12:00 ET",
  submissionsDue: "2026-11-04 21:00 ET",
  firstCommit: "535b942",
  firstCommitAt: "2026-10-26 19:43 -04:00",
  started: "Implementation started 2026-10-26 with the day-0 tooling checks in `experiments/` and `infra/`.",
  agents: "Development uses AI coding agents under the owner's direction and review.",
  noEarlierCode: "No code from earlier personal projects is included.",
} as const;

/** README.md, "Built during the hackathon": what the repository holds, all created on or after the kickoff. */
export const BUILT = [
  "the judge and its Comparator configuration",
  "the Passport and `bin/proofforge`",
  "the counterexample stage",
  "the 59 benchmark tasks",
  "the real-world tasks with their adapters to the real Move and Solidity code",
  "the Muse agents and the evaluation runners",
  "ProofForgeFin",
  "the API",
  "the PR gate",
  "this site",
] as const;

/** ORIGIN.md, "Not built during the hackathon (dependencies)", row by row. */
export const DEPENDENCIES = [
  { name: "Lean 4 v4.35.0 (kernel, compiler, Lake, `lake comparator`, `leanchecker`)", use: "Proof checking, challenge comparison, executable build" },
  { name: "bubblewrap", use: "Comparator's sandbox" },
  { name: "elan", use: "Lean toolchain installer" },
  { name: "Ubuntu 24.04 base image", use: "Judge/dev container" },
  { name: "Meta Model API (Muse Spark, Muse Wonder)", use: "Repair, proof and planning agents" },
  { name: "FastAPI, Starlette, Pydantic, Uvicorn", use: "API server" },
  { name: "Next.js, React", use: "Web front end" },
  { name: "fast-check, Vitest", use: "Property tests of the web glue code" },
] as const;

/** The six kernels Comparator runs, as harness/fin_kernels.py names them, and the README sentence that lists them. */
export const KERNELS = ["Lean default", "Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron"] as const;
export const KERNELS_SENTENCE = "six kernels in paranoid mode: Lean default and paranoid, lean4lean, nanoda, con-leche, con-ron";

/** The Meta models and tools ProofForge runs, with their roles as README.md and the results state them. */
export const META = [
  { name: "Muse Spark 1.3", role: "The repairer, implementer and prover." },
  { name: "Muse Wonder 1.0", role: "The lemma planner: when an obligation resists direct proof, it proposes helper lemma statements that Spark then proves." },
  { name: "Muse Code", role: "The coding agent that runs with the ProofForge MCP server, the skill and ProofForgeFin." },
  { name: "Muse Spark Open", role: "Meta's open-weight model, measured on the frozen test tasks." },
  { name: "Muse Glimmer 30B", role: "Self-hosted on one Modal H100, measured on the frozen test tasks." },
] as const;
