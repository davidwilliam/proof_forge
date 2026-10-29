// Headline figures shown on the home page. Each is copied from a committed result file named
// beside it; tests/evidence.test.ts recomputes every one from those files.

/** E2: the same candidate artifacts checked three ways. */
export const E2 = {
  source: "results/e2-all-1/e2.json",
  // results/e2-all-1/e2.json: rows with label "bad"
  bad: 247,
  // results/e2-all-1/e2.json: rows with label "good"
  good: 239,
  arms: [
    {
      key: "ordinary",
      label: "Ordinary checking",
      detail: "The project builds, theorem names are present, the axiom audit is clean.",
      // results/e2-all-1/e2.json: bad rows with ordinary.accepted
      badAccepted: 233,
      // results/e2-all-1/e2.json: good rows without ordinary.accepted
      goodRejected: 0,
    },
    {
      key: "binary",
      label: "Rebuild and property tests only",
      detail: "The executable rebuilt from the locked project passes the task's property tests.",
      // results/e2-all-1/e2.json: bad rows with proofforge.binary "PASS"
      badAccepted: 1,
      // results/e2-all-1/e2.json: good rows with proofforge.binary other than "PASS"
      goodRejected: 0,
    },
    {
      key: "proofforge",
      label: "ProofForge",
      detail: "Tree check, implementation scan, Comparator in a fresh sandbox, leanchecker, rebuild and tests.",
      // results/e2-all-1/e2.json: bad rows with proofforge.accepted
      badAccepted: 0,
      // results/e2-all-1/e2.json: good rows without proofforge.accepted
      goodRejected: 0,
    },
  ],
} as const;

/** E1: Muse Spark 1.3 repair arms on the frozen test tasks. */
export const E1 = {
  source: "results/e1-test-1/e1.json",
  // results/e1-test-1/e1.json: summary.arms.*.n
  tasks: 30,
  // results/e1-test-1/e1.md: "Tasks: 30. A repair is completed when ... its binary passes 2000 property cases"
  propertyCases: 2000,
  arms: [
    // results/e1-test-1/e1.json: summary.arms.A0.completed
    { key: "A0", label: "Compile-and-retry", detail: "Muse Spark sees Lean errors and the axiom audit only.", completed: 28 },
    // results/e1-test-1/e1.json: summary.arms.A1.completed
    {
      key: "A1",
      label: "ProofForge harness",
      detail: "Behavior first, one dialog per proof obligation, snippet checks and property tests.",
      completed: 30,
    },
    // results/e1-test-1/e1.json: summary.arms.A2.completed
    { key: "A2", label: "Harness and planner", detail: "A1 with Muse Wonder proposing helper lemmas.", completed: 30 },
  ],
  // results/e1-test-1/e1.json: summary.pairs["A1-A0"].mcnemar_p and summary.pairs["A2-A0"].mcnemar_p
  mcnemarP: 0.5,
  // results/e1-test-1/coverage.json: batch_spent_usd_list (70.0886), rounded to cents
  batchUsdList: 70.09,
} as const;
