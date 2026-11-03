import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { aggregateE2, isE1, isE2, isMuseCode, ledgerComparison, type E2Data, type LedgerComparison } from "../lib/results";
import { METHODS, resultSentence } from "../lib/methods";

describe("published E2 comparison", () => {
  it("includes the tests-only acceptance of the bulk-rounding attack", () => {
    const data = JSON.parse(readFileSync(new URL("../../results/e2-all-1/e2.json", import.meta.url), "utf8")) as E2Data;
    const result = aggregateE2(data);
    expect(result.arms.map((a) => [a.arm, a.falseAccept.count, a.falseAccept.of, a.falseReject.count, a.falseReject.of]))
      .toEqual([["ordinary", 233, 247, 0, 239], ["binary", 1, 247, 0, 239], ["proofforge", 0, 247, 0, 239]]);
    expect(result.families.find((f) => f.family === "payouts")?.arms.binary.falseAccept.count).toBe(1);
  });

  it("does not count a missing binary result as a rejection", () => {
    const data: E2Data = { rows: [{ task: "legacy", family: "payouts", case: "unknown", label: "bad",
      ordinary: { accepted: true }, proofforge: { accepted: false } }] };
    expect(aggregateE2(data).arms.find((a) => a.arm === "binary")?.falseAccept).toEqual({ count: 0, of: 0 });
  });
});

describe("Muse Code experiments from GET /api/results", () => {
  const ledger = JSON.parse(readFileSync(new URL("../../results/wins/ledger.json", import.meta.url), "utf8")) as { comparisons: (LedgerComparison & { experiment: string })[] };
  // The shape server/app.py serves for frontier-4 (tests/test_api_tasks.py checks the server side).
  const f4 = {
    readme: "results/frontier-4/README.md",
    preregistration: "results/frontier-4/PREREGISTRATION.md",
    source: "results/wins/ledger.json",
    comparisons: ledger.comparisons.filter((c) => c.experiment === "frontier-4"),
    runs: [],
  };

  it("is told apart from the E1 and E2 sets", () => {
    expect(isMuseCode(f4)).toBe(true);
    expect(isE1(f4)).toBe(false);
    expect(isE2(f4)).toBe(false);
  });

  it("words a comparison as the /methods page does", () => {
    const c = f4.comparisons.find((x) => x.id === "frontier-4/rw-compound-comp")!;
    const m = METHODS.entries.find((e) => e.id === "frontier-4")!.tasks.find((t) => t.id === c.id)!;
    expect(ledgerComparison(c)).toEqual(m);
    expect(resultSentence(ledgerComparison(c))).toMatch(/^8 of 10 runs verified with ProofForge, 0 of 10 on its own/);
  });
});
