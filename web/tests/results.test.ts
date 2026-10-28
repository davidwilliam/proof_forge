import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { aggregateE2, type E2Data } from "../lib/results";

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
