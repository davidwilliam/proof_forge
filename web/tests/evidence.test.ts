import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { E1, E2 } from "../lib/evidence";
import { aggregateE2, type E1Summary, type E2Data } from "../lib/results";

const read = <T>(rel: string) => JSON.parse(readFileSync(new URL(`../../${rel}`, import.meta.url), "utf8")) as T;

describe("home page figures match the committed result files", () => {
  it("E2", () => {
    const data = read<E2Data>(E2.source);
    expect(data.rows.filter((r) => r.label === "bad").length).toBe(E2.bad);
    expect(data.rows.filter((r) => r.label === "good").length).toBe(E2.good);
    const agg = aggregateE2(data);
    for (const arm of E2.arms) {
      const a = agg.arms.find((x) => x.arm === arm.key)!;
      expect([a.falseAccept.count, a.falseAccept.of, a.falseReject.count, a.falseReject.of]).toEqual([arm.badAccepted, E2.bad, arm.goodRejected, E2.good]);
    }
  });

  it("E1", () => {
    const { summary } = read<{ summary: E1Summary }>(E1.source);
    for (const arm of E1.arms) expect(summary.arms?.[arm.key]).toMatchObject({ completed: arm.completed, n: E1.tasks });
    expect(summary.pairs?.["A1-A0"]?.mcnemar_p).toBe(E1.mcnemarP);
    expect(summary.pairs?.["A2-A0"]?.mcnemar_p).toBe(E1.mcnemarP);
    const coverage = read<{ batch_spent_usd_list: number }>("results/e1-test-1/coverage.json");
    expect(Math.round(coverage.batch_spent_usd_list * 100) / 100).toBe(E1.batchUsdList);
    expect(readFileSync(new URL("../../results/e1-test-1/e1.md", import.meta.url), "utf8")).toContain(`passes ${E1.propertyCases} property cases`);
  });
});
