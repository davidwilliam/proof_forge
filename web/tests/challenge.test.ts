import { execFileSync } from "node:child_process";
import { readFileSync, readdirSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { CHALLENGE, balanceRows, challengeFacts, median, payoutWitness, recordedLabel } from "../lib/challenge";
import { ROOT } from "../scripts/lib/results.mjs";

// Every figure the /challenge page shows, pinned to the committed files it comes from.
const text = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");
const json = (rel: string) => JSON.parse(text(rel));
const hidden = readdirSync(path.join(ROOT, "hidden")).sort();
const reliability = readdirSync(path.join(ROOT, "reports/reliability"))
  .filter((f) => f.endsWith(".json"))
  .sort()
  .map((f) => json(`reports/reliability/${f}`));
const calls = reliability.flatMap((r) => r.session_records.map((s: { steps: Record<string, { ok: boolean; seconds: number }> }) => s.steps["hidden challenge"]!));

describe("generated/challenge.json", () => {
  it("is up to date with its sources", () => {
    expect(() => execFileSync(process.execPath, [path.join(ROOT, "web/scripts/challenge.mjs"), "--check"], { stdio: "pipe" })).not.toThrow();
  });

  it("lists every hidden variant with its issue report", () => {
    expect(CHALLENGE.variants.map((v) => v.id)).toEqual(hidden);
    for (const v of CHALLENGE.variants) {
      const t = json(`hidden/${v.id}/task.json`);
      expect(v.requirements).toEqual(t.requirements.map((r: [string, string]) => r[0]));
      expect(v.issue).toBe(t.issue);
    }
  });

  it("reads the property cases and deadline from the endpoint", () => {
    const app = text("server/app.py");
    expect(app).toContain(`binary_check.property_tests(project, t, ${CHALLENGE.server.propertyCases},`);
    expect(app).toContain(`seconds("PF_CHALLENGE_DEADLINE_S", ${CHALLENGE.server.deadlineS})`);
    expect(CHALLENGE.server.propertyCases).toBe(300);
    expect(text("infra/reliability.py")).toContain(`{"variant": "${CHALLENGE.reliability.variant}"}`);
  });
});

describe("the page's figures", () => {
  const f = challengeFacts();

  it("counts the variants and their validation", () => {
    expect(f.variants).toBe(3);
    const refs = hidden.flatMap((id) => Object.values(json(`hidden/${id}/validation.json`).checks.references) as { judge: string; binary: string }[]);
    expect(f.references).toBe(refs.length);
    expect(f.referencesAccepted).toBe(refs.filter((r) => r.judge === "ACCEPT" && r.binary === "PASS").length);
    expect([f.referencesAccepted, f.references]).toEqual([6, 6]);
    expect(f.startsRefuted).toBe(hidden.filter((id) => json(`hidden/${id}/validation.json`).checks.start.binary === "REFUTED").length);
    expect(f.startsRefuted).toBe(3);
  });

  it("counts the recorded calls of the deployed challenge", () => {
    expect(f.calls).toBe(calls.length);
    expect(f.refuted).toBe(calls.filter((c) => c.ok).length);
    expect([f.refuted, f.calls]).toEqual([40, 40]);
    expect(f.medianSeconds).toBe(median(calls.map((c) => c.seconds)));
    expect(f.medianSeconds!.toFixed(2)).toBe("0.23");
    expect([f.minSeconds, f.maxSeconds]).toEqual([0.2, 0.47]);
    expect(CHALLENGE.reliability.runs.map((r) => recordedLabel(r.recordedAt))).toEqual(["2026-10-28 02:15", "2026-10-28 02:33"]);
  });
});

describe("payout witnesses", () => {
  it("reads a committed witness: recipients receive more than the source is debited", () => {
    const w = json("hidden/payouts-flagship-h3/validation.json").checks.start.witness;
    const p = payoutWitness(w.input, w.output)!;
    expect(p).not.toBeNull();
    const rows = balanceRows(p);
    const src = rows.find((r) => r.account === p.request.source)!;
    const paid = rows.filter((r) => p.request.recipients.includes(r.account)).reduce((a, r) => a + r.delta!, 0);
    expect(src.delta).toBe(-p.request.amount);
    expect(paid).toBeGreaterThan(p.request.amount);
  });

  it("returns null for other shapes", () => {
    expect(payoutWitness({ x: 1 }, { outcome: "ok" })).toBeNull();
    expect(payoutWitness(null, null)).toBeNull();
  });
});
