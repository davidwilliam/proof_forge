import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { FIX_TARGETS, checkPath, statusDifferences, summarizePassport, type RecordedCheck } from "../lib/checkfix";
import { COMPARISON } from "../lib/contribution";
import { FLAGSHIPS } from "../lib/flagships";
import { ROOT, readPassport } from "../scripts/lib/results.mjs";

const publicFile = (p: string) => path.join(ROOT, "web/public", p);
const recorded = (task: string, key: string) => JSON.parse(readFileSync(publicFile(checkPath(task, key, "json")), "utf8")) as RecordedCheck;

describe("Check a fix", () => {
  it("public/check is up to date", () => {
    const script = path.join(ROOT, "web/scripts/check-fixes.mjs");
    expect(() => execFileSync(process.execPath, [script, "--check"], { stdio: "pipe" })).not.toThrow();
  });

  it("covers every task of the comparison and every flagship", () => {
    expect(FIX_TARGETS.map((t) => t.task).sort()).toEqual(COMPARISON.map((r) => r.task).sort());
    for (const f of FLAGSHIPS) expect(FIX_TARGETS.find((t) => t.key === f.key)?.task, f.key).toBe(path.basename(f.task));
  });

  for (const t of FIX_TARGETS)
    it(t.task, () => {
      const f = FLAGSHIPS.find((x) => x.key === t.key);
      for (const c of t.candidates) {
        const r = recorded(t.task, c.key);
        const facts = readPassport(c.recorded);
        expect(r.passportSha256).toBe(facts.sha256);
        expect(r.status).toBe(facts.status);
        expect(Object.fromEntries(r.requirements.map((q) => [q.id, q.status]))).toEqual(facts.requirements);
        expect(readFileSync(publicFile(checkPath(t.task, c.key, "lean")), "utf8")).toBe(readFileSync(path.join(ROOT, c.source), "utf8"));
        if (c.author === "muse" && f) expect(r.passportSha256).toBe(f.repair.passport.sha256);
        if (c.author === "muse") expect(r.status).toBe("VERIFIED");
        if (c.key === "original") {
          expect(r.status).toBe("REFUTED");
          expect(r.counterexamples?.some((x) => x.kernelChecked && x.kernels === 6)).toBe(true);
        }
      }
    });

  it("the Cetus hotfix is the first choice and is refuted by a kernel-checked counterexample", () => {
    const cetus = FIX_TARGETS[0]!;
    expect(cetus.key).toBe("cetus");
    const r = recorded(cetus.task, cetus.candidates[0]!.key);
    expect(cetus.candidates[0]!.key).toBe("pr6-hotfix");
    expect(r.status).toBe("REFUTED");
    expect(r.counterexamples).toEqual([
      expect.objectContaining({ requirement: "REQ-SHLW-EXACT", kernelChecked: true, kernels: 6, statement: "¬ (ShlwExact checkedShlw)" }),
    ]);
  });
});

describe("summarizePassport", () => {
  const p = {
    status: "REFUTED",
    passport_sha256: "ab",
    requirements: [
      { id: "REQ-A", text: "REQ-A: a holds.", status: "REFUTED", witness: { message: "a fails at 3" } },
      { id: "REQ-B", text: null, status: "UNRESOLVED", witness: null },
    ],
    checks: { comparator_kernels: [], property_tests: { cases: 1001 } },
    executable: { status: "REFUTED" },
  };

  it("strips the id from the requirement text and keeps the witness", () => {
    const s = summarizePassport(p);
    expect(s.requirements).toEqual([
      { id: "REQ-A", text: "a holds.", status: "REFUTED", witness: "a fails at 3" },
      { id: "REQ-B", text: null, status: "UNRESOLVED", witness: null },
    ]);
    expect(s.counterexamples).toBeNull();
    expect(s.propertyCases).toBe(1001);
  });

  it("reports the requirements whose status differs", () => {
    const a = summarizePassport(p);
    const b = summarizePassport({ ...p, requirements: [p.requirements[0]!, { ...p.requirements[1]!, status: "VERIFIED" }] });
    expect(statusDifferences(a, a)).toEqual([]);
    expect(statusDifferences(a, b)).toEqual(["REQ-B"]);
  });
});
