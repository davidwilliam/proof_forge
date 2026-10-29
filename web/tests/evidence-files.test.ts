import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { FLAGSHIPS } from "../lib/flagships";
import { ROOT } from "../scripts/lib/results.mjs";

describe("published machine-readable evidence", () => {
  it("public/evidence.json and public/llms.txt are up to date", () => {
    const script = path.join(ROOT, "web/scripts/evidence.mjs");
    expect(() => execFileSync(process.execPath, [script, "--check"], { stdio: "pipe" })).not.toThrow();
  });

  it("lists every flagship Passport with its reproduction command", () => {
    const evidence = JSON.parse(readFileSync(path.join(ROOT, "web/public/evidence.json"), "utf8"));
    const listed = new Map(evidence.reproduce.passports.map((p: { sha256: string; command: string }) => [p.sha256, p.command]));
    for (const f of FLAGSHIPS) {
      expect(listed.get(f.repair.passport.sha256)).toBe(f.repair.passport.reproduce);
      if (f.vulnerable.passport) expect(listed.get(f.vulnerable.passport.sha256)).toBe(f.vulnerable.passport.reproduce);
    }
    const llms = readFileSync(path.join(ROOT, "web/public/llms.txt"), "utf8");
    for (const f of FLAGSHIPS) expect(llms).toContain(f.repair.passport.reproduce);
  });
});
