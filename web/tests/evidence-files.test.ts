import { execFileSync } from "node:child_process";
import { existsSync, readFileSync, readdirSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { COMPOUND, HACKATHON, META_TOOLING } from "../lib/contribution";
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

  it("lists the Compound Passports, and every candidate they name exists", () => {
    const evidence = JSON.parse(readFileSync(path.join(ROOT, "web/public/evidence.json"), "utf8"));
    const listed = evidence.reproduce.passports.map((p: { passport: string }) => p.passport);
    expect(listed).toContain(COMPOUND.vulnerable.passport);
    expect(listed).toContain(COMPOUND.fix.passport);
    for (const r of COMPOUND.museRepairs) expect(listed).toContain(r.passport);
    for (const p of evidence.reproduce.passports as { command: string }[]) {
      const candidate = /--candidate (\S+)/.exec(p.command)![1]!;
      expect(existsSync(path.join(ROOT, candidate)), p.command).toBe(true);
    }
  });

  it("llms.txt states the frontier results and the Meta tooling before the incidents, and lists every page", () => {
    const llms = readFileSync(path.join(ROOT, "web/public/llms.txt"), "utf8");
    const at = (s: string) => {
      const i = llms.indexOf(s);
      expect(i, s).toBeGreaterThanOrEqual(0);
      return i;
    };
    const firstIncident = at(`## ${FLAGSHIPS[0]!.incident}, `);
    expect(at("## Meta models and tools used")).toBeLessThan(firstIncident);
    expect(at("## The frontier, measured")).toBeLessThan(firstIncident);
    expect(at(`Built during the ${HACKATHON.event}`)).toBeLessThan(firstIncident);
    for (const m of META_TOOLING) expect(at(m.name)).toBeLessThan(firstIncident);
    at(`## ${COMPOUND.incident}, ${COMPOUND.date}`);
    const pages = llms.slice(at("## Pages"));
    const routes = (dir: string): string[] =>
      readdirSync(dir, { withFileTypes: true }).flatMap((e) => {
        if (!e.isDirectory()) return e.name === "page.tsx" ? [dir] : [];
        return e.name.startsWith("_") ? [] : routes(path.join(dir, e.name));
      });
    const app = path.join(ROOT, "web/app");
    for (const r of routes(app)) {
      const route = "/" + path.relative(app, r).replace(/\[sha\]/, "{sha256}");
      if (route === "/app/payout") continue;
      expect(pages, route).toContain(`- ${route === "/" ? "/" : route}: `);
    }
  });
});
