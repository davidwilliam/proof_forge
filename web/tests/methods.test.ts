import { execFileSync } from "node:child_process";
import { existsSync, readFileSync, readdirSync } from "node:fs";
import path from "node:path";
import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, it } from "vitest";
import MethodsPage from "../app/methods/page";
import { METHODS, pooledSentence, resultSentence } from "../lib/methods";
import { ROOT } from "../scripts/lib/results.mjs";

const read = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");
const flat = (s: string) => s.replace(/\s+/g, " ");
const ledger = JSON.parse(read("results/wins/ledger.json")) as {
  comparisons: { id: string; experiment: string; scope: string; alone: { verified: number; runs: number }; proofforge: { verified: number; runs: number }; test: { p: number } | null }[];
};

describe("the /methods page data (generated/methods.json)", () => {
  it("is up to date with the preregistrations, the READMEs and the ledger", () => {
    expect(() => execFileSync(process.execPath, [path.join(ROOT, "web/scripts/methods.mjs"), "--check"], { stdio: "pipe" })).not.toThrow();
  });

  it("lists every results/*/PREREGISTRATION.md once", () => {
    const dirs = readdirSync(path.join(ROOT, "results")).filter((d) => existsSync(path.join(ROOT, "results", d, "PREREGISTRATION.md")));
    expect(METHODS.entries.map((e) => e.id).sort()).toEqual(dirs.sort());
    expect(dirs.length).toBe(7);
  });

  it("copies each question, run count and primary test from its preregistration", () => {
    for (const e of METHODS.entries) {
      const md = flat(read(e.prereg));
      const question = flat(md.split("## Question")[1]!.split("## ")[0]!);
      expect(question.startsWith(` ${e.question}`), e.id).toBe(true);
      expect(md, e.id).toContain(e.runsText);
      expect(e.runsText, e.id).toContain(String(e.runs));
      expect(md, e.id).toContain(e.primaryTest);
      expect(e.primaryTest, e.id).toContain(e.testName);
      expect(md, e.id).toContain(`Written on ${e.written}`);
      for (const a of e.addenda) expect(md, e.id).toContain(`## ${a}`);
    }
  });

  it("names the commit that added each preregistration", () => {
    for (const e of METHODS.entries) {
      const added = execFileSync("git", ["-C", ROOT, "log", "--diff-filter=A", "--format=%H", "--", e.prereg], { encoding: "utf8" }).trim().split("\n").pop();
      expect(added, e.id).toBe(e.commitFull);
      expect(e.commitFull.startsWith(e.commit)).toBe(true);
    }
  });

  it("is finished exactly when the README says measured, with the ledger's figures", () => {
    for (const e of METHODS.entries) {
      const readme = `results/${e.id}/README.md`;
      const measured = existsSync(path.join(ROOT, readme)) && /^Status: measured\./m.test(read(readme));
      expect(e.status === "finished", e.id).toBe(measured);
      if (!measured) {
        expect(e.tasks).toEqual([]);
        continue;
      }
      expect(e.tasks.length, e.id).toBeGreaterThan(0);
      for (const t of [...e.tasks, ...e.pooled]) {
        const c = ledger.comparisons.find((x) => x.id === t.id)!;
        expect(c, t.id).toBeDefined();
        expect([t.alone.verified, t.alone.runs, t.proofforge.verified, t.proofforge.runs]).toEqual([c.alone.verified, c.alone.runs, c.proofforge.verified, c.proofforge.runs]);
        expect(t.test?.p).toBe(c.test?.p);
      }
    }
  });

  it("states the known status of the experiments still without a result", () => {
    const by = new Map(METHODS.entries.map((e) => [e.id, e]));
    if (!existsSync(path.join(ROOT, "results/hard-task-2/README.md"))) expect(by.get("hard-task-2")!.status).toBe("running");
    if (!existsSync(path.join(ROOT, "results/frontier-4/README.md"))) expect(by.get("frontier-4")!.status).toBe("running");
  });

  it("leads each result with figures, p as a number, and no hedging or significance claims", () => {
    const sentences = METHODS.entries.flatMap((e) => [...e.tasks.map(resultSentence), ...e.pooled.map(pooledSentence)]);
    expect(sentences.length).toBeGreaterThan(0);
    for (const s of sentences) {
      expect(s).toMatch(/^\d+ of \d+/);
      expect(s).not.toMatch(/significan|not shown|did not|only|e-\d/i);
    }
    const oz = resultSentence(METHODS.entries.find((e) => e.id === "frontier-2")!.tasks.find((t) => t.task === "rw-oz-sqrt")!);
    expect(oz).toBe("10 of 10 runs verified with ProofForge, 0 of 10 on its own; $1.99 per verified run with ProofForge (one-sided Fisher exact p = 0.0000054; one-sided Mann-Whitney U, ProofForge spends fewer list dollars per run, p = 0.0000054).");
    expect(read("results/frontier-2/README.md")).toContain("p = 5.4e-6");
  });

  it("renders every plan with its links on the server", () => {
    const html = renderToStaticMarkup(createElement(MethodsPage));
    for (const e of METHODS.entries) {
      expect(html).toContain(`id="${e.id}"`);
      expect(html).toContain(`/blob/main/${e.prereg}`);
      expect(html).toContain(`/commit/${e.commitFull}`);
    }
    expect(html).not.toMatch(/not significant/i);
  });
});
