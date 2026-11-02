import { readFileSync } from "node:fs";
import path from "node:path";
import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, it } from "vitest";
import Home from "../app/page";
import { COMPARISON, COST_PER_VERIFIED, LIBRARY } from "../lib/contribution";
import { FLAGSHIPS } from "../lib/flagships";
import { LIBRARY_COUNTS } from "../lib/library-data";
import { ROOT } from "../scripts/lib/results.mjs";

/** The server-rendered home page as plain text: tags dropped, entities decoded, white space collapsed. */
const html = renderToStaticMarkup(createElement(Home));
const text = html
  .replace(/<[^>]+>/g, " ")
  .replace(/&#x27;|&#39;/g, "'")
  .replace(/&quot;/g, '"')
  .replace(/&amp;/g, "&")
  .replace(/&lt;/g, "<")
  .replace(/&gt;/g, ">")
  .replace(/\s+/g, " ");
const has = (s: string) => expect(text, s).toContain(s.replace(/\s+/g, " "));

describe("the home page below the hero, as served", () => {
  it("leads every Compound passage with frontier-3 and states nothing it contradicts", () => {
    const readme = readFileSync(path.join(ROOT, "results/frontier-3/README.md"), "utf8").replace(/\s+/g, " ");
    expect(readme).toContain("Muse Code with ProofForge verified 2 of 10 runs; on its own it verified 0 of 10");
    expect(readme).toContain("2 of 10 with ProofForge against 0 of 20");
    has(
      "On Compound, Muse Code (Muse Spark 1.3) with ProofForge verified 2 of 10 runs in frontier-3 (proofforge-full-5 and proofforge-full-9), the first verified repairs of this task in any measured run; on its own it verified 0 of 10, and 0 of 20 with the runs on its own of frontier-2 pooled.",
    );
    has("Muse Code with ProofForge verified Compound in 2 of 10 runs");
    has("Before frontier-3, no run of any method had proved all 8 of Compound's requirements");
    for (const stale of ["On Compound nothing succeeds", "No Muse run has proved Compound", "no run of any method has proved all"]) {
      expect(text).not.toContain(stale);
    }
    // The table's Compound row leads with Muse Code.
    has("2 of 10 Muse Code with ProofForge, frontier-3");
    has("0 of 20 Muse Code on its own, frontier-2 and frontier-3");
  });

  it("keeps the earlier Compound facts as history", () => {
    has("in baseline-flagships-1 ended early, when one model call reached its 600 s timeout");
    has("the two in library-1 ran the full 4 hours");
    has("proved at most 4 of the eight requirements and none of the three sequence bounds");
    has(`Passport ${LIBRARY.compoundLivePassport.slice(0, 8)}`);
  });

  it("shows the library counts of generated/library.json", () => {
    const fmt = (n: number) => n.toLocaleString("en-US");
    has(`${fmt(LIBRARY_COUNTS.theorems)} theorems and ${fmt(LIBRARY_COUNTS.definitions)} definitions in ${LIBRARY_COUNTS.files} Lean files`);
    has(`All ${fmt(LIBRARY_COUNTS.latestFullRun.safeConstants)} safe constants of the library and its demonstrations are accepted by the six kernels`);
    has(`checked ${fmt(LIBRARY_COUNTS.committedFullRun.safeConstants)}, and leanchecker replayed all ${LIBRARY_COUNTS.committedFullRun.modulesReplayed} modules`);
    expect(text).not.toContain("All 10,128 constants");
  });

  it("keeps the comparison's facts: the cost per verified run and every failure", () => {
    for (const c of COST_PER_VERIFIED) has(`${c.planner.verified} of ${c.planner.runs} runs verified at $${c.planner.usdPerVerified.toFixed(2)} per verified run`);
    for (const r of COMPARISON) has(`${r.incident}, ${r.year}`);
    has("The figures that need ProofForge in every row are the specification each run proves");
  });

  it("renders every incident's facts, including the hidden panels and the attack steps", () => {
    for (const f of FLAGSHIPS) {
      has(f.bug);
      has(f.loss.basis);
      for (const s of f.attack) has(s.text);
      if (f.outcome) has(f.outcome);
      for (const v of f.timeline) {
        has(v.short);
        has(v.finding);
      }
      if (f.realCode) for (const row of f.realCode.rows) has(row.note);
      expect(html).toContain(`id="case-${f.key}"`);
    }
  });

  it("lists every headline gain with its text and note", () => {
    has("OpenZeppelin Math.sqrt");
    has("Compound Proposal 62");
    has("Vyper sqrt(), CVE-2025-26622");
    has("Balancer V2 rounding repair");
    has("Seeded bad candidates accepted by ProofForge");
  });
});
