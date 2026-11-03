import { readFileSync } from "node:fs";
import path from "node:path";
import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, it } from "vitest";
import Home from "../app/page";
import { COMPARISON, COMPOUND, COMPOUND_CASE, COST_PER_VERIFIED, LIBRARY } from "../lib/contribution";
import { FEATURED, FLAGSHIPS } from "../lib/flagships";
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
  it("leads every Compound passage with frontier-4 and states nothing it contradicts", () => {
    const readme = readFileSync(path.join(ROOT, "results/frontier-4/README.md"), "utf8").replace(/\s+/g, " ");
    expect(readme).toContain("Muse Code with ProofForge verified 8 of 10 runs; on its own it verified 0 of 10");
    expect(readme).toContain("0 of 30, against 8 of 10 with ProofForge");
    const first = readFileSync(path.join(ROOT, "results/frontier-3/README.md"), "utf8").replace(/\s+/g, " ");
    expect(first).toContain("Muse Code with ProofForge verified 2 of 10 runs; on its own it verified 0 of 10");
    has(
      "On Compound, Muse Code (Muse Spark 1.3) with ProofForge verified 8 of 10 runs in frontier-4; on its own it verified 0 of 10, and 0 of 30 with the runs on its own of frontier-2 and frontier-3 pooled. The first verified repairs of this task in any measured run came in frontier-3, 2 of 10 runs with ProofForge.",
    );
    has("Muse Code with ProofForge verified Compound in 8 of 10 runs");
    has("Before frontier-3, no run of any method had proved all 8 of Compound's requirements");
    for (const stale of ["On Compound nothing succeeds", "No Muse run has proved Compound", "no run of any method has proved all"]) {
      expect(text).not.toContain(stale);
    }
    // The table's Compound row leads with Muse Code.
    has("8 of 10 Muse Code with ProofForge, frontier-4");
    has("2 of 10 Muse Code with ProofForge, frontier-3");
    has("0 of 30 Muse Code on its own, frontier-2 to frontier-4");
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

  it("shows Compound Proposal 62 as the sixth case, last, with its own tab, panel and deep link", () => {
    const tabs = [...html.matchAll(/id="case-tab-([a-z0-9-]+)"/g)].map((m) => m[1]);
    expect(tabs).toEqual([FEATURED.key, ...FLAGSHIPS.filter((f) => f !== FEATURED).map((f) => f.key), "compound"]);
    expect(html).toContain('id="case-compound"');
    expect(html).toContain('aria-controls="case-compound"');
    expect(html).toContain('href="#case-compound"');
    // The tab: name, year and the README's dollar figure with the words that bound it.
    const tab = /<button[^>]*id="case-tab-compound"[^>]*>(.*?)<\/button>/s.exec(html)![1]!;
    expect(tab).toContain("Compound Proposal 62");
    expect(tab).toContain("2021");
    expect(tab).toContain("at worst about");
    expect(tab).toContain("$80 million");
    expect([...tab.matchAll(/data-v="([A-Z]+)"/g)].map((m) => m[1])).toEqual(["REFUTED", "UNRESOLVED", "VERIFIED", "VERIFIED"]);
    // The panel: loss in COMP, the bug, the trail, both verdicts and the real code.
    const panel = /<div id="case-compound"[^>]*>(.*?)<\/article>/s.exec(html)![1]!;
    expect(panel).toContain("At worst 280,000 COMP");
    expect(panel).toContain("about $80 million at the time");
    expect(panel).toContain(COMPOUND.loss.basis);
    for (const s of COMPOUND.loss.sources) expect(panel).toContain(s);
    for (const r of COMPOUND_CASE.repairs) expect(panel).toContain(r.passport.sha256.slice(0, 16));
    expect(panel).toContain(COMPOUND_CASE.port.sha256.slice(0, 12));
    expect(panel).toContain(COMPOUND_CASE.fix.sha256.slice(0, 12));
    expect([...panel.matchAll(/class="tr-step" data-verdict="([A-Z]+)" data-author="([a-z]+)"/g)].map((m) => `${m[1]} ${m[2]}`)).toEqual([
      "REFUTED upstream",
      "UNRESOLVED muse",
      "VERIFIED muse",
      "VERIFIED upstream",
    ]);
    has("0 of 30 runs verified");
    has("8 of 10 runs verified");
    // The README's code spans become <code>.
    has(COMPOUND.bug.replace(/`([^`]+)`/g, " $1 "));
    expect(panel).toContain("<code>&gt;=</code>");
    has(COMPOUND.vulnerable.finding);
    has("Verified in 8 of 10 runs of frontier-4, at $3.13 to $8.67 at list prices per run");
    has("REQ-REWARDS-BOUNDED, REQ-ACCOUNT-BOUNDED and REQ-NO-BACKDATED-REWARDS");
    expect(panel).toContain(`${COMPOUND.realCode.sequences} sequences`);
    expect(panel).toContain("503 sequences");
    for (const row of COMPOUND.realCode.rows) has(row.note);
    for (const n of COMPOUND.notProved) has(n);
    // The section names all six incidents.
    has(`${FLAGSHIPS.find((f) => f.key === "hundred")!.incident} and Compound Proposal 62, step by step`);
  });

  it("lists every headline gain with its text and note", () => {
    has("OpenZeppelin Math.sqrt");
    has("Compound Proposal 62");
    has("Vyper sqrt(), CVE-2025-26622");
    has("Balancer V2 rounding repair");
    has("Seeded bad candidates accepted by ProofForge");
  });
});
