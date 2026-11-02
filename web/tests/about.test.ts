import { readFileSync, readdirSync, statSync } from "node:fs";
import path from "node:path";
import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, it } from "vitest";
import AboutPage from "../app/about/page";
import Home from "../app/page";
import { EMAIL_FALLBACK } from "../components/Email";
import { BUILT, DEPENDENCIES, KERNELS, KERNELS_SENTENCE, ORIGIN } from "../lib/about";
import { ROOT } from "../scripts/lib/results.mjs";

const read = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");
const flat = (s: string) => s.replace(/\s+/g, " ");
// Built from parts so this file does not hold the address either.
const ADDRESS = ["contact", "davidwsilva.com"].join("@");
// harness/fin_kernels.py lists the kernels in this order.
const ORDER = ["Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default"];

describe("the contact address", () => {
  const pages = { "/about": renderToStaticMarkup(createElement(AboutPage)), "/": renderToStaticMarkup(createElement(Home)) };

  it("never appears in plain text in the server HTML of /about and /", () => {
    for (const [p, html] of Object.entries(pages)) {
      expect(html, p).not.toContain(ADDRESS);
      expect(html, p).not.toContain("mailto:");
      expect(html, p).toContain(EMAIL_FALLBACK);
    }
  });

  it("is in no source file or published text file of the site", () => {
    const files: string[] = [];
    const walk = (d: string) => {
      for (const n of readdirSync(d)) {
        const p = path.join(d, n);
        if (statSync(p).isDirectory()) walk(p);
        else if (/\.(tsx?|mjs|css|json|txt|svg|md)$/.test(n)) files.push(p);
      }
    };
    for (const d of ["app", "components", "lib", "generated", "public"]) walk(path.join(ROOT, "web", d));
    for (const f of files) expect(readFileSync(f, "utf8").includes(ADDRESS), f).toBe(false);
  });
});

describe("the /about page", () => {
  it("copies its origin facts from ORIGIN.md and README.md", () => {
    const origin = flat(read("ORIGIN.md"));
    const readme = flat(read("README.md"));
    expect(origin).toContain(`kickoff ${ORIGIN.kickoff}`);
    expect(origin).toContain(`submissions due ${ORIGIN.submissionsDue}`);
    expect(origin).toContain(ORIGIN.started);
    expect(origin).toContain(ORIGIN.agents);
    expect(origin).toContain(ORIGIN.noEarlierCode);
    expect(readme).toContain(`first commit \`${ORIGIN.firstCommit}\`, ${ORIGIN.firstCommitAt}`);
    expect(readme).toContain(`That includes ${BUILT.slice(0, -1).join(", ")} and ${BUILT[BUILT.length - 1]}.`);
    for (const d of DEPENDENCIES) expect(origin).toContain(`| ${d.name} | ${d.use} |`);
    expect(readme).toContain(KERNELS_SENTENCE);
    expect(read("harness/fin_kernels.py")).toContain(`KERNELS = [${[...KERNELS].sort((a, b) => ORDER.indexOf(a) - ORDER.indexOf(b)).map((k) => `"${k}"`).join(", ")}]`);
  });

  it("states the repository's license, Apache 2.0, with the name and logo excluded as NOTICE says", () => {
    expect(read("LICENSE")).toContain("Apache License\n                           Version 2.0, January 2004");
    expect(read("NOTICE")).toContain("grants no permission to use them");
    expect(read("README.md")).toContain("Apache License 2.0 (`LICENSE`)");
    expect(JSON.parse(read("web/package.json")).license).toBe("Apache-2.0");
    const html = renderToStaticMarkup(createElement(AboutPage));
    expect(html).toContain("Apache License 2.0");
    expect(html).toContain("The ProofForge name and logo are not");
  });
});
