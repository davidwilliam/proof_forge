import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import path from "node:path";
import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";
import { describe, expect, it } from "vitest";
import VerifyPage from "../app/verify/page";
import guide from "../generated/verify-guide.json";
import { ROOT } from "../scripts/lib/results.mjs";

const read = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8");

describe("the /verify page", () => {
  it("generated/verify-guide.json is up to date with README.md, AGENTS.md and bin/proofforge", () => {
    expect(() => execFileSync(process.execPath, [path.join(ROOT, "web/scripts/verify-guide.mjs"), "--check"], { stdio: "pipe" })).not.toThrow();
  });

  it("shows only commands that the repository's documents state", () => {
    const readme = read("README.md");
    for (const b of [guide.quickstart, guide.reproduce, guide.running]) expect(readme).toContain(b.code);
    expect(readme).toContain("bin/proofforge verify results/cetus-1/repair-A1-1/passport.json --candidate results/cetus-1/repair-A1-1/final.lean");
    expect(read("AGENTS.md")).toContain("`bin/proofforge verify passport.json --candidate <file>`");
    const html = renderToStaticMarkup(createElement(VerifyPage));
    expect(html).toContain("docker build -t proofforge-lean:4.35.0 -f infra/docker/Dockerfile.lean infra/docker");
    expect(html).toContain("reproduced, except the executable hash (linux/amd64 vs linux/arm64)");
  });
});
