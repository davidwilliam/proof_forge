import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { LIBRARY_COUNTS as L } from "../lib/library-data";
import { ROOT } from "../scripts/lib/results.mjs";
import { countDeclarations } from "../scripts/library.mjs";

const text = (rel: string) => readFileSync(path.join(ROOT, rel), "utf8").replace(/\s+/g, " ");
const json = (rel: string) => JSON.parse(readFileSync(path.join(ROOT, rel), "utf8"));
const fmt = (n: number) => n.toLocaleString("en-US");

describe("ProofForgeFin counts (generated/library.json)", () => {
  it("is up to date with the library's sources, lib/README.md and the kernel runs", () => {
    expect(() => execFileSync(process.execPath, [path.join(ROOT, "web/scripts/library.mjs"), "--check"], { stdio: "pipe" })).not.toThrow();
  });

  it("recounts the declarations and agrees with lib/README.md", () => {
    expect(countDeclarations("ProofForgeFin")).toEqual({ files: L.files, theorems: L.theorems, definitions: L.definitions });
    expect(countDeclarations("ProofForgeFinDemo")).toMatchObject({ files: L.demoFiles, theorems: L.demoTheorems });
    const readme = text("lib/README.md");
    expect(readme).toContain(`The library has ${fmt(L.theorems)} theorems and ${fmt(L.definitions)} definitions in ${L.files} files`);
    expect(readme).toContain(`(${L.demoTheorems} theorems in ${L.demoFiles} files)`);
  });

  it("takes the latest full kernel run lib/README.md reports, after the compound-gaps-1 additions", () => {
    expect(L.latestFullRun.safeConstants).toBe(10909);
    expect(text("lib/README.md")).toContain(
      `A full run of \`tests/test_fin_kernels.py\` with the additions exports ${fmt(L.latestFullRun.safeConstants)} safe constants of the library and its demonstrations, which all six kernels accept, with \`leanchecker\` exiting 0.`,
    );
  });

  it("reads the committed kernel runs from their JSON", () => {
    const full = json(L.committedFullRun.file);
    expect([L.committedFullRun.safeConstants, L.committedFullRun.modulesReplayed, L.committedFullRun.passed]).toEqual([full.safe_exported, full.leanchecker.modules, true]);
    expect(text("lib/README.md")).toContain(`all ${fmt(L.committedFullRun.safeConstants)} safe constants`);
    expect(text("lib/README.md")).toContain(`accepts all ${L.committedFullRun.modulesReplayed} modules`);
    const mod = json(L.latestModuleRun.file);
    expect([L.latestModuleRun.constants, L.latestModuleRun.theorems, L.latestModuleRun.modules]).toEqual([mod.safe_exported, mod.theorems, mod.modules]);
    expect(text("results/library-compound-gaps-1/README.md") + text("lib/README.md")).toContain(`The ${L.latestModuleRun.constants} constants of`);
  });
});
