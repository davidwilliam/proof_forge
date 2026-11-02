// ProofForgeFin's counts as the pages read them: generated/library.json, written by
// scripts/library.mjs from the library's sources, lib/README.md and the committed kernel runs.
// tests/library.test.ts fails when the generated file is stale.

import data from "@/generated/library.json";

export interface LibraryCounts {
  generator: string;
  source: { declarations: string; readme: string };
  files: number;
  theorems: number;
  definitions: number;
  demoFiles: number;
  demoTheorems: number;
  latestFullRun: { safeConstants: number; kernels: number; leanchecker: string; when: string; source: string };
  committedFullRun: { file: string; safeConstants: number; theorems: number; modulesReplayed: number; passed: boolean };
  latestModuleRun: { file: string; modules: string[]; constants: number; theorems: number; passed: boolean };
}

export const LIBRARY_COUNTS = data as LibraryCounts;
