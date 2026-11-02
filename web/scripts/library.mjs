// Counts ProofForgeFin from its sources and reads its kernel checks from the committed files, into
// generated/library.json for the home page, public/evidence.json and public/llms.txt. Nothing is
// typed in by hand: declarations are counted in lib/ (comments excluded), the latest full kernel
// run is the last one lib/README.md reports, and the committed runs are read from their JSON.
// Usage: node scripts/library.mjs           write generated/library.json
//        node scripts/library.mjs --check   exit 1 if generated/library.json is out of date

import fs from "node:fs";
import path from "node:path";
import { ROOT } from "./lib/results.mjs";

const dest = path.join(ROOT, "web/generated/library.json");
const README = "lib/README.md";
/** The last full kernel run committed with its JSON, and the latest per-module run (after the compound-gaps-1 additions). */
const FULL_RUN = "results/feedback-library-1/kernels-full.json";
const MODULE_RUN = "results/library-compound-gaps-1/kernels.json";

/** Lean files under lib/<dir>, with their theorem and definition declarations counted as tests/library.test.ts recounts them. */
export function countDeclarations(dir) {
  const files = [];
  const walk = (d) => {
    for (const n of fs.readdirSync(d).sort()) {
      const f = path.join(d, n);
      if (fs.statSync(f).isDirectory()) walk(f);
      else if (n.endsWith(".lean")) files.push(f);
    }
  };
  walk(path.join(ROOT, "lib", dir));
  let theorems = 0;
  let definitions = 0;
  for (const f of files) {
    const src = fs.readFileSync(f, "utf8").replace(/\/-[\s\S]*?-\//g, "").replace(/--[^\n]*/g, "");
    theorems += (src.match(/^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)*(?:theorem|lemma)\s/gm) ?? []).length;
    definitions += (src.match(/^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*(?:def|abbrev)\s/gm) ?? []).length;
  }
  return { files: files.length, theorems, definitions };
}

const num = (s) => Number(s.replace(/,/g, ""));

function build() {
  const lib = countDeclarations("ProofForgeFin");
  const demo = countDeclarations("ProofForgeFinDemo");
  const readme = fs.readFileSync(path.join(ROOT, README), "utf8").replace(/\s+/g, " ");
  // "A full run of `tests/test_fin_kernels.py` with ... exports 10,909 safe constants of the library and its demonstrations, which all six kernels accept, with `leanchecker` exiting 0."
  const runs = [...readme.matchAll(/A full run of `tests\/test_fin_kernels\.py` ([^.]*?) exports ([\d,]+) safe constants of the library and its demonstrations, which all six kernels accept, with `leanchecker` exiting 0/g)];
  if (!runs.length) throw new Error(`${README}: no full kernel run found`);
  const last = runs[runs.length - 1];
  const full = JSON.parse(fs.readFileSync(path.join(ROOT, FULL_RUN), "utf8"));
  const mod = JSON.parse(fs.readFileSync(path.join(ROOT, MODULE_RUN), "utf8"));
  return {
    generator: "web/scripts/library.mjs",
    source: { declarations: "lib/ProofForgeFin/**/*.lean, lib/ProofForgeFinDemo/**/*.lean (comments excluded)", readme: README },
    files: lib.files,
    theorems: lib.theorems,
    definitions: lib.definitions,
    demoFiles: demo.files,
    demoTheorems: demo.theorems,
    /** The latest full kernel run lib/README.md reports: every safe constant of the library and its demonstrations, six kernels, leanchecker. */
    latestFullRun: { safeConstants: num(last[2]), kernels: 6, leanchecker: "exit 0", when: last[1], source: README },
    /** The last full kernel run committed with its JSON. */
    committedFullRun: {
      file: FULL_RUN,
      safeConstants: full.safe_exported,
      theorems: full.theorems,
      modulesReplayed: full.leanchecker.modules,
      passed: full.passed,
    },
    /** The latest per-module kernel run, committed with its JSON. */
    latestModuleRun: { file: MODULE_RUN, modules: mod.modules, constants: mod.safe_exported, theorems: mod.theorems, passed: mod.passed },
  };
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const out = `${JSON.stringify(build(), null, 2)}\n`;
  if (process.argv.includes("--check")) {
    const cur = fs.existsSync(dest) ? fs.readFileSync(dest, "utf8") : "";
    if (cur !== out) {
      console.error("generated/library.json is out of date; run node scripts/library.mjs");
      process.exit(1);
    }
  } else {
    fs.writeFileSync(dest, out);
    console.log(`wrote ${path.relative(ROOT, dest)}`);
  }
}
