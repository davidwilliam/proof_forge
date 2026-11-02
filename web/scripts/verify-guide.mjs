// Copies what the /verify page shows from the repository's own documents, so no command on that page
// is written by hand: the command blocks of README.md (Quickstart without Docker, Reproduce the
// Passports, Running it), the check-and-verify steps of AGENTS.md, the list of what
// `bin/proofforge verify` compares (each item checked against bin/proofforge), and two committed
// verify outputs.
// Usage: node scripts/verify-guide.mjs           write generated/verify-guide.json
//        node scripts/verify-guide.mjs --check   exit 1 if generated/verify-guide.json is out of date

import fs from "node:fs";
import path from "node:path";
import { ROOT } from "./lib/results.mjs";

const dest = path.join(ROOT, "web/generated/verify-guide.json");
const read = (rel) => fs.readFileSync(path.join(ROOT, rel), "utf8");
const oneLine = (s) => s.replace(/\s+/g, " ").trim();

const README = read("README.md");

/** The body of a Markdown section, from its heading to the next heading of the same or a higher level. */
function section(md, heading) {
  const lines = md.split("\n");
  const start = lines.findIndex((l) => l.replace(/^#+ /, "") === heading && /^#+ /.test(l));
  if (start < 0) throw new Error(`README.md: no heading "${heading}"`);
  const level = /^#+/.exec(lines[start])[0].length;
  let end = lines.length;
  let fenced = false;
  for (let i = start + 1; i < lines.length; i++) {
    if (lines[i].startsWith("```")) fenced = !fenced;
    if (fenced) continue;
    const m = /^(#+) /.exec(lines[i]);
    if (m && m[1].length <= level) {
      end = i;
      break;
    }
  }
  return lines.slice(start + 1, end).join("\n");
}

/** The fenced code blocks of a section and the prose around them. */
function blocks(body) {
  const out = [];
  const re = /```[a-z]*\n([\s\S]*?)```/g;
  let m;
  let last = 0;
  while ((m = re.exec(body))) {
    out.push({ before: oneLine(body.slice(last, m.index)), code: m[1].replace(/\n$/, "") });
    last = re.lastIndex;
  }
  return { blocks: out, after: oneLine(body.slice(last)) };
}

function readmeBlock(heading, n = 0) {
  const b = blocks(section(README, heading));
  const blk = b.blocks[n];
  if (!blk) throw new Error(`README.md: no code block ${n} under "${heading}"`);
  return { source: "README.md", heading, before: blk.before, code: blk.code, after: n === b.blocks.length - 1 ? b.after : "" };
}

const quickstart = readmeBlock("Quickstart without Docker");
const reproduce = readmeBlock("Reproduce the Passports");
const running = readmeBlock("Running it");

// AGENTS.md, "Fixing a task": the check and verify steps.
const agentSteps = section(read("AGENTS.md"), "Fixing a task")
  .trim()
  .split(/\n\s*\n/)[0]
  .split(/\n(?=\d+\. )/)
  .map(oneLine)
  .filter((s) => /^[45]\. /.test(s));
if (agentSteps.length !== 2) throw new Error("AGENTS.md: steps 4 and 5 of Fixing a task not found");

// What `verify` compares, in the order bin/proofforge prints it. Each needle must occur in its source.
const CLI = read("bin/proofforge");
const COMPARED = [
  { name: "locked manifest", text: "The hash of the locked specification files.", needle: '("locked manifest"' },
  { name: "solution tree", text: "The hash of the candidate's solution tree.", needle: '("solution tree"' },
  { name: "executable", text: "The hash of the rebuilt executable, when this machine builds for the Passport's platform.", needle: '("executable", old["executable"]["sha256"]' },
  { name: "executable tests", text: "The property-test result of the rebuilt executable, on every platform.", needle: '("executable tests"' },
  { name: "component status", text: "VERIFIED, REFUTED or UNRESOLVED for the whole component.", needle: '("component status"' },
  { name: "requirement status", text: "The status of every requirement.", needle: "status\", r[\"status\"], n[\"status\"]" },
  { name: "requirement statement", text: "The hash of every requirement's locked statement.", needle: "statement\", r[\"statement_sha256\"]" },
  { name: "Lean toolchain", text: "The Lean version the judge ran.", needle: '("Lean toolchain"' },
  { name: "library", text: "Whether ProofForgeFin was vendored and, if so, its source tree hash, the modules imported and the library scan.", needle: '("library source tree"' },
  { name: "counterexamples", text: "For a REFUTED Passport, each recorded refutation re-checked in a fresh container: statement, source, challenge, kernel check, kernels and axioms.", needle: "counterexample kernel check" },
  { name: "judge image", text: "The judge image digest is reported, and counted as a difference only with --strict-image.", needle: '("judge image"' },
  { name: "exit code", text: "0 and \"reproduced\" when every comparison is the same; 1 and the number of differences otherwise.", needle: 'print(f"NOT reproduced: {bad} differences")' },
];
for (const c of COMPARED) if (!CLI.includes(c.needle)) throw new Error(`bin/proofforge: "${c.needle}" not found (${c.name})`);
const usage = /proofforge verify passport\.json --candidate PATH \[--strict-image\]/.exec(CLI)?.[0];
if (!usage) throw new Error("bin/proofforge: verify usage line not found");

// Committed verify outputs.
const SAMPLES = [
  {
    title: "The Cetus repair by Muse Spark 1.3, on the machine that issued it",
    source: "results/cetus-1/repair-A1-1/verify.txt",
    passport: "results/cetus-1/repair-A1-1/passport.json",
  },
  {
    title: "A Passport issued by the deployed judge (linux/amd64), reproduced on an Apple Silicon Mac",
    source: "reports/reproduction/fly-passport-on-arm64.txt",
    passport: null,
  },
];
const samples = SAMPLES.map((s) => {
  const text = read(s.source).replace(/\n+$/, "");
  let command = null;
  let sha256 = null;
  let status = null;
  if (s.passport) {
    const p = JSON.parse(read(s.passport));
    command = p.reproduce;
    sha256 = p.passport_sha256;
    status = p.status;
  }
  const last = text.split("\n").filter((l) => /^(reproduced|NOT reproduced)/.test(l)).pop() ?? null;
  if (!last) throw new Error(`${s.source}: no reproduced line`);
  return { ...s, command, sha256, status, text, result: last };
});

const out = {
  generator: "web/scripts/verify-guide.mjs",
  usage,
  quickstart,
  reproduce,
  running,
  agentSteps,
  compared: COMPARED.map(({ name, text }) => ({ name, text })),
  comparedSource: ["bin/proofforge", "docs/ARCHITECTURE.md"],
  samples,
};

const body = JSON.stringify(out, null, 1) + "\n";
if (process.argv.includes("--check")) {
  const now = fs.existsSync(dest) ? fs.readFileSync(dest, "utf8") : "";
  if (now !== body) {
    console.error("generated/verify-guide.json is out of date: run node web/scripts/verify-guide.mjs");
    process.exit(1);
  }
  console.log("generated/verify-guide.json is up to date");
} else {
  fs.writeFileSync(dest, body);
  console.log(`wrote ${path.relative(ROOT, dest)}`);
}
