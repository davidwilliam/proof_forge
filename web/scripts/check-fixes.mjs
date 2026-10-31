// Writes the files behind the home page's "Check a fix" panel (lib/checkfix.ts): each candidate's
// Lean source as public/check/<task>/<key>.lean, and the committed Passport of that exact file,
// summarized, as public/check/<task>/<key>.json. The panel submits the source to POST /api/verify
// and shows the recorded summary when the API is slow or down. No checks are run.
// Usage: node scripts/check-fixes.mjs           write the files (and remove stale ones)
//        node scripts/check-fixes.mjs --check   exit 1 if any file is missing, stale or extra

import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { loadTs } from "./lib/load-ts.mjs";
import { ROOT, readExact, readPassport } from "./lib/results.mjs";

const OUT = path.join(ROOT, "web/public/check");
const C = await loadTs("lib/checkfix.ts");

const outputs = new Map();
for (const target of C.FIX_TARGETS) {
  const keys = new Set();
  for (const c of target.candidates) {
    if (keys.has(c.key)) throw new Error(`${target.task}: duplicate candidate ${c.key}`);
    keys.add(c.key);
    const bytes = fs.readFileSync(path.join(ROOT, c.source));
    const sha = createHash("sha256").update(bytes).digest("hex");
    const facts = readPassport(c.recorded);
    if (facts.recomputedSha256 !== facts.sha256) throw new Error(`${c.recorded}: stored passport_sha256 does not match its content`);
    if (facts.task !== target.task) throw new Error(`${c.recorded}: task ${facts.task}, expected ${target.task}`);
    const p = readExact(c.recorded);
    if (!Object.values(p.solution.files).includes(sha)) throw new Error(`${c.recorded} did not check ${c.source} (sha256 ${sha})`);
    const recorded = { task: target.task, candidate: c.key, source: c.source, sourceSha256: sha, passportPath: c.recorded, ...C.summarizePassport(p) };
    outputs.set(path.join(OUT, target.task, `${c.key}.lean`), bytes);
    outputs.set(path.join(OUT, target.task, `${c.key}.json`), Buffer.from(JSON.stringify(recorded, null, 2) + "\n"));
  }
}

const existing = fs.existsSync(OUT) ? fs.readdirSync(OUT, { recursive: true }).map((f) => path.join(OUT, f)).filter((f) => fs.statSync(f).isFile()) : [];
const extra = existing.filter((f) => !outputs.has(f));
const rel = (f) => path.relative(path.join(ROOT, "web"), f);

if (process.argv.includes("--check")) {
  const stale = [...outputs].filter(([f, body]) => !fs.existsSync(f) || !fs.readFileSync(f).equals(body)).map(([f]) => f);
  if (stale.length || extra.length) {
    if (stale.length) console.error(`out of date: ${stale.map(rel).join(", ")}`);
    if (extra.length) console.error(`not in lib/checkfix.ts: ${extra.map(rel).join(", ")}`);
    console.error("run node scripts/check-fixes.mjs");
    process.exit(1);
  }
  console.log(`public/check is up to date (${outputs.size / 2} candidates)`);
} else {
  for (const f of extra) fs.rmSync(f);
  for (const [f, body] of outputs) {
    fs.mkdirSync(path.dirname(f), { recursive: true });
    fs.writeFileSync(f, body);
  }
  console.log(`${outputs.size / 2} candidates in ${C.FIX_TARGETS.length} tasks; wrote public/check`);
}
