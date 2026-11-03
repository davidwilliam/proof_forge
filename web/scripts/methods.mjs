// Lists every preregistered experiment (results/*/PREREGISTRATION.md) for the /methods page:
// its question, the commit that added the plan, the number of runs it fixes, its primary test,
// its addenda and its status. An experiment is finished when its README says "Status: measured";
// its figures are then copied from the wins ledger (results/wins/ledger.json, written by
// eval/wins.py) and nothing is recomputed. An experiment without that README takes its status
// from STATUS below, which states what was known on AS_OF.
// Usage: node scripts/methods.mjs           write generated/methods.json
//        node scripts/methods.mjs --check   exit 1 if generated/methods.json is out of date

import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { ROOT } from "./lib/results.mjs";

const dest = path.join(ROOT, "web/generated/methods.json");
const LEDGER = "results/wins/ledger.json";

const AS_OF = "2026-11-03";
/** Experiments without a README result yet, as of AS_OF. */
const STATUS = {
  "frontier-4": {
    status: "running",
    label: "Running",
    note: "The 20 preregistered runs started on 2026-11-02 at 22:36, after results/hard-task-2 ended, as the preregistration states. Every run is reported in results/frontier-4/README.md when they end.",
  },
};

const read = (rel) => fs.readFileSync(path.join(ROOT, rel), "utf8");
const exists = (rel) => fs.existsSync(path.join(ROOT, rel));
const oneLine = (s) => s.replace(/\s+/g, " ").trim();

/** The sections of a Markdown file by "## " heading, in order. */
function sections(md) {
  const out = [];
  let cur = null;
  for (const line of md.split("\n")) {
    const h = /^## (.+)$/.exec(line);
    if (h) {
      cur = { heading: h[1].trim(), lines: [] };
      out.push(cur);
    } else if (cur) cur.lines.push(line);
  }
  return out.map((s) => ({ heading: s.heading, body: s.lines.join("\n").trim() }));
}

const paragraphs = (body) =>
  body
    .split(/\n\s*\n/)
    .map(oneLine)
    .filter(Boolean);

/** Top-level bullets of a section, each joined to one line. */
function bullets(body) {
  const out = [];
  for (const line of body.split("\n")) {
    if (/^- /.test(line)) out.push(line.slice(2));
    else if (/^\s+\S/.test(line) && out.length) out[out.length - 1] += " " + line.trim();
    else if (line.trim() === "" || /^\S/.test(line)) out.push(null);
  }
  return out.filter((b) => b !== null).map(oneLine);
}

const RUN_COUNT = [/(\d+) in total/, /so (\d+) runs/, /(\d+) runs\./];

function runsOf(id, body) {
  const bs = bullets(body);
  for (const re of RUN_COUNT) {
    for (const b of bs) {
      const m = re.exec(b);
      if (m) return { runs: Number(m[1]), runsText: b };
    }
  }
  throw new Error(`${id}: no run count in the Runs section`);
}

function git(...args) {
  return execFileSync("git", ["-C", ROOT, ...args], { encoding: "utf8" }).trim();
}

/** The commit that added a file, from git history. */
function addedBy(rel) {
  const line = git("log", "--diff-filter=A", "--format=%H %h %cI", "--", rel).split("\n").filter(Boolean).pop();
  if (!line) throw new Error(`${rel}: no commit adds it`);
  const [full, short, date] = line.split(" ");
  return { commit: short, commitFull: full, commitDate: date };
}

const L = JSON.parse(read(LEDGER));

function arm(a) {
  return {
    verified: a.verified,
    runs: a.runs,
    usdPerVerified: a.list_usd_per_verified,
    usdTotal: a.list_usd_total,
    capStops: a.cap_stops.usd + a.cap_stops.wall,
    reqMean: a.req_proved_mean,
    reqTotal: a.req_total,
  };
}

function comparison(c) {
  return {
    id: c.id,
    task: c.task,
    model: c.model,
    alone: arm(c.alone),
    proofforge: arm(c.proofforge),
    test: c.test
      ? { name: c.test.name, p: c.test.p, ...(c.test.secondary ? { secondary: { name: c.test.secondary.name, p: c.test.secondary.p } } : {}) }
      : null,
    factors: { cost: c.factors.cost ?? null, time: c.factors.time ?? null },
  };
}

function entry(dir) {
  const rel = `results/${dir}/PREREGISTRATION.md`;
  const md = read(rel);
  const title = /^# (.+)$/m.exec(md)?.[1] ?? "";
  if (!title.startsWith(`${dir}: preregistration`)) throw new Error(`${rel}: unexpected title "${title}"`);
  const written = /Written on (\d{4}-\d{2}-\d{2})/.exec(md)?.[1];
  if (!written) throw new Error(`${rel}: no "Written on" date`);
  const secs = sections(md);
  const first = secs[0];
  if (!first || first.heading !== "Question") throw new Error(`${rel}: the first section is not "Question"`);
  const [question, ...questionMore] = paragraphs(first.body);
  const runsSec = secs.find((s) => s.heading === "Runs");
  if (!runsSec) throw new Error(`${rel}: no Runs section`);
  const outcomes = secs.find((s) => s.heading.startsWith("Outcomes"));
  const primaryTest = outcomes && bullets(outcomes.body).find((b) => b.startsWith("Primary analysis"));
  if (!primaryTest) throw new Error(`${rel}: no "Primary analysis" bullet`);
  const testName = /(one-sided Fisher exact test|exact McNemar test)/.exec(primaryTest)?.[1];
  if (!testName) throw new Error(`${rel}: unknown primary test`);
  const addenda = secs.filter((s) => s.heading.startsWith("Addendum")).map((s) => s.heading);

  const readmeRel = `results/${dir}/README.md`;
  const readme = exists(readmeRel) ? read(readmeRel) : null;
  const measured = readme ? /^Status: measured\.[\s\S]*?(?=\n\s*\n)/m.exec(readme)?.[0] : null;
  let status;
  if (readme) {
    if (!measured) throw new Error(`${readmeRel}: no "Status: measured" paragraph`);
    if (STATUS[dir]) throw new Error(`${dir}: has a README result; remove it from STATUS`);
    status = { status: "finished", label: "Finished", note: oneLine(measured) };
  } else {
    if (!STATUS[dir]) throw new Error(`${dir}: no README result and no entry in STATUS`);
    status = STATUS[dir];
  }

  const ofExperiment = L.comparisons.filter((c) => c.experiment === dir);
  const tasks = status.status === "finished" ? ofExperiment.filter((c) => c.scope === "task").map(comparison) : [];
  const pooled = status.status === "finished" ? L.comparisons.filter((c) => c.scope === "aggregate" && c.experiment.split("+")[0] === dir).map(comparison) : [];
  if (status.status === "finished" && !tasks.length) throw new Error(`${dir}: finished but no task comparison in ${LEDGER}`);

  return {
    id: dir,
    prereg: rel,
    readme: readme ? readmeRel : null,
    written,
    ...addedBy(rel),
    question,
    questionMore,
    ...runsOf(dir, runsSec.body),
    testName,
    primaryTest,
    addenda,
    ...status,
    tasks,
    pooled,
  };
}

const dirs = fs
  .readdirSync(path.join(ROOT, "results"), { withFileTypes: true })
  .filter((d) => d.isDirectory() && exists(`results/${d.name}/PREREGISTRATION.md`))
  .map((d) => d.name);
for (const k of Object.keys(STATUS)) if (!dirs.includes(k)) throw new Error(`STATUS names ${k}, which has no PREREGISTRATION.md`);

const entries = dirs.map(entry).sort((a, b) => a.commitDate.localeCompare(b.commitDate));
const out = {
  source: "results/*/PREREGISTRATION.md",
  ledger: LEDGER,
  generator: "web/scripts/methods.mjs",
  asOf: AS_OF,
  entries,
};

const body = JSON.stringify(out, null, 1) + "\n";
if (process.argv.includes("--check")) {
  const now = fs.existsSync(dest) ? fs.readFileSync(dest, "utf8") : "";
  if (now !== body) {
    console.error("generated/methods.json is out of date: run node web/scripts/methods.mjs");
    process.exit(1);
  }
  console.log("generated/methods.json is up to date");
} else {
  fs.writeFileSync(dest, body);
  console.log(`wrote ${path.relative(ROOT, dest)}: ${entries.length} preregistrations`);
}
