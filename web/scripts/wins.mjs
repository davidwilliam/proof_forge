// Copies the wins ledger (results/wins/ledger.json, written by eval/wins.py) into
// generated/wins.json for the /wins page, the home page wins section, public/evidence.json and
// public/llms.txt. No checks are run and nothing is recomputed: every figure is the ledger's.
// Usage: node scripts/wins.mjs           write generated/wins.json
//        node scripts/wins.mjs --check   exit 1 if generated/wins.json is out of date
//
// Per comparison it keeps both arms' runs, verified runs, list dollars per verified run, wall
// times, requirements proved and cap stops, the classification of each dimension, the factors,
// the test where one was stated, the flags and the links to its reports in the repository. Per
// win it keeps the ledger's own sentence.

import fs from "node:fs";
import path from "node:path";
import { ROOT } from "./lib/results.mjs";

const src = path.join(ROOT, "results/wins/ledger.json");
const dest = path.join(ROOT, "web/generated/wins.json");
const L = JSON.parse(fs.readFileSync(src, "utf8"));

const README = "results/wins/README.md";
// GitHub's anchors for the headings of results/wins/README.md under "Every comparison".
const slug = (heading) => heading.toLowerCase().replace(/[^a-z0-9 -]/g, "").replace(/ /g, "-");
const tableAnchor = (c) => (c.experiment.startsWith("e1-") && c.scope === "task" ? slug(`${c.experiment}, per task`) : slug("Aggregates and real-world tasks"));

/** Reports of a comparison: the committed READMEs and E1 reports among its sources, else its experiment's E1 report. */
function reports(c) {
  const committed = (p) => !p.startsWith(".claude/") && fs.existsSync(path.join(ROOT, p));
  const md = c.sources.filter((p) => /\/(README|e1)\.md$/.test(p) && committed(p));
  if (md.length) return [...new Set(md)];
  const e1 = `results/${c.experiment}/e1.md`;
  return c.experiment.startsWith("e1-") && committed(e1) ? [e1] : [];
}

const kindOf = (exp) => (exp.startsWith("e1-") ? "benchmark" : exp.startsWith("e2-") ? "catches" : "real-world");

function arm(a) {
  return {
    arm: a.arm,
    label: a.label,
    runs: a.runs,
    verified: a.verified,
    usdPerVerified: a.list_usd_per_verified,
    usdTotal: a.list_usd_total,
    priceBasis: a.price_basis,
    caps: a.caps.map((x) => ({ usd: x.usd, seconds: x.wall_s })),
    capStops: a.cap_stops.usd + a.cap_stops.wall,
    reqMean: a.req_proved_mean,
    reqTotal: a.req_total,
    passports: a.passports,
    judgeRecords: a.judge_records.length,
  };
}

// The wall times the ledger's time classification compared (eval/wins.py time_vals).
function time(c) {
  const pb = c.paired_both_verified;
  if (pb) return { alone: pb.alone_wall_s_mean, proofforge: pb.proofforge_wall_s_mean, basis: `mean wall time on the ${pb.tasks_both_verified} tasks both arms verified` };
  if (c.time_basis.startsWith("not compared")) return { alone: null, proofforge: null, basis: c.time_basis };
  return { alone: c.alone.wall_s_mean_verified, proofforge: c.proofforge.wall_s_mean_verified, basis: "mean wall time of the verified runs" };
}

// Caveats repeat across the comparisons of an experiment; each is stored once and referenced by index.
const caveats = [...new Set(L.comparisons.flatMap((c) => c.caveats))];

const comparisons = L.comparisons.map((c) => ({
  id: c.id,
  experiment: c.experiment,
  task: c.task,
  model: c.model,
  scope: c.scope,
  kind: kindOf(c.experiment),
  alone: arm(c.alone),
  proofforge: arm(c.proofforge),
  equalCaps: c.equal_caps,
  time: time(c),
  classification: c.classification,
  factors: { cost: c.factors.cost ?? null, time: c.factors.time ?? null },
  test: c.test
    ? { name: c.test.name, p: c.test.p, preregistered: c.test.preregistered === true, significant: c.test.significant_at_0_05 === true, statedIn: c.test.stated_in, ...(c.test.secondary ? { secondary: { name: c.test.secondary.name, p: c.test.secondary.p } } : {}) }
    : null,
  flags: c.flags,
  caveats: c.caveats.map((x) => caveats.indexOf(x)),
  links: { comparison: `${README}#${tableAnchor(c)}`, reports: reports(c) },
}));

const e = L.catches[0];
const catches = {
  id: e.id,
  experiment: e.experiment,
  task: e.task,
  kind: "catches",
  badCases: e.bad_cases,
  badCasesWithCompleteProofs: e.bad_cases_with_complete_proofs,
  goodCases: e.good_cases,
  badAccepted: { ordinary: e.bad_accepted.ordinary, rebuildAndTests: e.bad_accepted.rebuild_and_tests, proofforge: e.bad_accepted.proofforge },
  goodRejected: { ordinary: e.good_rejected.ordinary, rebuildAndTests: e.good_rejected.rebuild_and_tests, proofforge: e.good_rejected.proofforge },
  passedRebuildAndTests: e.passed_rebuild_and_tests,
  caveats: e.caveats,
  links: { comparison: `${README}#${slug("Catches (e2-all-1)")}`, reports: e.sources.filter((p) => p.endsWith(".md")) },
};

const ids = new Set([...comparisons.map((c) => c.id), catches.id]);
const win = (w, group) => {
  if (!ids.has(w.id)) throw new Error(`${w.id}: a win without a comparison`);
  return { group, id: w.id, kind: w.kind ?? null, costFactor: w.cost_factor ?? null, timeFactor: w.time_factor ?? null, sentence: w.sentence };
};
const W = L.wins;
const wins = [
  ...W["1_alone_did_not_verify_proofforge_did"].map((w) => win(w, 1)),
  ...W["2_both_verified_proofforge_faster_or_cheaper"].map((w) => win(w, 2)),
  ...W["3_other"].map((w) => win(w, 3)),
];

const out = {
  source: "results/wins/ledger.json",
  readme: README,
  generator: L.generator,
  rules: L.rules,
  counts: L.counts,
  optionalSources: L.optional_sources,
  notComparisons: L.not_comparisons,
  caveats,
  comparisons,
  catches,
  wins,
};

const body = JSON.stringify(out) + "\n";
if (/[—–]/.test(body)) throw new Error("generated/wins.json would contain an em or en dash");

if (process.argv.includes("--check")) {
  if (!fs.existsSync(dest) || fs.readFileSync(dest, "utf8") !== body) {
    console.error("out of date: generated/wins.json; run node scripts/wins.mjs");
    process.exit(1);
  }
  console.log("generated/wins.json is up to date");
} else {
  fs.mkdirSync(path.dirname(dest), { recursive: true });
  fs.writeFileSync(dest, body);
  console.log(`${comparisons.length} comparisons, ${wins.length} wins; wrote ${path.relative(process.cwd(), dest)}`);
}
