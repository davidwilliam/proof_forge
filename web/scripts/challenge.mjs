// Collects the committed facts about the hidden challenge into generated/challenge.json for the
// /challenge page: the hidden variants (hidden/<id>/task.json, with the issue report, which the page
// opens only on request after a check of that variant), how each was validated (hidden/<id>/validation.json), what the endpoint runs
// (server/app.py) and every recorded call of the deployed endpoint (reports/reliability/*.json,
// made by infra/reliability.py). Nothing is recomputed or run.
// Usage: node scripts/challenge.mjs           write generated/challenge.json
//        node scripts/challenge.mjs --check   exit 1 if generated/challenge.json is out of date

import fs from "node:fs";
import path from "node:path";
import { ROOT } from "./lib/results.mjs";

const dest = path.join(ROOT, "web/generated/challenge.json");
const read = (rel) => fs.readFileSync(path.join(ROOT, rel), "utf8");
const json = (rel) => JSON.parse(read(rel));

function must(m, what) {
  if (!m) throw new Error(`challenge.mjs: could not find ${what}`);
  return m[1];
}

// What POST /api/challenge runs: the property cases and the deadline, from the endpoint itself.
const SERVER = "server/app.py";
const app = read(SERVER);
const endpoint = app.slice(app.indexOf('@app.post("/api/challenge")'), app.indexOf("def prewarm("));
const server = {
  source: SERVER,
  propertyCases: Number(must(endpoint.match(/property_tests\(project, t, (\d+),/), "the property case count in server/app.py")),
  deadlineS: Number(must(endpoint.match(/seconds\("PF_CHALLENGE_DEADLINE_S", (\d+)\)/), "the challenge deadline in server/app.py")),
};

const variants = fs
  .readdirSync(path.join(ROOT, "hidden"))
  .filter((d) => fs.existsSync(path.join(ROOT, "hidden", d, "task.json")))
  .sort()
  .map((id) => {
    const t = json(`hidden/${id}/task.json`);
    const vRel = `hidden/${id}/validation.json`;
    const v = json(vRel).checks;
    return {
      id: t.id,
      family: t.family,
      lib: t.lib,
      definitions: t.definitions,
      requirements: t.requirements.map(([rid]) => rid),
      exe: t.exe,
      issue: t.issue,
      source: `hidden/${id}/task.json`,
      validation: {
        source: vRel,
        checks: ["metadata", "lock", "hygiene"].map((k) => ({ check: k, passed: v[k].passed })),
        references: Object.entries(v.references).map(([file, r]) => ({ file, judge: r.judge, judgeMs: r.judge_ms, binary: r.binary })),
        start: { judge: v.start.judge, binary: v.start.binary },
      },
    };
  });

// The deployed endpoint as infra/reliability.py called it, once per session.
const RUNNER = "infra/reliability.py";
const runnerVariant = must(read(RUNNER).match(/"\/api\/challenge", \{"variant": "([^"]+)"\}/), "the variant infra/reliability.py calls");
const reliability = fs
  .readdirSync(path.join(ROOT, "reports/reliability"))
  .filter((f) => f.endsWith(".json"))
  .sort()
  .map((f) => {
    const rel = `reports/reliability/${f}`;
    const r = json(rel);
    return {
      source: rel,
      recordedAt: r.recorded_at,
      api: r.api,
      calls: r.session_records
        .filter((s) => s.steps["hidden challenge"])
        .map((s) => ({ session: s.session, refuted: s.steps["hidden challenge"].ok, seconds: s.steps["hidden challenge"].seconds })),
    };
  });

const out = {
  generator: "web/scripts/challenge.mjs",
  server,
  variants,
  reliability: { runner: RUNNER, variant: runnerVariant, refutedMeans: "HTTP 200 with status REFUTED", runs: reliability },
};
const text = JSON.stringify(out, null, 2) + "\n";

if (process.argv.includes("--check")) {
  const cur = fs.existsSync(dest) ? fs.readFileSync(dest, "utf8") : "";
  if (cur !== text) {
    console.error("generated/challenge.json is out of date: run node scripts/challenge.mjs");
    process.exit(1);
  }
} else {
  fs.writeFileSync(dest, text);
  console.log(`wrote ${path.relative(ROOT, dest)}: ${variants.length} variants, ${reliability.reduce((n, r) => n + r.calls.length, 0)} recorded calls`);
}
