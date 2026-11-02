// Copies the per-task E1 outcomes (results/e1-*/e1.json, field "results", written by eval/e1.py)
// into generated/e1-tasks.json for the task-by-arm grids of the /results page. GET /api/results
// serves only each set's summary; this file adds one record per run. Nothing is recomputed.
// Usage: node scripts/e1-tasks.mjs           write generated/e1-tasks.json
//        node scripts/e1-tasks.mjs --check   exit 1 if generated/e1-tasks.json is out of date
//
// Per run it keeps the arm, whether the repair completed (judge ACCEPT and binary PASS), the
// judge and binary verdicts, the budget stop, the list dollars and the wall time. testTasks is the
// frozen test split (tasks/*/task.json with split "test"), so an incomplete test set shows the
// tasks it never reached.

import fs from "node:fs";
import path from "node:path";
import { ROOT } from "./lib/results.mjs";

const dest = path.join(ROOT, "web/generated/e1-tasks.json");
const resultsDir = path.join(ROOT, "results");

const sets = {};
for (const dir of fs.readdirSync(resultsDir).sort()) {
  const file = path.join(resultsDir, dir, "e1.json");
  if (!dir.startsWith("e1-") || !fs.existsSync(file)) continue;
  const d = JSON.parse(fs.readFileSync(file, "utf8"));
  const runs = {};
  for (const r of d.results ?? []) {
    runs[r.task] ??= {};
    runs[r.task][r.arm] = {
      completed: r.completed === true,
      judge: r.judge ?? null,
      binary: r.binary ?? null,
      stop: r.stop ?? null,
      usdList: r.usd_list ?? null,
      elapsedS: r.elapsed_s ?? null,
    };
  }
  const family = Object.fromEntries((d.results ?? []).map((r) => [r.task, r.family]));
  sets[dir] = { source: `results/${dir}/e1.json`, tasks: d.summary?.tasks ?? Object.keys(runs), family, runs };
}

const testTasks = fs
  .readdirSync(path.join(ROOT, "tasks"))
  .filter((id) => {
    const f = path.join(ROOT, "tasks", id, "task.json");
    return fs.existsSync(f) && JSON.parse(fs.readFileSync(f, "utf8")).split === "test";
  })
  .sort()
  .map((id) => ({ id, family: JSON.parse(fs.readFileSync(path.join(ROOT, "tasks", id, "task.json"), "utf8")).family }));

const body = JSON.stringify({ sets, testTasks }) + "\n";

if (process.argv.includes("--check")) {
  if (!fs.existsSync(dest) || fs.readFileSync(dest, "utf8") !== body) {
    console.error("out of date: generated/e1-tasks.json; run node scripts/e1-tasks.mjs");
    process.exit(1);
  }
  console.log("generated/e1-tasks.json is up to date");
} else {
  fs.mkdirSync(path.dirname(dest), { recursive: true });
  fs.writeFileSync(dest, body);
  console.log(`${Object.keys(sets).length} E1 sets, ${testTasks.length} frozen test tasks; wrote ${path.relative(process.cwd(), dest)}`);
}
