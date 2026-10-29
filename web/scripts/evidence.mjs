// Writes public/evidence.json and public/llms.txt: a machine-readable summary of the claims on
// the home page, for people and agents evaluating ProofForge. No checks are run.
// Usage: node scripts/evidence.mjs           write both files
//        node scripts/evidence.mjs --check   exit 1 if either file is out of date
//
// Passport hashes, statuses, reproduction commands, run costs and real-code counts are read
// from the committed result files. The wording (loss figures, properties, limits) comes from
// lib/flagships.ts and the E1 and E2 figures from lib/evidence.ts, which tests check against the
// same files. Both modules have no runtime imports and are loaded here with the TypeScript
// compiler's transpiler.

import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { pathToFileURL } from "node:url";
import ts from "typescript";
import { ROOT, readExact, readPassport, readRunSummary } from "./lib/results.mjs";

const web = path.join(ROOT, "web");

async function loadTs(rel) {
  const src = fs.readFileSync(path.join(web, rel), "utf8");
  const { outputText } = ts.transpileModule(src, {
    compilerOptions: { module: ts.ModuleKind.ESNext, target: ts.ScriptTarget.ES2022 },
    fileName: rel,
  });
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "pf-evidence-"));
  const file = path.join(tmp, path.basename(rel).replace(/\.ts$/, ".mjs"));
  fs.writeFileSync(file, outputText);
  try {
    return await import(pathToFileURL(file).href);
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
}

const F = await loadTs("lib/flagships.ts");
const { E1, E2 } = await loadTs("lib/evidence.ts");

function passport(ref) {
  if (!ref) return null;
  const p = readPassport(ref.path);
  if (p.recomputedSha256 !== p.sha256) throw new Error(`${ref.path}: stored passport_sha256 does not match its content`);
  return {
    path: p.path,
    url: F.githubFile(p.path),
    sha256: p.sha256,
    status: p.status,
    requirements: p.requirements,
    kernels: p.kernels,
    property_cases: p.propertyCases,
    executable: p.executableStatus,
    reproduce: p.reproduce,
  };
}

function realCode(f) {
  const r = readExact(f.realCode.report);
  const rows = f.realCode.rows.map((row) => ({
    code: row.label,
    commit: row.commit,
    [`${f.realCode.unit}_violating_a_requirement`]: row.violating,
    [`${f.realCode.unit}_equal_to_lean_port`]: row.sameAsPort,
    [`${f.realCode.unit}_equal_to_proved_repair`]: row.sameAsProved,
    note: row.note,
  }));
  // Totals come from the report, not the data module.
  const total = f.key === "cetus" ? r.cases : f.key === "euler" ? r.versions.b1ee326.sequences : f.key === "hundred" ? r.comparison.cases : f.realCode.total;
  return { summary: f.realCode.short, result: f.realCode.result, method: f.realCode.how, unit: f.realCode.unit, total, results: rows, report: f.realCode.report, witnesses_checked_in_lean: f.realCode.confirmedInLean };
}

function flagship(f) {
  const run = readRunSummary(`${f.repair.run}/summary.json`);
  return {
    key: f.key,
    incident: f.incident,
    date: f.date,
    system: f.system,
    language: f.language,
    loss: { amount: f.loss.amount, basis: f.loss.basis, sources: f.loss.citations, quoted_from: `${f.task}/README.md` },
    bug: f.bug,
    property_proved: { text: f.property, requirement: f.propertyId },
    task: f.task,
    readme: `${f.task}/README.md`,
    vulnerable_code: {
      label: f.vulnerable.label,
      verdict: f.vulnerable.verdict,
      finding: f.vulnerable.finding,
      kernel_checked_counterexample: f.vulnerable.witness,
      passport: passport(f.vulnerable.passport),
    },
    muse_repair: {
      model: f.repair.model,
      tier: f.repair.tier,
      arm: f.repair.arm,
      attempt: f.repair.attempt,
      change: f.repair.change,
      verdict: f.repair.verdict,
      run: f.repair.run,
      seconds: Math.round(run.seconds),
      model_calls: run.calls,
      usd_list_price: run.usdList,
      usd_charged: run.usdCharged,
      passport: passport(f.repair.passport),
    },
    versions: f.timeline.length
      ? f.timeline.map((v) => ({ version: v.title, detail: v.detail, commit: v.commit, merged: v.merged ?? undefined, code: v.code, verdict: v.verdict, finding: v.finding, passport: passport(v.passport) }))
      : undefined,
    muse_repair_equivalent_to_upstream_fix: f.equivalence ?? undefined,
    attack: f.attack.length ? f.attack.map((s, i) => ({ step: i + 1, ...s })) : undefined,
    kernel_checked_outcome: f.outcome || undefined,
    real_code: realCode(f),
    not_proved: f.limits,
  };
}

const flagships = F.FLAGSHIPS.map(flagship);
const notClaimed = [
  "The Solidity and Move code are not themselves proved. Each incident's Lean 4 port is a reviewed hand translation, tested against the real code on the stated inputs; the translation is not machine-checked.",
  "A requirement covers exactly what its Lean statement says. Each port models only the logic named in its task README.",
  "Loss figures are quoted from the sources each task README cites.",
  "The JSON wrapper around each proved function is tested, not proved.",
  ...F.FLAGSHIPS.map((f) => f.reconstruction).filter(Boolean),
];

const evidence = {
  name: "ProofForge",
  repository: F.REPO_URL,
  headline: F.HEADLINE,
  summary: F.SUMMARY,
  generated_by: "web/scripts/evidence.mjs from committed result files",
  checking: {
    lean: "Lean v4.35.0",
    judge: "lake comparator --paranoid in a fresh bubblewrap sandbox with six kernels (Lean default and paranoid, lean4lean, nanoda, con-leche, con-ron), then leanchecker and an axiom audit; the executable rebuilt from the same source runs generated property cases",
    statuses: ["VERIFIED", "REFUTED", "UNRESOLVED"],
  },
  flagships,
  implements: F.IMPLEMENTS ?? undefined,
  implemented_flagships: F.IMPLEMENTED_FLAGSHIPS.map((i) => ({
    flagship: i.key,
    mode: "implement: Muse starts from the locked challenge with placeholder definitions and unproved theorems; no vulnerable code, issue report or reference",
    status: i.passport.status,
    passport: { sha256: i.passport.sha256, path: i.passport.path, requirements: i.passport.requirements, reproduce: i.passport.reproduce },
  })),
  benchmark: {
    tasks: F.BENCHMARK.tasks,
    splits: F.BENCHMARK.splits,
    families: F.BENCHMARK.families.map((x) => ({ family: x.label, tasks: x.tasks })),
    e1: {
      source: E1.source,
      test_tasks: E1.tasks,
      property_cases_per_repair: E1.propertyCases,
      completed: Object.fromEntries(E1.arms.map((a) => [`${a.key} ${a.label}`, a.completed])),
      mcnemar_p_vs_A0: E1.mcnemarP,
      batch_usd_list_price: E1.batchUsdList,
    },
    e2: {
      source: E2.source,
      seeded_bad_cases: E2.bad,
      good_cases: E2.good,
      accepted_bad: Object.fromEntries(E2.arms.map((a) => [a.label, a.badAccepted])),
      rejected_good: Object.fromEntries(E2.arms.map((a) => [a.label, a.goodRejected])),
    },
  },
  not_claimed: notClaimed,
  reproduce: {
    setup: [
      `git clone ${F.REPO_URL} && cd proof_forge`,
      "docker build -t proofforge-lean:4.35.0 -f infra/docker/Dockerfile.lean infra/docker",
    ],
    passports: flagships.flatMap((f) => [f.vulnerable_code.passport, f.muse_repair.passport, ...(f.versions ?? []).map((v) => v.passport)])
      .filter(Boolean)
      .filter((p, i, all) => all.findIndex((q) => q.sha256 === p.sha256) === i)
      .map((p) => ({ passport: p.path, sha256: p.sha256, status: p.status, command: p.reproduce })),
  },
};

const count = (n) => ["No", "One", "Two", "Three", "Four", "Five", "Six"][n] ?? String(n);

function llms() {
  const L = [];
  L.push("# ProofForge", "", `> ${F.HEADLINE} ${F.SUMMARY}`, "");
  L.push(
    `${count(flagships.length)} real exploits, each repaired by Muse Spark 1.3 (Meta) and checked by ProofForge. Machine-readable version: /evidence.json. Source: ${F.REPO_URL}`,
    "",
  );
  for (const f of flagships) {
    L.push(`## ${f.incident}, ${f.date}`, "");
    L.push(`- Loss: ${f.loss.amount} ${f.loss.basis}. Sources: ${f.loss.sources.map((s) => s.url).join(", ")}`);
    L.push(`- Bug: ${f.bug}`);
    L.push(`- Property proved in Lean 4 (${f.property_proved.requirement}): ${f.property_proved.text}`);
    const vp = f.vulnerable_code.passport;
    L.push(`- Vulnerable code (${f.vulnerable_code.label}): ${f.vulnerable_code.verdict}. ${f.vulnerable_code.finding} Kernel-checked counterexample: ${f.vulnerable_code.kernel_checked_counterexample}${vp ? `. Passport ${vp.sha256} (${vp.path})` : ""}`);
    for (const v of f.versions ?? []) if (v.passport.sha256 !== vp?.sha256 && v.passport.sha256 !== f.muse_repair.passport.sha256) L.push(`- ${v.version} (${v.detail}): ${v.verdict}. ${v.finding} Passport ${v.passport.sha256} (${v.passport.path})`);
    const m = f.muse_repair;
    const reqs = Object.keys(m.passport.requirements).length;
    L.push(`- Muse repair: ${m.verdict}, ${reqs} of ${reqs} requirements, ${m.passport.kernels} kernels, ${m.passport.property_cases} property cases; attempt ${m.attempt}, ${m.seconds} s, ${m.model_calls} model calls, $${m.usd_list_price} at list prices, $${m.usd_charged} charged. Passport ${m.passport.sha256} (${m.passport.path})`);
    const eq = f.muse_repair_equivalent_to_upstream_fix;
    if (eq) L.push(`- Proved separately (${eq.file}, axioms ${eq.axioms}): ${eq.theorem}`);
    L.push(`- Reproduce: ${m.passport.reproduce}`);
    L.push(`- Real code: ${f.real_code.method}`);
    for (const r of f.real_code.results) {
      const u = f.real_code.unit;
      const parts = [`${r[`${u}_violating_a_requirement`]} of ${f.real_code.total} ${u} break a requirement`];
      if (r[`${u}_equal_to_lean_port`] != null) parts.push(`${r[`${u}_equal_to_lean_port`]} equal the Lean port`);
      if (r[`${u}_equal_to_proved_repair`] != null) parts.push(`${r[`${u}_equal_to_proved_repair`]} equal the proved repair`);
      L.push(`  - ${r.code}: ${parts.join("; ")} (${r.note})`);
    }
    L.push(`- Not proved: ${f.not_proved.join(" ")}`);
    L.push(`- Task: ${f.readme}`, "");
  }
  L.push("## Implemented from the specification alone", "");
  for (const i of evidence.implemented_flagships) {
    const n = Object.keys(i.passport.requirements).length;
    L.push(`- ${i.flagship}: ${i.status}, ${n} of ${n} requirements. Passport ${i.passport.sha256} (${i.passport.path}). Reproduce: ${i.passport.reproduce}`);
  }
  if (F.IMPLEMENTS) L.push(`- Benchmark: ${F.IMPLEMENTS.value} of ${F.IMPLEMENTS.of} ${F.IMPLEMENTS.label} (${F.IMPLEMENTS.detail}; ${F.IMPLEMENTS.source}).`);
  L.push("");
  L.push("## Benchmark", "");
  L.push(`- ${evidence.benchmark.tasks} repair tasks in six families: ${evidence.benchmark.families.map((x) => `${x.family.toLowerCase()} (${x.tasks})`).join(", ")}; ${F.BENCHMARK.splits.dev} development, ${F.BENCHMARK.splits.val} validation, ${F.BENCHMARK.splits.test} test.`);
  L.push(`- E1 (${E1.source}): on the ${E1.tasks} frozen test tasks, ${E1.arms.map((a) => `${a.key} ${a.label} completed ${a.completed}`).join(", ")}; McNemar exact p = ${E1.mcnemarP} against A0, so the arms are not shown to differ. ${E1.tasks * E1.arms.length} runs cost $${E1.batchUsdList} at list prices.`);
  L.push(`- E2 (${E2.source}): seeded bad repairs accepted, out of ${E2.bad}: ${E2.arms.map((a) => `${a.label} ${a.badAccepted}`).join(", ")}. Correct repairs rejected, out of ${E2.good}: ${E2.arms.map((a) => `${a.label} ${a.goodRejected}`).join(", ")}. Every bad case is a seeded attack written by the build team.`);
  L.push("");
  L.push("## Not claimed", "");
  for (const c of notClaimed) L.push(`- ${c}`);
  L.push("");
  L.push("## Reproduce", "");
  for (const c of evidence.reproduce.setup) L.push(`    ${c}`);
  for (const p of evidence.reproduce.passports) L.push(`    ${p.command}`);
  L.push("");
  L.push("## Pages", "");
  L.push(`- /: overview with the ${count(flagships.length).toLowerCase()} incidents`, "- /forge: live forge session (replay of a recorded Muse repair, then a fresh check)", "- /results: E1 and E2 per arm, family and case", "");
  return L.join("\n");
}

const outputs = {
  "public/evidence.json": JSON.stringify(evidence, null, 2) + "\n",
  "public/llms.txt": llms(),
};

const banned = /[\u2014\u2013]/;
for (const [rel, body] of Object.entries(outputs)) if (banned.test(body)) throw new Error(`${rel} would contain an em or en dash`);

if (process.argv.includes("--check")) {
  const stale = Object.entries(outputs).filter(([rel, body]) => {
    const f = path.join(web, rel);
    return !fs.existsSync(f) || fs.readFileSync(f, "utf8") !== body;
  });
  if (stale.length) {
    console.error(`out of date: ${stale.map(([rel]) => rel).join(", ")}; run node scripts/evidence.mjs`);
    process.exit(1);
  }
  console.log("public/evidence.json and public/llms.txt are up to date");
} else {
  for (const [rel, body] of Object.entries(outputs)) {
    fs.mkdirSync(path.dirname(path.join(web, rel)), { recursive: true });
    fs.writeFileSync(path.join(web, rel), body);
  }
  console.log(`${flagships.length} flagships, ${evidence.reproduce.passports.length} Passports; wrote ${Object.keys(outputs).join(" and ")}`);
}
