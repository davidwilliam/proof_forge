// Writes public/evidence.json and public/llms.txt: a machine-readable summary of the claims on
// the home page, for people and agents evaluating ProofForge. No checks are run.
// Usage: node scripts/evidence.mjs           write both files
//        node scripts/evidence.mjs --check   exit 1 if either file is out of date
//
// Passport hashes, statuses, reproduction commands, run costs and real-code counts are read
// from the committed result files. The wording (loss figures, properties, limits) comes from
// lib/flagships.ts, the E1 and E2 figures from lib/evidence.ts and the comparison with Muse alone,
// the counterexample, open-weight, planner and library figures from lib/contribution.ts, which
// tests check against the same files, and the comparisons of the Meta models on their own and with ProofForge from generated/wins.json
// (scripts/wins.mjs, from results/wins/ledger.json) worded by lib/wins.ts. The modules have no runtime imports and are loaded here with
// the TypeScript compiler's transpiler.

import fs from "node:fs";
import path from "node:path";
import { loadTs } from "./lib/load-ts.mjs";
import { ROOT, readExact, readPassport, readRunSummary } from "./lib/results.mjs";

const web = path.join(ROOT, "web");

const F = await loadTs("lib/flagships.ts");
const { E1, E2 } = await loadTs("lib/evidence.ts");
const K = await loadTs("lib/contribution.ts");
const WL = await loadTs("lib/wins.ts");
const W = JSON.parse(fs.readFileSync(path.join(web, "generated/wins.json"), "utf8"));

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
  if (!f.realCode) return null;
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
  const totals = { cetus: () => r.cases, euler: () => r.versions.b1ee326.sequences, hundred: () => r.comparison.cases, balancer: () => r.comparison.batches };
  const total = totals[f.key] ? totals[f.key]() : f.realCode.total;
  return { summary: f.realCode.short, result: f.realCode.result, method: f.realCode.how, unit: f.realCode.unit, total, results: rows, report: f.realCode.report, witnesses_checked_in_lean: f.realCode.confirmedInLean };
}

function flagship(f) {
  const run = readRunSummary(`${f.repair.run}/summary.json`);
  return {
    key: f.key,
    incident: f.incident,
    date: f.date,
    system: f.system,
    domain: f.domain,
    language: f.language,
    reconstructed: f.reconstruction ?? undefined,
    loss: { amount: f.loss.amount, basis: f.loss.basis, sources: f.loss.citations, quoted_from: `${f.task}/README.md` },
    bug: f.bug,
    context: f.context ?? undefined,
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
      planner: f.repair.planner,
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
      reproduced_by: f.repair.verifyLog,
    },
    unresolved_attempts: f.unresolved.length
      ? f.unresolved.map((u) => ({ attempt: u.label, run: u.run, required_theorems_proved: u.proved, stopped_by: u.stop, passport: passport(u.passport) }))
      : undefined,
    versions: f.timeline.length
      ? f.timeline.map((v) => ({ version: v.title, detail: v.detail, commit: v.commit, merged: v.merged ?? undefined, code: v.code, verdict: v.verdict, finding: v.finding, passport: passport(v.passport) }))
      : undefined,
    muse_repair_equivalent_to_upstream_fix: f.equivalence ?? undefined,
    attack: f.attack.length ? f.attack.map((s, i) => ({ step: i + 1, ...s })) : undefined,
    kernel_checked_outcome: f.outcome || undefined,
    real_code: realCode(f) ?? "none: the code is not public",
    not_proved: f.limits,
  };
}

const flagships = F.FLAGSHIPS.map(flagship);
const notClaimed = [
  "The deployed Solidity and Move code is not itself proved. Each incident's Lean 4 port is a reviewed hand translation, tested against the real code on the stated inputs; the translation is not machine-checked.",
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
  loss_total: { phrase: F.lossTotalPhrase(), usd_millions_rounded_down: F.lossTotalMillions(), note: "the sum of the loss figures quoted for the incidents, each rounded down; the figures measure different things (taken, net profit to the attacker, realized loss), as each states" },
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
  meta_models_with_proofforge: {
    source: W.source,
    readme: W.readme,
    page: "/frontier",
    note: "What Meta's models reach with ProofForge that they do not reach on their own: every measured comparison of a Meta model on its own (A0 compile-and-retry, or Muse Code with Lean only) and the same model with ProofForge (A1 harness, A2 harness with the Muse Wonder 1.0 planner, or Muse Code with the ProofForge MCP server), judged by ProofForge against the same locked specification. Generated by eval/wins.py from the raw run files with no model calls; every comparison is kept, each test with its p value.",
    counts: {
      comparisons: W.counts.comparisons,
      runs: W.counts.runs,
      wins_model_alone_did_not_verify_proofforge_did: W.counts.wins_group_1,
      wins_both_verified_proofforge_cheaper_or_faster: W.counts.wins_group_2,
      wins_other: W.counts.wins_group_3,
      by_dimension_for_proofforge: W.counts.classification,
    },
    summary: WL.countsSentence(W),
    headline: WL.headlines(W).map((h) => ({ key: h.key, figure: `${h.figure} ${h.figureAlt}`, text: h.text, note: h.note, links: h.links.map((l) => ({ label: l.label, path: l.path, url: F.githubFile(l.path) })) })),
    tests: W.comparisons.filter((c) => c.test).map((c) => ({ comparison: c.id, test: c.test.name, p: c.test.p, preregistered: c.test.preregistered, significant_at_0_05: c.test.significant, verification_for_proofforge: c.classification.verification, stated_in: c.test.statedIn })),
    wins: W.wins.map((w) => ({ group: w.group, comparison: w.id, kind: w.kind ?? undefined, sentence: w.sentence })),
  },
  muse_alone_vs_proofforge: {
    note: `Every run is Muse Spark 1.3 (Contributor tier), capped at $${K.RUN_CAPS.usdList} at list prices and ${K.RUN_CAPS.seconds} s, and judged by ProofForge against the same locked specification. A0: Muse alone, compile-and-retry with Lean's errors and the axiom audit. A1: the ProofForge harness. A2: A1 with Muse Wonder 1.0 as lemma planner. On Cetus, Euler and Hundred both Muse alone and the harness were accepted in every run. On Balancer and Knight, A2 was accepted more often and at a lower list price per verified run than Muse alone (cost_per_verified_run). On Compound no run of any method has proved every requirement; the build team's library-based proof is VERIFIED on the deployed judge.`,
    rows: K.COMPARISON.map((r) => ({
      task: r.task,
      incident: r.incident,
      requirements: r.requirements,
      muse_alone_A0: { accepted: r.alone.accepted, runs: r.alone.runs },
      with_proofforge: r.harness.map((h) => ({ arm: h.arm, accepted: h.accepted, runs: h.runs })),
      implement_from_specification: { arm: r.implement.arm, accepted: r.implement.accepted, runs: r.implement.runs },
      vulnerable_code_refuted: r.refutations.map((x) => ({ candidate: x.label, passport: `results/counterexamples-1/${x.target}/passport.json`, refuted_requirements: x.refuted, kernel_checked_refutations: x.kernelChecked })),
      library_1: r.library
        ? {
            source: r.library.source,
            muse_alone_A0: r.library.alone ? { accepted: r.library.alone.accepted, runs: r.library.alone.runs } : null,
            A2_planner_and_library: { accepted: r.library.withLibrary.accepted, runs: r.library.withLibrary.runs },
            A2_planner_and_library_topdown: r.library.topdown ? { accepted: r.library.topdown.accepted, runs: r.library.topdown.runs } : null,
          }
        : null,
      all_runs: { muse_alone_A0: K.aloneRuns(r).accepted + " of " + K.aloneRuns(r).runs.length, ...(K.plannerRuns(r) ? { A2_with_wonder_planner: K.plannerRuns(r).accepted + " of " + K.plannerRuns(r).runs.length } : {}) },
    })),
    library_comparison: { source: K.LIBRARY_RUN.source, tasks: K.LIBRARY_RUN.tasks, readme: `${K.LIBRARY_RUN.source}/README.md` },
    cost_per_verified_run: K.COST_PER_VERIFIED.map((c) => ({
      incident: c.incident,
      muse_alone_A0: { verified: c.alone.verified, runs: c.alone.runs, usd_list_price_all_runs: c.alone.usdList, usd_list_price_per_verified_run: c.alone.usdPerVerified },
      A2_with_wonder_planner: { verified: c.planner.verified, runs: c.planner.runs, usd_list_price_all_runs: c.planner.usdList, usd_list_price_per_verified_run: c.planner.usdPerVerified },
      fisher_exact_one_sided_p_on_rate: c.fisherOneSidedP,
    })),
  },
  specification_strength: { ...K.SPEC_STRENGTH, note: "Single-site mutants of each reference solution, built in the judge image; rejected means failing the property tests, and kernelChecked counts rejections that also carry a kernel-checked refutation of a locked requirement." },
  counterexamples: { ...K.COUNTEREXAMPLES, cetus_hotfix: K.CETUS_HOTFIX },
  open_weight_models: K.OPEN_WEIGHTS,
  wonder_planner: K.PLANNER,
  proofforgefin: K.LIBRARY,
  hackathon: K.HACKATHON,
  scope: K.SCOPE,
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
    `${count(flagships.length)} real financial failures with ${F.lossTotalPhrase()} taken or lost, as the cited sources report. Each vulnerable version is refuted by a kernel-checked counterexample, and each was repaired by Muse Spark 1.3 (Meta), with Muse Wonder 1.0 planning where stated, and checked by ProofForge. Machine-readable version: /evidence.json. Source: ${F.REPO_URL}`,
    "",
  );
  const wo = evidence.meta_models_with_proofforge;
  L.push("## The frontier, measured: Meta's models with ProofForge", "");
  L.push(`- ${wo.note}`);
  L.push(`- ${wo.summary} Ledger: ${F.githubFile(wo.source)}; prose: ${F.githubFile(wo.readme)}; page: /frontier`);
  for (const h of wo.headline) L.push(`- ${h.figure}: ${h.text} ${h.note} Full comparison: ${h.links[0].url}`);
  const dims = wo.counts.by_dimension_for_proofforge;
  L.push(`- Every comparison, by dimension, with ProofForge: ${Object.entries(dims).map(([k, v]) => `${k.replace("_", " ")} better on ${v.win}, the same on ${v.tie}, worse on ${v.loss}`).join("; ")}.`);
  L.push("", "### Verified only with ProofForge", "");
  for (const w of wo.wins.filter((x) => x.group === 1)) L.push(`- ${w.sentence.replace(/`/g, "")}`);
  L.push("", `The ${wo.counts.wins_both_verified_proofforge_cheaper_or_faster} comparisons where the model verified either way and ProofForge made it cheaper or faster, and the ${wo.counts.wins_other} gains of other kinds, are listed in /evidence.json (meta_models_with_proofforge.wins) and on /frontier.`, "");
  for (const f of flagships) {
    L.push(`## ${f.incident}, ${f.date}`, "");
    if (f.reconstructed) L.push(`- Reconstructed: ${f.reconstructed}`);
    L.push(`- Loss: ${f.loss.amount} ${f.loss.basis}. Sources: ${f.loss.sources.map((s) => s.url).join(", ")}`);
    L.push(`- Bug: ${f.bug}`);
    if (f.context) L.push(`- Context: ${f.context}`);
    L.push(`- Property proved in Lean 4 (${f.property_proved.requirement}): ${f.property_proved.text}`);
    const vp = f.vulnerable_code.passport;
    L.push(`- Vulnerable code (${f.vulnerable_code.label}): ${f.vulnerable_code.verdict}. ${f.vulnerable_code.finding} Kernel-checked counterexample: ${f.vulnerable_code.kernel_checked_counterexample}${vp ? `. Passport ${vp.sha256} (${vp.path})` : ""}`);
    for (const v of f.versions ?? []) if (v.passport.sha256 !== vp?.sha256 && v.passport.sha256 !== f.muse_repair.passport.sha256) L.push(`- ${v.version} (${v.detail}): ${v.verdict}. ${v.finding} Passport ${v.passport.sha256} (${v.passport.path})`);
    const m = f.muse_repair;
    const reqs = Object.keys(m.passport.requirements).length;
    L.push(`- Muse repair${m.planner ? `, planned by ${m.planner}` : ""}: ${m.verdict}, ${reqs} of ${reqs} requirements, ${m.passport.kernels} kernels, ${m.passport.property_cases} property cases; attempt ${m.attempt}, ${m.seconds} s, ${m.model_calls} model calls, $${m.usd_list_price} at list prices, $${m.usd_charged} charged. Passport ${m.passport.sha256} (${m.passport.path})`);
    const eq = f.muse_repair_equivalent_to_upstream_fix;
    if (eq) L.push(`- Proved separately (${eq.file}, axioms ${eq.axioms}): ${eq.theorem}`);
    for (const u of f.unresolved_attempts ?? [])
      L.push(`- Earlier attempt ${u.attempt}: ${u.passport.status}; its executable ${u.passport.executable === "PASS" ? `passed all ${u.passport.property_cases} property cases` : u.passport.executable}, but it proved ${u.required_theorems_proved} of ${reqs} requirements before its ${u.stopped_by}, so no VERIFIED Passport. Passport ${u.passport.sha256} (${u.passport.path})`);
    L.push(`- Reproduce: ${m.passport.reproduce}`);
    if (typeof f.real_code === "string") {
      L.push(`- Real code: ${f.real_code}`);
      L.push(`- Not proved: ${f.not_proved.join(" ")}`);
      L.push(`- Task: ${f.readme}`, "");
      continue;
    }
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
  L.push("## Muse alone and Muse with ProofForge", "");
  L.push(`- ${evidence.muse_alone_vs_proofforge.note}`);
  for (const r of evidence.muse_alone_vs_proofforge.rows) {
    const runs = (x) => `${x.accepted} of ${x.runs.length}`;
    L.push(`- ${r.incident} (${r.task}): Muse alone accepted ${runs(r.muse_alone_A0)}; ${r.with_proofforge.map((h) => `${h.arm} ${runs(h)}`).join(", ")}; implement mode ${runs(r.implement_from_specification)}; vulnerable code refuted on ${r.vulnerable_code_refuted.map((x) => `${x.kernel_checked_refutations} of ${x.refuted_requirements} requirements (${x.candidate}) by kernel-checked counterexamples`).join(" and ")}.`);
  }
  for (const r of K.COMPARISON.filter((x) => x.library)) {
    const pl = K.plannerRuns(r);
    L.push(`- ${r.incident} over all measured runs, including ${K.LIBRARY_RUN.source}: Muse alone ${K.aloneRuns(r).accepted} of ${K.aloneRuns(r).runs.length}; with the Muse Wonder planner ${pl.accepted} of ${pl.runs.length}.`);
  }
  for (const c of K.COST_PER_VERIFIED)
    L.push(`- ${c.incident}, list price per verified run: $${c.planner.usdPerVerified.toFixed(2)} with ProofForge and the Muse Wonder planner (${c.planner.verified} of ${c.planner.runs} verified), $${c.alone.usdPerVerified.toFixed(2)} for Muse on its own (${c.alone.verified} of ${c.alone.runs}). One-sided Fisher exact p = ${c.fisherOneSidedP} on the rate.`);
  L.push(`- Specification strength (${K.SPEC_STRENGTH.source}, ${K.SPEC_STRENGTH.doc}): the ${K.SPEC_STRENGTH.specifications} locked specifications reject ${K.SPEC_STRENGTH.rejected} of ${K.SPEC_STRENGTH.compiled} compiling single-site mutants of their reference solutions, ${K.SPEC_STRENGTH.kernelChecked} with kernel-checked counterexamples; ${K.SPEC_STRENGTH.survivedDiffers} surviving mutants behave differently and are reported as specification gaps.`);
  L.push(`- Counterexamples (${K.COUNTEREXAMPLES.source}): ${K.COUNTEREXAMPLES.kernelChecked} of ${K.COUNTEREXAMPLES.refuted} refuted requirements over ${K.COUNTEREXAMPLES.candidates} candidates refuted by a Lean theorem accepted by six kernels and leanchecker. The Cetus same-day hotfix: ${K.CETUS_HOTFIX.statement} at n = ${K.CETUS_HOTFIX.input} (2^192).`);
  for (const o of K.OPEN_WEIGHTS)
    L.push(`- ${o.model} (${o.serving}; ${o.source}${o.complete ? "" : ", incomplete"}): A0 ${o.a0.completed} of ${o.a0.n}, A1 ${o.outage ? `${o.outage.a1Completed} of ${o.outage.a1N} excluding runs ended by an outage (${o.a1.completed} of ${o.a1.n} including them)` : `${o.a1.completed} of ${o.a1.n}`}; McNemar p = ${o.mcnemarP}, 95% interval of the difference [${o.ci95.join(", ")}].`);
  for (const p of K.PLANNER) L.push(`- Muse Wonder planner on ${p.incident}: A1 proved ${p.a1.join(" and ")} of ${p.requirements} requirements, A2 ${p.a2.join(" and ")}; A2 accepted in ${p.a2Accepted} of ${p.a2.length}.`);
  L.push(`- ProofForgeFin (lib/): ${K.LIBRARY.theorems} theorems and ${K.LIBRARY.definitions} definitions in ${K.LIBRARY.files} files; ${K.LIBRARY.constantsChecked} constants of the library and demonstrations accepted by six kernels. A library-based Compound candidate written by the build team (${K.LIBRARY.compoundFixture}) is VERIFIED on the deployed judge, Passport ${K.LIBRARY.compoundLivePassport} (${K.LIBRARY.compoundLivePassportFile}).`);
  L.push(`- Built during the ${K.HACKATHON.event}: first commit ${K.HACKATHON.firstCommit}, submissions due ${K.HACKATHON.submissionsDue} (ORIGIN.md).`);
  L.push(`- Scope: ${K.SCOPE}`);
  L.push("");
  L.push("## Implemented from the specification alone", "");
  for (const i of evidence.implemented_flagships) {
    const n = Object.keys(i.passport.requirements).length;
    L.push(`- ${i.flagship}: ${i.status}, ${n} of ${n} requirements. Passport ${i.passport.sha256} (${i.passport.path}). Reproduce: ${i.passport.reproduce}`);
  }
  if (F.IMPLEMENTS) L.push(`- Benchmark: ${F.IMPLEMENTS.value} of ${F.IMPLEMENTS.of} ${F.IMPLEMENTS.label} (${F.IMPLEMENTS.detail}; ${F.IMPLEMENTS.source}).`);
  L.push("");
  L.push("## Benchmark", "");
  L.push(`- ${evidence.benchmark.tasks} repair tasks in six families: ${evidence.benchmark.families.map((x) => `${x.family.toLowerCase()} (${x.tasks})`).join(", ")}; ${F.BENCHMARK.splits.dev} development, ${F.BENCHMARK.splits.val} validation, ${F.BENCHMARK.splits.test} test.`);
  L.push(`- E1 (${E1.source}): on the ${E1.tasks} frozen test tasks, ${E1.arms.map((a) => `${a.key} ${a.label} completed ${a.completed}`).join(", ")}; McNemar exact p = ${E1.mcnemarP} against A0. ${E1.tasks * E1.arms.length} runs cost $${E1.batchUsdList} at list prices.`);
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
  L.push(`- /: overview with the ${count(flagships.length).toLowerCase()} incidents`, "- /frontier: what Meta's models reach with ProofForge that they do not reach on their own, and every comparison", "- /#check: check a fix; submits a real-world candidate to POST /api/verify on the API, with the committed Passport as fallback", "- /forge: live forge session (replay of a recorded Muse repair, then a fresh check)", "- /results: E1 and E2 per arm, family and case", "");
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
