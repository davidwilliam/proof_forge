// Writes public/evidence.json and public/llms.txt: a machine-readable summary of the claims on
// the home page, for people and agents evaluating ProofForge. No checks are run.
// Usage: node scripts/evidence.mjs           write both files
//        node scripts/evidence.mjs --check   exit 1 if either file is out of date
//
// Passport hashes, statuses, reproduction commands, run costs and real-code counts are read
// from the committed result files. The wording (loss figures, properties, limits) comes from
// lib/flagships.ts, the E1 and E2 figures from lib/evidence.ts and the comparison with Muse alone,
// the counterexample, open-weight, planner and library figures, the Meta models and tools and the
// Compound Proposal 62 record from lib/contribution.ts, which
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
const LIB = JSON.parse(fs.readFileSync(path.join(web, "generated/library.json"), "utf8"));
const wc = (id) => W.comparisons.find((c) => c.id === id);
const C4 = wc(WL.HEADLINE_IDS.compound);
const CP = wc(WL.HEADLINE_IDS.compoundPooled);
const C3 = wc(WL.HEADLINE_IDS.compoundFirst);
const C2 = wc("frontier-2/rw-compound-comp");
const OZ = wc(WL.HEADLINE_IDS.oz);
const usd2 = (n) => `$${n.toFixed(2)}`;

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

/** Compound Proposal 62: not a flagship record (lib/flagships.ts); its verified repairs are Muse Code runs of frontier-3 and frontier-4. */
function compound() {
  const c = K.COMPOUND;
  const row = K.COMPARISON.find((r) => r.key === c.key);
  const repairs = c.museRepairs.map((r) => {
    const s = readExact(r.summary);
    const p = passport({ path: r.passport });
    // The Passport's stored reproduce line names the candidate without the runs/ directory; the committed candidate is r.candidate.
    p.reproduce = `bin/proofforge verify ${r.passport} --candidate ${r.candidate}`;
    return {
      run: `results/frontier-4 ${r.run}`,
      agent: s.muse_code,
      model: s.model,
      mcp_profile: s.mcp_profile,
      ended_by: s.ended_by,
      seconds: Math.round(s.elapsed_s),
      model_calls: s.meter.calls,
      usd_list_price: s.meter.usd_list,
      usd_charged: s.meter.usd_actual,
      candidate: r.candidate,
      passport: p,
    };
  });
  return {
    key: c.key,
    incident: c.incident,
    date: c.date,
    loss: { amount: c.loss.amount, basis: c.loss.basis, sources: c.loss.sources, quoted_from: c.readme },
    bug: c.bug,
    property_proved: { text: c.property.text, requirement: c.property.requirement },
    requirements: row.requirements,
    task: c.task,
    readme: c.readme,
    vulnerable_code: { label: c.vulnerable.label, verdict: "REFUTED", finding: c.vulnerable.finding, kernel_checked_counterexample: c.vulnerable.witness, passport: passport({ path: c.vulnerable.passport }) },
    upstream_fix: { label: c.fix.label, passport: passport({ path: c.fix.passport }) },
    muse_code_with_proofforge: {
      source: COMPOUND_README,
      verified: C4.proofforge.verified,
      runs: C4.proofforge.runs,
      alone_verified: C4.alone.verified,
      alone_runs: C4.alone.runs,
      alone_pooled_with_frontier_2_and_3: { verified: CP.alone.verified, runs: CP.alone.runs },
      fisher_exact_one_sided_p: C4.test.p,
      fisher_exact_one_sided_p_pooled: CP.test.p,
      usd_list_price_per_verified_run: C4.proofforge.usdPerVerified,
      first_verified_repairs: {
        source: COMPOUND_FIRST,
        verified: C3.proofforge.verified,
        runs: C3.proofforge.runs,
        fisher_exact_one_sided_p_frontier_4_against_frontier_3: C4.test.secondary.p,
      },
      verified_runs: repairs,
    },
    earlier_runs: `Before frontier-3 no measured run of any method verified the task (${COMPOUND_FIRST}): Muse Spark 1.3 alone (A0) ${K.aloneRuns(row).accepted} of ${K.aloneRuns(row).runs.length}, with the ProofForge harness (A1) ${row.harness.filter((h) => h.arm === "A1").map((h) => `${h.accepted} of ${h.runs.length}`).join(", ")}, with the harness and the Muse Wonder planner ${K.plannerRuns(row).accepted} of ${K.plannerRuns(row).runs.length}, implement mode ${row.implement.accepted} of ${row.implement.runs.length}, and Muse Code in frontier-2 ${C2.alone.verified} of ${C2.alone.runs} on its own and ${C2.proofforge.verified} of ${C2.proofforge.runs} with ProofForge.`,
    real_code: { method: c.realCode.method, sequences: c.realCode.sequences, results: c.realCode.rows, report: c.realCode.report },
    not_proved: c.notProved,
  };
}
const COMPOUND_README = "results/frontier-4/README.md";
const COMPOUND_FIRST = "results/frontier-3/README.md";
const compoundRecord = compound();
const incidents = [...F.FLAGSHIPS.map((f) => f.incident), compoundRecord.incident];
const notClaimed = [
  "The deployed Solidity and Move code is not itself proved. Each incident's Lean 4 port is a reviewed hand translation, tested against the real code on the stated inputs; the translation is not machine-checked.",
  "A requirement covers exactly what its Lean statement says. Each port models only the logic named in its task README.",
  "Loss figures are quoted from the sources each task README cites.",
  "The JSON wrapper around each proved function is tested, not proved.",
  ...F.FLAGSHIPS.map((f) => f.reconstruction).filter(Boolean),
];

/** frontier-4 on Compound, worded as the home page's Compound strip (lib/home-view.ts). */
function compoundHeadline() {
  const cap = C4.alone.caps[0];
  return {
    key: "compound",
    figure: `${C4.alone.verified} → ${C4.proofforge.verified}`,
    figureAlt: `of ${C4.proofforge.runs}`,
    text: `Compound Proposal 62, the COMP reward distribution, a task no measured run of any arm had verified before frontier-3: ${WL.modelName(C4.model)} in Muse Code verified ${WL.runsOf(C4.proofforge)} runs with ProofForge, at ${usd2(C4.proofforge.usdPerVerified)} per verified run, and ${WL.runsOf(C4.alone)} on its own after spending ${usd2(C4.alone.usdTotal)}. Every verified run proves the three bounds over any sequence of operations (rewards, each account, no backdated rewards); no run on its own proved any of them. Passports ${compoundRecord.muse_code_with_proofforge.verified_runs.map((r) => r.passport.sha256.slice(0, 16)).join(", ")}.`,
    note: `Preregistered one-sided ${C4.test.name.replace(/^one-sided /, "")} p = ${WL.pValue(C4.test.p)}; with the runs on its own of frontier-2 and frontier-3 pooled, ${WL.runsOf(C4.proofforge)} against ${WL.runsOf(CP.alone)}, p = ${WL.pValue(CP.test.p)}. frontier-3 gave the first verified repairs, ${WL.runsOf(C3.proofforge)} with ProofForge; frontier-4 measures the build feedback, the skill step and the ProofForgeFin additions built from those runs (${WL.runsOf(C4.proofforge)} against ${WL.runsOf(C3.proofforge)}, preregistered p = ${WL.pValue(C4.test.secondary.p)}). Caps of $${cap.usd} and ${cap.seconds / 3600} hours per run, list prices.`,
    links: [{ label: "Full comparison", path: C4.links.comparison }, ...[...new Set([...C4.links.reports, ...C3.links.reports])].map((p) => ({ label: p.replace(/^results\//, "").replace(/\/README\.md$/, ""), path: p }))],
  };
}

const evidence = {
  name: "ProofForge",
  repository: F.REPO_URL,
  headline: F.HEADLINE,
  summary: F.SUMMARY,
  generated_by: "web/scripts/evidence.mjs from committed result files",
  hackathon: { ...K.HACKATHON, origin: "ORIGIN.md" },
  meta_models_and_tools: K.META_TOOLING.map((m) => ({ name: m.name, kind: m.kind, model_id: m.id ?? undefined, how: m.how, paths: m.paths, experiments: m.experiments })),
  real_failures: {
    count: incidents.length,
    incidents,
    refuted_with_kernel_checked_counterexamples: incidents.length,
    note: `Each vulnerable version is refuted by a kernel-checked counterexample. The loss total counts the ${flagships.length} failures with a quoted dollar loss; ${compoundRecord.incident} is listed in compound_proposal_62 and is not in the total.`,
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
    headline: WL.headlines(W)
      .flatMap((h) => (h.key === "oz" ? [h, compoundHeadline()] : [h]))
      .map((h) => ({ key: h.key, figure: `${h.figure} ${h.figureAlt}`, text: h.text, note: h.note, links: h.links.map((l) => ({ label: l.label, path: l.path, url: F.githubFile(l.path) })) })),
    tests: W.comparisons.filter((c) => c.test).map((c) => ({ comparison: c.id, test: c.test.name, p: c.test.p, preregistered: c.test.preregistered, significant_at_0_05: c.test.significant, verification_for_proofforge: c.classification.verification, stated_in: c.test.statedIn })),
    wins: W.wins.map((w) => ({ group: w.group, comparison: w.id, kind: w.kind ?? undefined, sentence: w.sentence })),
  },
  checking: {
    lean: "Lean v4.35.0",
    judge: "lake comparator --paranoid in a fresh bubblewrap sandbox with six kernels (Lean default and paranoid, lean4lean, nanoda, con-leche, con-ron), then leanchecker and an axiom audit; the executable rebuilt from the same source runs generated property cases",
    statuses: ["VERIFIED", "REFUTED", "UNRESOLVED"],
  },
  loss_total: { phrase: F.lossTotalPhrase(), usd_millions_rounded_down: F.lossTotalMillions(), note: "the sum of the loss figures quoted for the incidents, each rounded down; the figures measure different things (taken, net profit to the attacker, realized loss), as each states" },
  flagships,
  compound_proposal_62: compoundRecord,
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
  muse_alone_vs_proofforge: {
    note: `Every run is Muse Spark 1.3 (Contributor tier), capped at $${K.RUN_CAPS.usdList} at list prices and ${K.RUN_CAPS.seconds} s, and judged by ProofForge against the same locked specification. A0: Muse alone, compile-and-retry with Lean's errors and the axiom audit. A1: the ProofForge harness. A2: A1 with Muse Wonder 1.0 as lemma planner. On Cetus, Euler and Hundred both Muse alone and the harness were accepted in every run. On Balancer and Knight, A2 was accepted more often and at a lower list price per verified run than Muse alone (cost_per_verified_run). On Compound, Muse Code (Muse Spark 1.3) with ProofForge verified ${C3.proofforge.verified} of ${C3.proofforge.runs} runs in frontier-3 (results/frontier-3/README.md), the first verified repairs of the task; on its own it verified ${C3.alone.verified} of ${C3.alone.runs}, and ${CP.alone.verified} of ${CP.alone.runs} with frontier-2 pooled. Before frontier-3 no run of any method had proved every Compound requirement (the rows below); the build team's library-based proof is VERIFIED on the deployed judge.`,
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
  proofforgefin: { ...K.LIBRARY, counts: LIB },
  scope: K.SCOPE,
  not_claimed: notClaimed,
  reproduce: {
    setup: [
      `git clone ${F.REPO_URL} && cd proof_forge`,
      "docker build -t proofforge-lean:4.35.0 -f infra/docker/Dockerfile.lean infra/docker",
    ],
    passports: [
      ...flagships.flatMap((f) => [f.vulnerable_code.passport, f.muse_repair.passport, ...(f.versions ?? []).map((v) => v.passport)]),
      compoundRecord.vulnerable_code.passport,
      ...compoundRecord.muse_code_with_proofforge.verified_runs.map((r) => r.passport),
      compoundRecord.upstream_fix.passport,
    ]
      .filter(Boolean)
      .filter((p, i, all) => all.findIndex((q) => q.sha256 === p.sha256) === i)
      .map((p) => ({ passport: p.path, sha256: p.sha256, status: p.status, command: p.reproduce })),
  },
};

const count = (n) => ["No", "One", "Two", "Three", "Four", "Five", "Six"][n] ?? String(n);

function llms() {
  const L = [];
  L.push("# ProofForge", "", `> ${F.HEADLINE} ${F.SUMMARY}`, "");
  const plannerKeys = F.FLAGSHIPS.filter((f) => f.repair.planner).map((f) => f.incident);
  L.push(
    `With ProofForge as its MCP server, Muse Code, Meta's coding agent, running ${WL.modelName(OZ.model)} verified ${WL.runsOf(OZ.proofforge)} runs on OpenZeppelin Math.sqrt behind the Aerodrome first deposit, against ${WL.runsOf(OZ.alone)} on its own (preregistered one-sided Fisher exact p = ${WL.pValue(OZ.test.p)}), and ${WL.runsOf(C4.proofforge)} runs on Compound Proposal 62, against ${WL.runsOf(C4.alone)} (p = ${WL.pValue(C4.test.p)}), a task no measured run had verified before frontier-3.`,
    "",
    `${count(incidents.length)} real financial failures are specified in Lean 4: ${incidents.join(", ")}. Each vulnerable version is refuted by a kernel-checked counterexample, and each has a VERIFIED repair written by ${WL.modelName(OZ.model)} (with Muse Wonder 1.0 planning on ${plannerKeys.join(" and ")}, and in Muse Code on Compound) and checked by ProofForge. The ${count(flagships.length).toLowerCase()} with a quoted dollar loss total ${F.lossTotalPhrase()} taken or lost, as the cited sources report.`,
    "",
    `Built during the ${K.HACKATHON.event}: first commit ${K.HACKATHON.firstCommit}, submissions due ${K.HACKATHON.submissionsDue} (ORIGIN.md). Machine-readable version: /evidence.json. Source: ${F.REPO_URL}`,
    "",
  );
  L.push("## Meta models and tools used", "");
  for (const m of evidence.meta_models_and_tools) L.push(`- ${m.name} (${m.kind}${m.model_id ? `; model ID ${m.model_id}` : ""}). ${m.how} Results: ${m.experiments.join(", ")}.`);
  L.push("");
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
  {
    const c = compoundRecord;
    const m = c.muse_code_with_proofforge;
    L.push(`## ${c.incident}, ${c.date}`, "");
    L.push(`- Loss: ${c.loss.amount}, ${c.loss.basis}. Sources: ${c.loss.sources.join(", ")}`);
    L.push(`- Bug: ${c.bug.replace(/`/g, "")}`);
    L.push(`- Property proved in Lean 4 (${c.property_proved.requirement}): ${c.property_proved.text}`);
    const vp = c.vulnerable_code.passport;
    L.push(`- Vulnerable code (${c.vulnerable_code.label}): ${vp.status}, ${Object.values(vp.requirements).filter((x) => x === "REFUTED").length} of ${c.requirements} requirements refuted. ${c.vulnerable_code.finding} Kernel-checked counterexample: ${c.vulnerable_code.kernel_checked_counterexample}. Passport ${vp.sha256} (${vp.path})`);
    L.push(`- Muse repair in Muse Code with ProofForge (${m.source}): ${m.verified} of ${m.runs} runs VERIFIED, ${m.alone_verified} of ${m.alone_runs} on its own (${m.alone_pooled_with_frontier_2_and_3.verified} of ${m.alone_pooled_with_frontier_2_and_3.runs} with frontier-2 and frontier-3 pooled); one-sided Fisher exact p = ${WL.pValue(m.fisher_exact_one_sided_p)}, pooled p = ${WL.pValue(m.fisher_exact_one_sided_p_pooled)}. The first verified repairs came in frontier-3 (${m.first_verified_repairs.source}): ${m.first_verified_repairs.verified} of ${m.first_verified_repairs.runs} with ProofForge; frontier-4 against frontier-3, p = ${WL.pValue(m.first_verified_repairs.fisher_exact_one_sided_p_frontier_4_against_frontier_3)}.`);
    for (const r of m.verified_runs) {
      const reqs = Object.keys(r.passport.requirements).length;
      L.push(`  - ${r.run}: ${r.passport.status}, ${reqs} of ${reqs} requirements, ${r.passport.kernels} kernels, ${r.passport.property_cases} property cases; ${r.agent}, ${r.model}, MCP profile ${r.mcp_profile}, ${r.ended_by === "accepted" ? "ended at an accepted check" : `ended by ${r.ended_by}`}, ${r.seconds} s, ${r.model_calls} model calls, ${usd2(r.usd_list_price)} at list prices, $${r.usd_charged} charged. Passport ${r.passport.sha256} (${r.passport.path}). Reproduce: ${r.passport.reproduce}`);
    }
    L.push(`- ${c.earlier_runs}`);
    L.push(`- ${c.upstream_fix.label}: ${c.upstream_fix.passport.status}, ${Object.keys(c.upstream_fix.passport.requirements).length} of ${c.requirements} requirements. Passport ${c.upstream_fix.passport.sha256} (${c.upstream_fix.passport.path})`);
    L.push(`- Real code: ${c.real_code.method}`);
    for (const r of c.real_code.results) L.push(`  - ${r.code}: ${r.violating} of ${c.real_code.sequences} sequences break a requirement (${r.note})`);
    L.push(`- Not proved: ${c.not_proved.join(" ")}`);
    L.push(`- Task: ${c.readme}`, "");
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
  L.push(`- ProofForgeFin (lib/): ${LIB.theorems} theorems and ${LIB.definitions} definitions in ${LIB.files} files; ${LIB.latestFullRun.safeConstants} safe constants of the library and demonstrations accepted by six kernels in the latest full run (${LIB.latestFullRun.source}); the last committed full run (${LIB.committedFullRun.file}) checked ${LIB.committedFullRun.safeConstants} and leanchecker replayed ${LIB.committedFullRun.modulesReplayed} modules. A library-based Compound candidate written by the build team (${K.LIBRARY.compoundFixture}) is VERIFIED on the deployed judge, Passport ${K.LIBRARY.compoundLivePassport} (${K.LIBRARY.compoundLivePassportFile}).`);
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
  L.push(`- /: overview with the measured gains of Meta's models with ProofForge and the ${count(incidents.length).toLowerCase()} real failures`, "- /frontier: what Meta's models reach with ProofForge that they do not reach on their own, and every comparison", "- /#check: check a fix; submits a real-world candidate to POST /api/verify on the API, with the committed Passport as fallback", "- /app: the Balancer V2 rounding exploit replayed on the deployed swap code, the plus-one hotfix and the repair Muse proved with ProofForge", "- /challenge: hidden payout variants checked by the property tests derived from the locked requirements, each violation with a concrete witness", "- /forge: live forge session (replay of a recorded Muse repair, then a fresh check)", "- /passport/{sha256}: one Passport, with its per-requirement statuses, hashes and reproduction command", "- /results: E1 and E2 per arm, family and case", "- /methods: every preregistered experiment, with its question, commit, run count, primary test, status and result", "- /verify: the commands that reproduce a Passport and what bin/proofforge verify compares", "- /brand: the identity kit, with the palette, the rules and every file to download", "- /about: who built ProofForge, why, what was built during the hackathon, and acknowledgments", "");
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
