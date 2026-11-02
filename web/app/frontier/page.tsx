import type { Metadata } from "next";
import Link from "next/link";
import { FactorSwarm, type FactorPoint } from "@/components/FactorSwarm";
import { CatchWaffles, DimensionBars, KpiStrip, RunStrips, type Strip } from "@/components/FrontierViz";
import { GainsMap, type WinRow } from "@/components/GainsMap";
import { ComparisonTable } from "@/components/Wins";
import { githubFile } from "@/lib/flagships";
import {
  DIMENSIONS,
  GROUPS,
  KIND_LABEL,
  HEADLINE_IDS,
  comparison,
  countsSentence,
  factor1,
  fmtInt,
  headlines,
  kindOf,
  modelName,
  pValue,
  runsOf,
  testPhrase,
  usd,
  winDetail,
  type Comparison,
  type Headline,
} from "@/lib/wins";
import { WINS } from "@/lib/wins-data";

const description = `What Meta's models reach with ProofForge that they do not reach on their own: every measured comparison, from results/wins/ledger.json. ${countsSentence(WINS)}`;

export const metadata: Metadata = {
  title: "The frontier, measured, ProofForge",
  description,
  openGraph: { title: "The frontier, measured, ProofForge", description },
};

const reportLabel = (p: string) => p.replace(/^results\//, "").replace(/\/(README|e1|e2)\.md$/, "");

function rows(): WinRow[] {
  const d = WINS;
  return d.wins.map((w, i) => {
    const kind = kindOf(d, w);
    const c = d.comparisons.find((x) => x.id === w.id);
    const links = c ? c.links : d.catches.links;
    return {
      key: `${w.group}-${i}`,
      group: w.group,
      id: w.id,
      kind,
      kindLabel: KIND_LABEL[kind],
      model: c ? modelName(c.model) : "No model",
      winKind: w.kind,
      detail: winDetail(d, w),
      links: [
        { label: "Full comparison", href: githubFile(links.comparison) },
        ...links.reports.map((p) => ({ label: reportLabel(p), href: githubFile(p) })),
      ],
    };
  });
}

function factorPoints(): FactorPoint[] {
  const d = WINS;
  const out: FactorPoint[] = [];
  d.wins.forEach((w, i) => {
    if (w.group !== 2) return;
    const c = comparison(d, w.id);
    const base = { id: w.id, kind: c.kind, kindLabel: KIND_LABEL[c.kind], model: modelName(c.model), detail: winDetail(d, w) };
    if (w.costFactor && w.costFactor >= 1.05) out.push({ ...base, key: `c${i}`, lane: "cost", value: w.costFactor });
    if (w.timeFactor && w.timeFactor >= 1.05) out.push({ ...base, key: `t${i}`, lane: "time", value: w.timeFactor });
  });
  return out;
}

const hrefs = (h: Headline) => h.links.map((l) => ({ label: l.label, href: githubFile(l.path) }));

/** Compound Proposal 62 from frontier-3: the first verified repairs of the task. */
function compoundStrip(): Strip {
  const d = WINS;
  const c = comparison(d, HEADLINE_IDS.compound);
  const pooled = comparison(d, HEADLINE_IDS.compoundPooled);
  const f2 = comparison(d, "frontier-2/rw-compound-comp");
  return {
    key: "compound",
    title: "Compound Proposal 62",
    context: `COMP reward distribution, a task no measured run of any arm had verified before. ${modelName(c.model)} in Muse Code.`,
    unit: "run",
    alone: c.alone,
    proofforge: c.proofforge,
    figure: `${c.alone.verified} → ${c.proofforge.verified}`,
    figureAlt: "runs verified",
    stats: [
      { value: `${c.alone.reqMean} → ${c.proofforge.reqMean}`, label: `requirements of ${c.proofforge.reqTotal} proved per run` },
      { value: `${runsOf(pooled.alone)}`, label: "verified on its own, frontier-2 and frontier-3 pooled" },
      { value: `${c.alone.capStops} to ${c.proofforge.capStops}`, label: "runs stopped by a cap" },
    ],
    text: `Compound Proposal 62, the COMP reward distribution: ${modelName(c.model)} in Muse Code verified ${runsOf(c.proofforge)} runs with ProofForge, at ${usd(c.proofforge.usdPerVerified)} per verified run, and ${runsOf(c.alone)} on its own after spending ${usd(c.alone.usdTotal)}. Both verified runs prove the three bounds over any sequence of operations (rewards, each account, no backdated rewards) that no earlier run of either arm proved.`,
    note: `Preregistered one-sided ${c.test!.name.replace(/^one-sided /, "")} p = ${pValue(c.test!.p)}; with the runs on its own of frontier-2 pooled, ${runsOf(c.proofforge)} against ${runsOf(pooled.alone)}, p = ${pValue(pooled.test!.p)}. ProofForgeFin now supplies Accumulator.Market, two-sided reward markets bounded from one case analysis, written after the frontier-2 runs stopped at 5 of 8 requirements (${runsOf(f2.proofforge)} and ${runsOf(f2.alone)} verified). Caps of $${c.alone.caps[0]!.usd} and ${c.alone.caps[0]!.seconds / 3600} hours per run, list prices.`,
    links: [
      { label: "Full comparison", href: githubFile(c.links.comparison) },
      ...[...new Set([...c.links.reports, ...f2.links.reports])].map((p) => ({ label: reportLabel(p), href: githubFile(p) })),
    ],
  };
}

/** The headline gains as run strips; the sentences and conditions of each are kept under "What was measured". */
function strips(): Strip[] {
  const d = WINS;
  const hs = new Map(headlines(d).map((h) => [h.key, h]));
  const h = (k: string) => hs.get(k)!;
  const oz = comparison(d, HEADLINE_IDS.oz);
  const v = comparison(d, HEADLINE_IDS.vyper);
  const b = comparison(d, HEADLINE_IDS.balancer);
  const open = comparison(d, HEADLINE_IDS.openAll);
  const common = (k: string) => ({ key: k, figure: h(k).figure, text: h(k).text, note: h(k).note, links: hrefs(h(k)) });
  return [
    {
      ...common("oz"),
      title: "OpenZeppelin Math.sqrt",
      context: `Behind the Aerodrome first deposit, a task no measured run had verified before. ${modelName(oz.model)} in Muse Code.`,
      unit: "run",
      alone: oz.alone,
      proofforge: oz.proofforge,
      figureAlt: "runs verified",
      stats: [
        { value: usd(oz.proofforge.usdPerVerified), label: "per verified run with ProofForge" },
        { value: usd(oz.alone.usdTotal), label: "spent on its own, nothing verified" },
        { value: `p = ${pValue(oz.test!.p)}`, label: "preregistered one-sided Fisher exact" },
      ],
    },
    compoundStrip(),
    {
      ...common("vyper"),
      title: "Vyper sqrt(), CVE-2025-26622",
      context: `Two preregistered experiments, pooled. ${modelName(v.model)} in Muse Code.`,
      unit: "run",
      alone: v.alone,
      proofforge: v.proofforge,
      figureAlt: "runs verified",
      stats: [
        { value: factor1(v.factors.cost!), label: `cheaper per verified run, ${usd(v.proofforge.usdPerVerified)} against ${usd(v.alone.usdPerVerified)}` },
        { value: factor1(v.factors.time!), label: "faster" },
        { value: `${v.alone.capStops} to ${v.proofforge.capStops}`, label: "runs stopped by a cap" },
      ],
    },
    {
      ...common("balancer"),
      title: "Balancer V2 rounding repair",
      context: `Muse Wonder 1.0 plans the lemmas and ${modelName(b.model)} proves them, on one budget.`,
      unit: "run",
      alone: b.alone,
      proofforge: b.proofforge,
      figure: `${b.alone.verified} → ${b.proofforge.verified}`,
      figureAlt: `of ${b.alone.runs} and ${b.proofforge.runs} runs`,
      stats: [
        { value: factor1(b.factors.cost!), label: `cheaper per verified run, ${usd(b.proofforge.usdPerVerified)} against ${usd(b.alone.usdPerVerified)}` },
        { value: factor1(b.factors.time!), label: "faster" },
        { value: `${b.alone.capStops} to ${b.proofforge.capStops}`, label: "runs stopped by a cap" },
      ],
    },
    {
      ...common("open"),
      title: `${modelName(open.model)}, Meta's open-weight model`,
      context: "The frozen E1 test tasks, one run per arm per task.",
      unit: "task",
      alone: open.alone,
      proofforge: open.proofforge,
      figureAlt: "verified only with ProofForge",
      stats: [
        { value: `${open.alone.verified} → ${open.proofforge.verified}`, label: `of ${open.alone.runs} tasks verified` },
        { value: factor1(open.factors.cost!), label: `cheaper per verified task, ${usd(open.proofforge.usdPerVerified)} against ${usd(open.alone.usdPerVerified)}` },
        { value: `${open.alone.capStops} to ${open.proofforge.capStops}`, label: "runs stopped by a cap" },
      ],
    },
  ];
}

export default function WinsPage() {
  const d = WINS;
  const cnt = d.counts;
  const catchHeadline = headlines(d).find((h) => h.key === "catches")!;
  const wl = (k: keyof typeof cnt.classification) => `${cnt.classification[k].win} wins and ${cnt.classification[k].loss} losses`;
  const realAndAggregates = d.comparisons.filter((c) => c.kind !== "benchmark" || c.scope === "aggregate");
  const e1Sets = [...new Set(d.comparisons.filter((c) => c.kind === "benchmark").map((c) => c.experiment))];
  const tested = d.comparisons.filter((c): c is Comparison & { test: NonNullable<Comparison["test"]> } => c.test !== null);
  const budgets = d.comparisons.filter((c) => !c.equalCaps);
  const capsText = (c: Comparison, a: "alone" | "proofforge") => c[a].caps.map((x) => `$${x.usd} and ${fmtInt(x.seconds)} s`).join(", ");
  const byExperiment = new Map<string, number[]>();
  for (const c of d.comparisons) byExperiment.set(c.experiment, [...new Set([...(byExperiment.get(c.experiment) ?? []), ...c.caveats])]);
  return (
    <main id="main" className="page wins-page">
      <h1>The frontier, measured</h1>
      <p className="lead">
        What Meta&apos;s models reach with ProofForge that they do not reach on their own: the same Meta model, the same tasks, the same caps,
        run twice. Every dot below is a measured run, filled when it ended with a VERIFIED Passport.
      </p>
      <KpiStrip d={d} />

      <section aria-labelledby="wins-strongest">
        <h2 id="wins-strongest">The largest gains, run by run</h2>
        <RunStrips items={strips()} />
      </section>

      <section aria-labelledby="wins-catches">
        <h2 id="wins-catches">Bad candidates that ordinary checking lets through</h2>
        <p className="wins-group-lead">
          Each square is one of the {d.catches.badCases} seeded bad candidates of the E2 suite, filled when the check accepted it. None of the three
          rejected any of the {d.catches.goodCases} good candidates.
        </p>
        <CatchWaffles e={d.catches} />
        <details className="wins-details strip-more">
          <summary>What was measured</summary>
          <p>{catchHeadline.text}</p>
          <p>{catchHeadline.note}</p>
          <p className="win-links">
            {hrefs(catchHeadline).map((l) => (
              <a key={l.href} href={l.href}>
                {l.label}
              </a>
            ))}
          </p>
        </details>
      </section>

      <section aria-labelledby="wins-factors">
        <h2 id="wins-factors">How much cheaper, how much faster</h2>
        <p className="wins-group-lead">
          Where both arms verified, the factor is the value on its own divided by the value with ProofForge: list dollars per verified run, and
          the mean wall time of the verified runs. One dot per comparison of group 2; point at a dot to read it.
        </p>
        <FactorSwarm points={factorPoints()} />
      </section>

      <section aria-labelledby="wins-dims">
        <h2 id="wins-dims">Every comparison, by dimension</h2>
        <p className="wins-group-lead">
          Each of the {cnt.comparisons} comparisons is classified on five dimensions: better, the same or worse with ProofForge. Across all{" "}
          {cnt.comparisons}, verification is {wl("verification")}, requirements proved {wl("requirements")}, cost {wl("cost")} and time {wl("time")}.
        </p>
        <DimensionBars d={d} />
        <details className="wins-details">
          <summary>The counts and the rule of each dimension</summary>
          <div className="table-scroll wins-dim-table">
            <table>
              <thead>
                <tr>
                  <th scope="col">Dimension</th>
                  <th scope="col" className="num">
                    Better
                  </th>
                  <th scope="col" className="num">
                    Same
                  </th>
                  <th scope="col" className="num">
                    Worse
                  </th>
                  <th scope="col" className="num">
                    Not applicable
                  </th>
                  <th scope="col" className="wins-rule">
                    Rule
                  </th>
                </tr>
              </thead>
              <tbody>
                {DIMENSIONS.map((dim) => {
                  const v = cnt.classification[dim.key];
                  return (
                    <tr key={dim.key}>
                      <th scope="row">{dim.label}</th>
                      <td className="num">{v.win}</td>
                      <td className="num">{v.tie}</td>
                      <td className="num">{v.loss}</td>
                      <td className="num">{v["n/a"]}</td>
                      <td className="small muted wins-rule">{d.rules[dim.key]}</td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
        </details>
      </section>

      <section aria-labelledby="wins-map">
        <h2 id="wins-map">Every gain, {d.wins.length} tiles</h2>
        <GainsMap rows={rows()} groups={GROUPS} />
      </section>

      <section aria-labelledby="wins-all" id="every-comparison">
        <h2 id="wins-all">Every comparison</h2>
        <p className="wins-group-lead">
          Each pair of figures is on its own / with ProofForge. Wall time is the mean of the verified runs; on E1 aggregates, the mean on the tasks
          both arms verified. The last column classifies each dimension with ProofForge: V verification, C cost, T time, R requirements, S cap
          stops; + better, = same, x worse, - not applicable.
        </p>
        <details className="wins-details">
          <summary>
            Real-world tasks and aggregates, {realAndAggregates.length} comparisons: verification better with ProofForge on{" "}
            {realAndAggregates.filter((c) => c.classification.verification === "win").length}, cost on{" "}
            {realAndAggregates.filter((c) => c.classification.cost === "win").length}, requirements on{" "}
            {realAndAggregates.filter((c) => c.classification.requirements === "win").length}
          </summary>
          <ComparisonTable rows={realAndAggregates} caption={`Real-world tasks and aggregates, ${realAndAggregates.length} comparisons`} />
        </details>
        {e1Sets.map((exp) => {
          const set = d.comparisons.filter((c) => c.experiment === exp && c.scope === "task");
          const n = (o: string) => set.filter((c) => c.classification.verification === o).length;
          return (
            <details key={exp} className="wins-details">
              <summary>
                {exp}, {set.length} per-task comparisons with {modelName(set[0]!.model)}: verification better on {n("win")}, the same on {n("tie")}, worse on{" "}
                {n("loss")}
              </summary>
              <ComparisonTable rows={set} caption={`${exp}, one run per arm per task`} />
            </details>
          );
        })}
        <div className="table-scroll wins-dim-table">
          <table>
            <caption className="small muted">
              Catches ({d.catches.id}): the same {d.catches.badCases} seeded bad and {d.catches.goodCases} good candidates checked three ways
            </caption>
            <thead>
              <tr>
                <th scope="col">Checking</th>
                <th scope="col" className="num">
                  Bad candidates accepted
                </th>
                <th scope="col" className="num">
                  Good candidates rejected
                </th>
              </tr>
            </thead>
            <tbody>
              {(
                [
                  ["Ordinary checking", "ordinary"],
                  ["Rebuild and property tests", "rebuildAndTests"],
                  ["ProofForge", "proofforge"],
                ] as const
              ).map(([label, k]) => (
                <tr key={k}>
                  <th scope="row">{label}</th>
                  <td className="num">
                    {d.catches.badAccepted[k]} of {d.catches.badCases}
                  </td>
                  <td className="num">
                    {d.catches.goodRejected[k]} of {d.catches.goodCases}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </section>

      <section aria-labelledby="wins-caveats" className="wins-caveats">
        <h2 id="wins-caveats">Statistics and methods</h2>
        <p>
          Each comparison runs the same Meta model on the same tasks and caps twice, on its own and with ProofForge, and judges the final candidate
          of every run against the same locked specification, and a run counts as verified only with a VERIFIED Passport (on the E1 benchmark, a
          judge acceptance and a rebuilt executable that passes 2,000 property cases). {countsSentence(d)} Every comparison is listed above, each
          with its runs and Passports.
        </p>
        <p>
          Source: <a href={githubFile(d.source)}>{d.source}</a>, written by <a href={githubFile(d.generator)}>{d.generator}</a> from the raw run
          files with no model calls; the same comparisons in prose: <a href={githubFile(d.readme)}>{d.readme}</a>. Reproduce with{" "}
          <code>python3 eval/wins.py</code> and <code>python3 tests/test_wins.py</code>.
        </p>
        <p>
          {tested.length} comparisons have a stated test; {tested.filter((c) => c.test.preregistered).length} of them were preregistered.
        </p>
        <ul>
          {tested
            .map((c) => (
              <li key={c.id}>
                <code>{c.id}</code>: {testPhrase(c.test, c.classification.verification)} (stated in{" "}
                <a href={githubFile(c.test.statedIn)}>{c.test.statedIn}</a>){c.flags.length ? `; ${c.flags.join("; ")}` : ""}.
              </li>
            ))}
        </ul>
        <h3>Different budgets</h3>
        <ul>
          {budgets.map((c) => (
            <li key={c.id}>
              <code>{c.id}</code>: on its own {capsText(c, "alone")}; with ProofForge {capsText(c, "proofforge")}.
            </li>
          ))}
        </ul>
        <h3>Sources not on this branch or incomplete</h3>
        <ul>
          {Object.entries(d.optionalSources).map(([k, v]) => (
            <li key={k}>
              {k}: {v.found ? `found at ${v.source}${v.on_branch === false ? ", not committed on main" : ""}` : "not found"}
              {v.note ? `; ${v.note}` : ""}.
            </li>
          ))}
        </ul>
        <h3>Per experiment</h3>
        {[...byExperiment.entries()].map(([exp, idx]) =>
          idx.length ? (
            <details key={exp} className="wins-details">
              <summary>{exp}</summary>
              <ul>
                {idx.map((i) => (
                  <li key={i}>{d.caveats[i]}</li>
                ))}
              </ul>
            </details>
          ) : null,
        )}
        <details className="wins-details">
          <summary>{d.catches.experiment}</summary>
          <ul>
            {d.catches.caveats.map((x) => (
              <li key={x}>{x}</li>
            ))}
          </ul>
        </details>
        <h3>Measured, but not a comparison of the model alone with ProofForge</h3>
        <ul>
          {d.notComparisons.map((n) => (
            <li key={n.source}>
              <code>{n.source}</code>: {n.why}
            </li>
          ))}
        </ul>
        <p className="muted small">
          The ledger also checks {d.counts.claims_checked} figures stated in the result READMEs against the raw data; {d.counts.claims_differing}{" "}
          differ, and each is listed in <a href={`${githubFile(d.readme)}#readme-claims-checked-against-the-raw-data`}>{d.readme}</a>.{" "}
          <Link href="/results">E1 and E2 results</Link>
        </p>
      </section>
    </main>
  );
}
