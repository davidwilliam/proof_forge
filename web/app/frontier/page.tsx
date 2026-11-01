import type { Metadata } from "next";
import Link from "next/link";
import { ComparisonTable, WinsHeadline } from "@/components/Wins";
import { WinsExplorer, type WinRow } from "@/components/WinsExplorer";
import { githubFile } from "@/lib/flagships";
import {
  DIMENSIONS,
  GROUPS,
  KIND_LABEL,
  countsSentence,
  fmtInt,
  headlines,
  kindOf,
  modelName,
  testPhrase,
  winDetail,
  type Comparison,
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

export default function WinsPage() {
  const d = WINS;
  const cnt = d.counts;
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
        What Meta&apos;s models reach with ProofForge that they do not reach on their own. Each comparison runs the same Meta model on the same
        tasks and caps twice, on its own and with ProofForge, and judges the final candidate of every run against the same locked specification, and a run counts as verified only with a VERIFIED Passport (on the E1 benchmark, a
        judge acceptance and a rebuilt executable that passes 2,000 property cases). {countsSentence(d)} Every comparison is listed below the gains,
        each with its runs and Passports.
      </p>
      <p className="wins-sources">
        Source: <a href={githubFile(d.source)}>{d.source}</a>, written by <a href={githubFile(d.generator)}>{d.generator}</a> from the raw run
        files with no model calls; the same comparisons in prose: <a href={githubFile(d.readme)}>{d.readme}</a>. Reproduce with{" "}
        <code>python3 eval/wins.py</code> and <code>python3 tests/test_wins.py</code>.
      </p>

      <section aria-labelledby="wins-strongest">
        <h2 id="wins-strongest">The largest gains</h2>
        <WinsHeadline items={headlines(d)} />
      </section>

      <section aria-labelledby="wins-dims">
        <h2 id="wins-dims">Every comparison, by dimension</h2>
        <p className="wins-group-lead">
          Each comparison is classified on five dimensions: better, the same or worse with ProofForge. Across all {cnt.comparisons}, verification is{" "}
          {wl("verification")}, requirements proved {wl("requirements")}, cost {wl("cost")} and time {wl("time")}. Every comparison where it is worse is in the
          tables below.
        </p>
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
      </section>

      <WinsExplorer rows={rows()} groups={GROUPS} />

      <section aria-labelledby="wins-all" id="every-comparison">
        <h2 id="wins-all">Every comparison</h2>
        <p className="wins-group-lead">
          Each pair of figures is on its own / with ProofForge. Wall time is the mean of the verified runs; on E1 aggregates, the mean on the tasks
          both arms verified. The last column classifies each dimension with ProofForge: V verification, C cost, T time, R requirements, S cap
          stops; + better, = same, x worse, - not applicable.
        </p>
        <ComparisonTable rows={realAndAggregates} caption={`Real-world tasks and aggregates, ${realAndAggregates.length} comparisons`} />
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
