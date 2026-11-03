import type { Metadata } from "next";
import Link from "next/link";
import type { CSSProperties, ReactNode } from "react";
import "./results.css";
import { getJson } from "@/lib/api";
import { aggregateE2, e2ArmLabels, isE1, isE2, isMuseCode, ledgerComparison, pairText, type E1Summary, type E2Aggregate, type E2Data, type MuseCodeExperiment, type Rate } from "@/lib/results";
import { byGain, resultSentence, taskModel } from "@/lib/methods";
import { githubFile } from "@/lib/flagships";
import { ARMS, SET_MODEL, SET_ORDER, armName, e1Grid, e1Lead, resultsKpis, usdPerCompleted } from "@/lib/results-view";
import { formatUsd, prettyJson } from "@/lib/format";
import { CatchWaffles } from "@/components/FrontierViz";
import { E2Cases } from "@/components/E2Cases";
import { TaskGrid } from "@/components/TaskGrid";
import { Code, ErrorBox } from "@/components/ui";

export const dynamic = "force-dynamic";
const description =
  "E1: repair completion of Meta's Muse models on the frozen benchmark tasks, on their own and with ProofForge, under the same caps. E2: seeded bad repairs and correct repairs judged by ordinary checking, by a rebuild with property tests and by ProofForge.";

export const metadata: Metadata = {
  title: "Results, ProofForge",
  description,
  openGraph: { title: "Results, ProofForge", description },
};

const rate = (r: Rate) => `${r.count}/${r.of}`;

// Result sets kept for the record but replaced by a later run; listed collapsed after the current ones.
const SUPERSEDED: Record<string, string> = {
  "e1-dev-1": "Before the harness fixes in commit f8e0e6d; two runs were lost to network timeouts. Replaced by e1-dev-2.",
  "e2-dev-flagship": "Flagship task only, before the complete-proof attacks were added. Replaced by e2-all-1.",
};

// What each current E1 set measures; the test set is listed first.
const E1_SETS: Record<string, string> = {
  "e1-test-1": "The 30 frozen test tasks (ledgers, permissions, queues), never used in development. $3 at list prices and 60 minutes per run.",
  "e1-dev-2": "The 23 development tasks, used to set the test-run caps. $3 at list prices and 45 minutes per run.",
  "e1-test-open-2": "Preregistered: the 30 frozen test tasks with Muse Spark Open after the repair-agent changes made following e1-test-open-1, arms A0 and A1. $3 at list prices and 60 minutes per run. Twelve tasks are scored from their rerun (e1-test-open-2-rerun, meta-models/muse-spark-open), after the provider refused their first runs with HTTP 402; the other 18 ran on meta-models/muse-spark-open-1026.",
  "e1-test-open-2-rerun": "The rerun of e1-test-open-2's twelve tasks whose first runs the provider refused with HTTP 402, both arms, on meta-models/muse-spark-open. These runs replace the refused ones in e1-test-open-2; the other 18 test tasks were not rerun.",
  "e1-test-open-1": "The 30 frozen test tasks with Muse Spark Open, Meta's open-weight model (meta-models/muse-spark-open-1026 on Baseten Model APIs), arms A0 and A1. $3 at list prices and 60 minutes per run.",
  "e1-test-glimmer-1": "Incomplete: the 30 frozen test tasks with Muse Glimmer 30B self-hosted on one Modal H100, arms A0 and A1, stopped when the GPU host paused the workspace after 31 of 60 runs were scored. Three A1 runs counted here were ended by that outage (results/e1-test-glimmer-1/README.md). Dollars are at a GPU-cost price.",
};
const isTest = (key: string) => key.includes("-test-");
const order = (key: string) => (SET_ORDER.includes(key) ? SET_ORDER.indexOf(key) : SET_ORDER.length + Number(!isTest(key)));
const priceWord = (name: string) => (SET_MODEL[name]?.price === "gpu" ? "at the GPU-cost price" : "list");
/** The heatmap tint of a share; any count above zero gets at least a visible tint, and the cell prints the count. */
const pct = (x: number) => `${x > 0 ? Math.max(14, Math.round(x * 1000) / 10) : 0}%`;

function MuseCodeSection({ name, x }: { name: string; x: MuseCodeExperiment }) {
  const tasks = byGain(x.comparisons.filter((c) => c.scope === "task").map(ledgerComparison));
  const verified = x.runs.filter((r) => r.status === "VERIFIED");
  return (
    <section className="rs-set" aria-labelledby={`rs-${name}`}>
      <h3 id={`rs-${name}`}>{name}</h3>
      {tasks.map((c) => (
        <div key={c.id} className="rs-muse-task">
          <p className="rs-muse-name">
            <code>{c.task}</code>
            <span className="muted">, {taskModel(c)} in Muse Code</span>
          </p>
          <div className="strip-rows">
            {(
              [
                ["With ProofForge", c.proofforge, "pf"],
                ["On its own", c.alone, "alone"],
              ] as const
            ).map(([label, arm, k]) => (
              <div key={k} className={`strip-row strip-row-${k}`} role="img" aria-label={`${label}: ${arm.verified} of ${arm.runs} runs verified`}>
                <span className="strip-arm">{label}</span>
                <span className="strip-dots strip-dots-wide" aria-hidden="true">
                  {Array.from({ length: arm.runs }, (_, i) => (
                    <span key={i} className={i < arm.verified ? "sd sd-on" : "sd"} data-unit="run" />
                  ))}
                </span>
                <span className="strip-count">
                  {arm.verified} <span>of {arm.runs}</span>
                </span>
              </div>
            ))}
          </div>
          <p className="small">{resultSentence(c)}</p>
        </div>
      ))}
      {verified.length ? (
        <p className="small rs-muse-passports">
          VERIFIED Passports:{" "}
          {verified.map((r, i) => (
            <span key={r.passport}>
              {i ? ", " : ""}
              <a href={githubFile(r.passport)}>
                <code>{r.passport_sha256.slice(0, 16)}</code>
              </a>
            </span>
          ))}
        </p>
      ) : null}
      <p className="small muted">
        <a href={githubFile(x.readme)}>Results README</a>, <a href={githubFile(x.preregistration)}>preregistration</a>, {x.runs.length} runs
        judged.
      </p>
    </section>
  );
}

export default async function ResultsPage() {
  let data: Record<string, unknown>;
  try {
    data = await getJson<Record<string, unknown>>("/api/results");
  } catch (e) {
    return (
      <main id="main" className="page">
        <h1>Results</h1>
        <ErrorBox title="Could not load results." message={(e as Error).message} />
      </main>
    );
  }
  const entries = Object.entries(data ?? {});
  // In the API's order: the strongest preregistered result first.
  const museCode = entries.filter(([, v]) => isMuseCode(v)) as [string, MuseCodeExperiment][];
  const e1 = (entries.filter(([k, v]) => k.startsWith("e1") && isE1(v)) as [string, E1Summary][]).sort(([a], [b]) => order(a) - order(b));
  const e2 = entries.filter(([k, v]) => k.startsWith("e2") && isE2(v)) as [string, E2Data][];
  const other = entries.filter(([k]) => !e1.some(([x]) => x === k) && !e2.some(([x]) => x === k) && !museCode.some(([x]) => x === k));
  const e1Current = e1.filter(([key]) => !(key in SUPERSEDED));
  const e2Current = e2.filter(([key]) => !(key in SUPERSEDED)).map(([name, d]) => ({ name, d, agg: aggregateE2(d) }));
  const earlier: [string, ReactNode][] = [
    ...e1.filter(([key]) => key in SUPERSEDED).map(([key, s]): [string, ReactNode] => [key, <E1Section key={key} name={key} s={s} level="earlier" />]),
    ...e2.filter(([key]) => key in SUPERSEDED).map(([key, d]): [string, ReactNode] => [key, <E2Section key={key} name={key} d={d} agg={aggregateE2(d)} level="earlier" />]),
  ];
  const kpis = resultsKpis(Object.fromEntries(e1Current), e2Current[0] ? { name: e2Current[0].name, agg: e2Current[0].agg } : null);
  const testGains = e1Current.filter(([k]) => isTest(k));
  const allGain =
    testGains.length > 0 &&
    testGains.every(([, s]) => {
      const a0 = s.arms?.A0;
      return !!a0 && Object.entries(s.arms ?? {}).some(([a, v]) => a !== "A0" && v.completed > a0.completed);
    });

  return (
    <main id="main" className="page results-page">
      <h1>Results</h1>
      <p className="lead">
        {museCode.length
          ? `Muse Code, Meta's coding agent, verified OpenZeppelin Math.sqrt and Compound Proposal 62 with ProofForge in preregistered experiments where it verified neither on its own; every run and its Passport are below. `
          : null}
        {allGain
          ? `On the frozen test tasks, every Meta model measured completed more repairs with ProofForge than on its own, under the same caps. `
          : null}
        E1 measures repair completion per agent arm under identical budgets. E2 measures integrity: the same candidate artifacts are checked by
        ordinary checking, a trusted rebuild with property tests, and ProofForge. Every bad case in this suite is seeded;
        these results do not estimate error rates on repairs in general.
      </p>
      {kpis.length ? (
        <ul className="kpis rs-kpis" aria-label="The results in figures">
          {kpis.map((k) => (
            <li key={k.href + k.label}>
              <a href={k.href}>
                <span className="kpi-v" data-long={k.value.length > 9 ? "" : undefined}>
                  {k.value}
                </span>
                <span className="kpi-l">{k.label}</span>
              </a>
            </li>
          ))}
        </ul>
      ) : null}
      <p className="rs-frontier">
        These sets, and every other comparison of a Meta model on its own against the same model with ProofForge, are classified run by run on{" "}
        <Link href="/frontier">The frontier, measured</Link>.
      </p>
      {entries.length === 0 ? (
        <div className="notice">No result sets have been published yet. They appear here when the evaluation writes results under results/.</div>
      ) : null}

      {museCode.length ? (
        <section aria-labelledby="rs-muse" className="rs-group">
          <h2 id="rs-muse">Muse Code with ProofForge, preregistered</h2>
          <p className="wins-group-lead">
            Muse Spark 1.3 in Muse Code, on its own (Lean only) and with ProofForge (the MCP server, the skill and ProofForgeFin), at the same
            caps. Every final candidate is judged again from the experiment&apos;s frozen commit; every dot is one run, filled when its Passport is
            VERIFIED.
          </p>
          {museCode.map(([key, x]) => (
            <MuseCodeSection key={key} name={key} x={x} />
          ))}
        </section>
      ) : null}

      {e1Current.length ? (
        <section aria-labelledby="rs-e1" className="rs-group">
          <h2 id="rs-e1">E1: repair completion, task by task</h2>
          <p className="wins-group-lead">
            Each task is repaired once per arm, with the same model and the same caps. A repair is completed when the judge accepts the final candidate
            and its rebuilt executable passes 2000 property cases; every cell below is one run, filled when it completed.
          </p>
          <dl className="rs-armkey">
            {Object.entries(ARMS).map(([k, a]) => (
              <div key={k}>
                <dt>
                  {k} {a.name}
                </dt>
                <dd>{a.detail}</dd>
              </div>
            ))}
          </dl>
          {e1Current.map(([key, s]) => (
            <E1Section key={key} name={key} s={s} span={pairSpan(e1Current.map(([, x]) => x))} />
          ))}
          <CostBars sets={e1Current} />
        </section>
      ) : null}

      {e2Current.map(({ name, d, agg }) => (
        <E2Section key={name} name={name} d={d} agg={agg} />
      ))}

      {earlier.length ? (
        <details className="rs-earlier">
          <summary>Earlier runs ({earlier.map(([key]) => key).join(", ")})</summary>
          {earlier.map(([key, node]) => (
            <div key={key}>
              <p className="muted" style={{ marginTop: 16 }}>
                {key}: {SUPERSEDED[key]}
              </p>
              {node}
            </div>
          ))}
        </details>
      ) : null}
      {other.map(([key, v]) => (
        <section key={key}>
          <h2>{key}</h2>
          <Code text={prettyJson(v)} />
        </section>
      ))}
    </main>
  );
}

/** Paired differences in completion rate, each with its 95% interval, on one axis from -span to +span. */
function PairPlot({ pairs, span }: { pairs: [string, NonNullable<E1Summary["pairs"]>[string]][]; span: number }) {
  const x = (v: number) => `${Math.round(((Math.max(-span, Math.min(span, v)) + span) / (2 * span)) * 10000) / 100}%`;
  const sign = (v: number) => (v >= 0 ? `+${v.toFixed(3)}` : v.toFixed(3));
  return (
    <figure className="rs-pairs">
      <figcaption className="rs-pairs-cap">
        Difference in completion rate, paired by task, with its 95% interval (bootstrap over base specifications)
      </figcaption>
      {pairs.map(([k, p]) => {
        const [hi, lo] = k.split("-");
        return (
          <div key={k} className="rs-pair">
            <p className="rs-pair-name">
              {hi} vs {lo}
            </p>
            <div className="rs-pair-track" role="img" aria-label={pairText(k, p)}>
              <span className="rs-pair-zero" style={{ left: "50%" }} />
              {p.ci95_cluster ? (
                <span className="rs-pair-ci" style={{ left: x(p.ci95_cluster[0]), width: `calc(${x(p.ci95_cluster[1])} - ${x(p.ci95_cluster[0])})` }} />
              ) : null}
              <span className="rs-pair-dot" data-sign={p.diff > 0 ? "pos" : p.diff < 0 ? "neg" : "zero"} style={{ left: x(p.diff) }} />
            </div>
            <p className="rs-pair-text">
              <strong>{sign(p.diff)}</strong>
              {p.ci95_cluster ? (
                <span>
                  {" "}
                  [{sign(p.ci95_cluster[0])}, {sign(p.ci95_cluster[1])}]
                </span>
              ) : null}
              {p.discordant ? (
                <span>
                  {hi} only {p.discordant.hi_only}, {lo} only {p.discordant.lo_only}
                </span>
              ) : null}
              {p.mcnemar_p != null ? <span>McNemar p = {p.mcnemar_p.toFixed(4)}</span> : null}
            </p>
          </div>
        );
      })}
      <div className="rs-pair rs-pair-axis" aria-hidden="true">
        <span />
        <div className="rs-pair-ticks">
          {[-span, -span / 2, 0, span / 2, span].map((t) => (
            <span key={t} style={{ left: x(t) }}>
              {t > 0 ? `+${t}` : t}
            </span>
          ))}
        </div>
        <span />
      </div>
    </figure>
  );
}

/** The half-width of the pair axis: the largest difference or interval end, up to the next quarter. */
function pairSpan(sets: E1Summary[]): number {
  const ends = sets.flatMap((s) => Object.values(s.pairs ?? {}).flatMap((p) => [p.diff, ...(p.ci95_cluster ?? [])].map(Math.abs)));
  return Math.max(0.25, Math.ceil(Math.max(0, ...ends) * 4) / 4);
}

function E1Section({ name, s, level = "current", span }: { name: string; s: E1Summary; level?: "current" | "earlier"; span?: number }) {
  const arms = Object.entries(s.arms ?? {});
  const pairs = Object.entries(s.pairs ?? {});
  const fams = Object.entries(s.families ?? {});
  const grid = e1Grid(name, s);
  const lead = e1Lead(name, s);
  const model = SET_MODEL[name]?.model;
  const H = level === "earlier" ? "h4" : "h3";
  return (
    <article className="rs-set" id={name} aria-labelledby={`${name}-h`}>
      <H id={`${name}-h`} className="rs-set-title">
        E1 repair completion: {name}
        {model ? <span className="rs-set-model">{model}</span> : null}
      </H>
      {lead ? <p className="rs-set-lead">{lead}</p> : null}
      {E1_SETS[name] ? <p className="rs-set-desc">{E1_SETS[name]}</p> : s.tasks ? <p className="rs-set-desc">{s.tasks.length} tasks.</p> : null}
      {arms.length ? (
        <dl className="rs-armfigs">
          {arms.map(([arm, a]) => {
            const per = usdPerCompleted(a);
            return (
              <div key={arm} data-arm={arm}>
                <dt>
                  <span className="mono">{arm}</span> {armName(arm)}
                </dt>
                <dd>
                  <span className="rs-armfig-v">
                    {a.completed}
                    <span>/{a.n}</span>
                  </span>
                  <span className="rs-armfig-sub">
                    {a.n ? `${((100 * a.completed) / a.n).toFixed(0)}%` : "none"} completed, {formatUsd(a.usd_list_total)} {priceWord(name)} in total
                    {per != null ? `, ${formatUsd(per)} per completed repair` : ""}
                  </span>
                </dd>
              </div>
            );
          })}
        </dl>
      ) : (
        <p className="muted">No arms recorded.</p>
      )}
      {grid ? (
        <TaskGrid
          name={name}
          grid={grid}
          armNames={Object.fromEntries(Object.keys(ARMS).map((a) => [a, armName(a)]))}
          price={SET_MODEL[name]?.price === "gpu" ? "at the GPU-cost price" : "list"}
        />
      ) : null}
      {grid?.notStarted ? (
        <p className="small muted rs-note">
          {grid.notStarted} of the {grid.families.reduce((n, f) => n + f.tasks.length, 0)} frozen test tasks were never started on either arm before
          the GPU host paused the workspace.
        </p>
      ) : null}
      {pairs.length ? <PairPlot pairs={pairs} span={span ?? pairSpan([s])} /> : null}
      <details className="rs-more">
        <summary>Paired comparisons, per family and per task, as text</summary>
        {pairs.length ? (
          <>
            <h4>Paired comparisons</h4>
            <ul>
              {pairs.map(([k, p]) => (
                <li key={k}>{pairText(k, p)}</li>
              ))}
            </ul>
          </>
        ) : null}
        <h4>Per family</h4>
        {fams.length ? (
          <div className="table-scroll">
            <table>
              <thead>
                <tr>
                  <th>Family</th>
                  {arms.map(([arm]) => (
                    <th key={arm} className="num">
                      {arm}
                    </th>
                  ))}
                </tr>
              </thead>
              <tbody>
                {fams.map(([fam, byArm]) => (
                  <tr key={fam}>
                    <td>{fam}</td>
                    {arms.map(([arm]) => (
                      <td key={arm} className="num">
                        {byArm[arm] ? `${byArm[arm]!.completed}/${byArm[arm]!.n}` : "none"}
                      </td>
                    ))}
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        ) : (
          <p className="muted">The E1 summary from the API does not include a per-family breakdown.</p>
        )}
        <h4>Arms</h4>
        <div className="table-scroll">
          <table>
            <thead>
              <tr>
                <th>Arm</th>
                <th className="num">Completed</th>
                <th className="num">Rate</th>
                <th className="num">List cost, total</th>
              </tr>
            </thead>
            <tbody>
              {arms.map(([arm, a]) => (
                <tr key={arm}>
                  <td className="mono">{arm}</td>
                  <td className="num">
                    {a.completed}/{a.n}
                  </td>
                  <td className="num">{a.n ? `${((100 * a.completed) / a.n).toFixed(0)}%` : "none"}</td>
                  <td className="num">{formatUsd(a.usd_list_total)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        {grid ? (
          <>
            <h4>Per task</h4>
            <div className="table-scroll">
              <table className="small">
                <thead>
                  <tr>
                    <th>Task</th>
                    {grid.arms.map((a) => (
                      <th key={a}>{a}</th>
                    ))}
                  </tr>
                </thead>
                <tbody>
                  {grid.families.flatMap((f) =>
                    f.tasks.map((t) => (
                      <tr key={t.id}>
                        <td className="mono">{t.id}</td>
                        {grid.arms.map((a) => {
                          const c = t.cells[a]!;
                          return (
                            <td key={a}>
                              {c.state === "none"
                                ? "not run"
                                : c.state === "done"
                                  ? "completed"
                                  : `${c.run!.judge?.toLowerCase()}/${c.run!.binary?.toLowerCase()}${c.run!.stop ? ` (${c.run!.stop} stop)` : ""}${c.state === "outage" ? ", outage" : ""}`}
                            </td>
                          );
                        })}
                      </tr>
                    )),
                  )}
                </tbody>
              </table>
            </div>
          </>
        ) : null}
      </details>
    </article>
  );
}

/** List dollars per completed repair, one bar per arm of each list-priced set, on one axis. */
function CostBars({ sets }: { sets: [string, E1Summary][] }) {
  const listed = sets.filter(([k]) => SET_MODEL[k]?.price === "list");
  const gpu = sets.filter(([k]) => SET_MODEL[k]?.price === "gpu");
  const values = listed.flatMap(([, s]) => Object.values(s.arms ?? {}).map((a) => usdPerCompleted(a) ?? 0));
  if (!listed.length) return null;
  const max = Math.ceil(Math.max(...values) * 2) / 2;
  const w = (v: number) => `${Math.round((v / max) * 10000) / 100}%`;
  return (
    <div className="rs-cost" id="e1-cost">
      <h3>List cost per completed repair</h3>
      <p className="wins-group-lead">
        Each arm&apos;s list dollars over its completed repairs, as each set&apos;s e1.md reports it. Shorter is cheaper; every bar is labelled.
      </p>
      <div className="rs-cost-sets">
        {listed.map(([k, s]) => (
          <div key={k} className="rs-cost-set">
            <p className="rs-cost-name">
              <a href={`#${k}`}>{k}</a> <span className="muted">{SET_MODEL[k]!.model}</span>
            </p>
            {Object.entries(s.arms ?? {}).map(([arm, a]) => {
              const v = usdPerCompleted(a);
              return (
                <div key={arm} className="rs-cost-row" data-arm={arm}>
                  <span className="rs-cost-arm">
                    {arm} <span className="muted">{armName(arm)}</span>
                  </span>
                  <span className="rs-cost-track" style={{ backgroundSize: `${w(0.5)} 100%` }}>{v != null ? <span className="rs-cost-bar" style={{ width: w(v) }} /> : null}</span>
                  <span className="rs-cost-v">
                    {v != null ? formatUsd(v) : "none completed"}
                    <span className="muted">
                      {" "}
                      {formatUsd(a.usd_list_total)} for {a.completed}
                    </span>
                  </span>
                </div>
              );
            })}
          </div>
        ))}
      </div>
      <div className="rs-cost-axis" aria-hidden="true">
        <span />
        <span className="rs-cost-ticks">
          {Array.from({ length: max * 2 + 1 }, (_, i) => i / 2).map((t) => (
            <span key={t} style={{ left: w(t) }}>
              ${t.toFixed(2)}
            </span>
          ))}
        </span>
        <span />
      </div>
      {gpu.map(([k, s]) => (
        <p key={k} className="small muted rs-note">
          {k} is priced at a GPU-cost price, not a list price, and is left off this axis:{" "}
          {Object.entries(s.arms ?? {})
            .map(([arm, a]) => {
              const v = usdPerCompleted(a);
              return `${arm} ${v != null ? `${formatUsd(v)} per completed repair (${formatUsd(a.usd_list_total)} for ${a.completed})` : `none completed (${formatUsd(a.usd_list_total)} spent)`}`;
            })
            .join("; ")}
          .
        </p>
      ))}
    </div>
  );
}

const E2_ARMS = ["ordinary", "binary", "proofforge"] as const;

function E2Section({ name, d, agg, level = "current" }: { name: string; d: E2Data; agg: E2Aggregate; level?: "current" | "earlier" }) {
  const arm = (k: (typeof E2_ARMS)[number]) => agg.arms.find((a) => a.arm === k)!;
  const pf = arm("proofforge");
  const ord = arm("ordinary");
  const bin = arm("binary");
  const noneRejected = agg.arms.every((a) => a.falseReject.count === 0);
  const passedTests = d.rows.filter((r) => r.label === "bad" && r.proofforge.binary === "PASS");
  const H = level === "earlier" ? "h3" : "h2";
  const Hs = level === "earlier" ? "h4" : "h3";
  const sameBase = ord.falseAccept.of === bin.falseAccept.of && bin.falseAccept.of === pf.falseAccept.of;
  return (
    <section id={name} aria-labelledby={`${name}-h`} className="rs-group">
      <H id={`${name}-h`}>E2 integrity: {name}</H>
      <p className="rs-set-lead">
        ProofForge accepted {pf.falseAccept.count} of the {pf.falseAccept.of} seeded bad candidates; ordinary checking accepted {ord.falseAccept.count}{" "}
        and the rebuild with property tests {bin.falseAccept.count}.{" "}
        {noneRejected
          ? `None of the three rejected any of the ${pf.falseReject.of} good candidates.`
          : `Good candidates rejected: ${agg.arms.map((a) => `${e2ArmLabels[a.arm]} ${rate(a.falseReject)}`).join(", ")}.`}
      </p>
      {d.generated ? <p className="rs-set-desc">Generated {d.generated}. {d.rows.length} case evaluations; task variants may reuse source artifacts.</p> : null}
      {sameBase && pf.falseAccept.of > 0 ? (
        <>
          <p className="wins-group-lead">Each square is one seeded bad candidate, filled when the check accepted it.</p>
          <CatchWaffles
            e={{
              badCases: ord.falseAccept.of,
              badAccepted: { ordinary: ord.falseAccept.count, rebuildAndTests: bin.falseAccept.count, proofforge: pf.falseAccept.count },
            }}
          />
        </>
      ) : null}
      <Hs className="rs-sub">Bad candidates accepted, by family</Hs>
      <div className="table-scroll rs-heat-wrap">
        <table className="rs-heat">
          <thead>
            <tr>
              <th scope="col">Family</th>
              {E2_ARMS.map((a) => (
                <th key={a} scope="col" className="num">
                  {e2ArmLabels[a]}
                </th>
              ))}
            </tr>
          </thead>
          <tbody>
            {agg.families.map((f) => (
              <tr key={f.family}>
                <th scope="row">{f.family}</th>
                {E2_ARMS.map((a) => {
                  const r = f.arms[a].falseAccept;
                  const share = r.of ? r.count / r.of : 0;
                  return (
                    <td
                      key={a}
                      className="num rs-heat-cell"
                      data-strong={share >= 0.5 ? "" : undefined}
                      data-zero={r.count === 0 ? "" : undefined}
                      style={{ "--p": pct(share) } as CSSProperties}
                    >
                      {rate(r)}
                    </td>
                  );
                })}
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      {passedTests.length ? (
        <p className="small muted rs-note">
          Bad {passedTests.length === 1 ? "candidate" : "candidates"} the rebuild with property tests accepted:{" "}
          {passedTests.map((r, i) => (
            <span key={`${r.task}${r.case}`}>
              {i ? "; " : ""}
              <code>{r.task}</code> <code>{r.case}</code>
              {r.note ? `, ${r.note}` : ""}
              {r.proofforge.accepted ? "" : ", rejected by ProofForge"}
            </span>
          ))}
          .
        </p>
      ) : null}
      <details className="rs-more">
        <summary>False acceptances and false rejections, per arm and per family</summary>
        <div className="table-scroll">
          <table>
            <thead>
              <tr>
                <th>Arm</th>
                <th className="num">Bad cases accepted (false acceptances)</th>
                <th className="num">Good cases rejected (false rejections)</th>
              </tr>
            </thead>
            <tbody>
              {agg.arms.map((a) => (
                <tr key={a.arm}>
                  <td>{e2ArmLabels[a.arm]}</td>
                  <td className="num">
                    {rate(a.falseAccept)}
                    <Meter r={a.falseAccept} />
                  </td>
                  <td className="num">
                    {rate(a.falseReject)}
                    <Meter r={a.falseReject} />
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <h4>Per family</h4>
        <div className="table-scroll">
          <table>
            <thead>
              <tr>
                <th>Family</th>
                <th className="num">Ordinary false acceptances</th>
                <th className="num">Ordinary false rejections</th>
                <th className="num">Rebuild/tests false acceptances</th>
                <th className="num">Rebuild/tests false rejections</th>
                <th className="num">ProofForge false acceptances</th>
                <th className="num">ProofForge false rejections</th>
              </tr>
            </thead>
            <tbody>
              {agg.families.map((f) => (
                <tr key={f.family}>
                  <td>{f.family}</td>
                  <td className="num">{rate(f.arms.ordinary.falseAccept)}</td>
                  <td className="num">{rate(f.arms.ordinary.falseReject)}</td>
                  <td className="num">{rate(f.arms.binary.falseAccept)}</td>
                  <td className="num">{rate(f.arms.binary.falseReject)}</td>
                  <td className="num">{rate(f.arms.proofforge.falseAccept)}</td>
                  <td className="num">{rate(f.arms.proofforge.falseReject)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </details>
      <E2Cases name={name} count={d.rows.length} />
    </section>
  );
}

/** A proportion bar beside a count; the count stays the primary signal. */
function Meter({ r }: { r: Rate }) {
  const pct = r.of ? (100 * r.count) / r.of : 0;
  return (
    <span className="meter" aria-hidden="true">
      <span style={{ width: `${pct}%` }} />
    </span>
  );
}
