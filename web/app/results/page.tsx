import type { Metadata } from "next";
import type { ReactNode } from "react";
import { getJson } from "@/lib/api";
import { aggregateE2, e2ArmLabels, isE1, isE2, pairText, type E1Summary, type E2Data, type Rate } from "@/lib/results";
import { formatUsd, prettyJson, shortHash } from "@/lib/format";
import { Code, ErrorBox, Status } from "@/components/ui";

export const dynamic = "force-dynamic";
export const metadata: Metadata = { title: "Results, ProofForge" };

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
};
const isTest = (key: string) => key.includes("-test-");

export default async function ResultsPage() {
  let data: Record<string, unknown>;
  try {
    data = await getJson<Record<string, unknown>>("/api/results");
  } catch (e) {
    return (
      <main className="page">
        <h1>Results</h1>
        <ErrorBox title="Could not load results." message={(e as Error).message} />
      </main>
    );
  }
  const entries = Object.entries(data ?? {});
  const e1 = (entries.filter(([k, v]) => k.startsWith("e1") && isE1(v)) as [string, E1Summary][]).sort(
    ([a], [b]) => Number(isTest(b)) - Number(isTest(a)),
  );
  const e2 = entries.filter(([k, v]) => k.startsWith("e2") && isE2(v)) as [string, E2Data][];
  const other = entries.filter(([k]) => !e1.some(([x]) => x === k) && !e2.some(([x]) => x === k));
  const earlier: [string, ReactNode][] = [
    ...e1.filter(([key]) => key in SUPERSEDED).map(([key, s]): [string, ReactNode] => [key, <E1Section key={key} name={key} s={s} />]),
    ...e2.filter(([key]) => key in SUPERSEDED).map(([key, d]): [string, ReactNode] => [key, <E2Section key={key} name={key} d={d} />]),
  ];

  return (
    <main className="page">
      <h1>Results</h1>
      <p className="lead">
        E1 measures repair completion per agent arm under identical budgets. E2 measures integrity: the same candidate artifacts are checked by
        ordinary checking, a trusted rebuild with property tests, and ProofForge. Every bad case in this suite is seeded;
        these results do not estimate error rates on repairs in general.
      </p>
      {entries.length === 0 ? (
        <div className="notice">No result sets have been published yet. They appear here when the evaluation writes results under results/.</div>
      ) : null}

      {e1
        .filter(([key]) => !(key in SUPERSEDED))
        .map(([key, s]) => (
          <E1Section key={key} name={key} s={s} />
        ))}
      {e2
        .filter(([key]) => !(key in SUPERSEDED))
        .map(([key, d]) => (
          <E2Section key={key} name={key} d={d} />
        ))}
      {earlier.length ? (
        <details style={{ marginTop: 24 }}>
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

function E1Section({ name, s }: { name: string; s: E1Summary }) {
  const arms = Object.entries(s.arms ?? {});
  const pairs = Object.entries(s.pairs ?? {});
  const fams = Object.entries(s.families ?? {});
  return (
    <section>
      <h2>E1 repair completion: {name}</h2>
      {E1_SETS[name] ? <p className="muted">{E1_SETS[name]}</p> : s.tasks ? <p className="muted">{s.tasks.length} tasks.</p> : null}
      {arms.length ? (
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
      ) : (
        <p className="muted">No arms recorded.</p>
      )}
      {pairs.length ? (
        <>
          <h3 style={{ marginTop: 16 }}>Paired comparisons</h3>
          <ul>
            {pairs.map(([k, p]) => (
              <li key={k}>{pairText(k, p)}</li>
            ))}
          </ul>
        </>
      ) : null}
      <h3 style={{ marginTop: 16 }}>Per family</h3>
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
    </section>
  );
}

function E2Section({ name, d }: { name: string; d: E2Data }) {
  const agg = aggregateE2(d);
  return (
    <section>
      <h2>E2 integrity: {name}</h2>
      {d.generated ? <p className="muted">Generated {d.generated}. {d.rows.length} case evaluations; task variants may reuse source artifacts.</p> : null}
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
      <h3 style={{ marginTop: 16 }}>Per family</h3>
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
      <details style={{ marginTop: 12 }}>
        <summary>All cases</summary>
        <div className="table-scroll">
          <table className="small">
            <thead>
              <tr>
                <th>Task</th>
                <th>Case</th>
                <th>Label</th>
                <th>Ordinary</th>
                <th>Rebuild and tests</th>
                <th>ProofForge</th>
                <th>ProofForge reason</th>
              </tr>
            </thead>
            <tbody>
              {d.rows.map((r, i) => (
                <tr key={i}>
                  <td className="mono">{r.task}</td>
                  <td>
                    <span className="mono">{r.case}</span>
                    {r.note ? <div className="muted">{r.note}</div> : null}
                    {r.sha256 ? <div className="muted hash">{shortHash(r.sha256)}</div> : null}
                  </td>
                  <td>{r.label}</td>
                  <td>
                    <Status value={r.ordinary.accepted === (r.label === "good") ? "PASS" : "REFUTED"}>
                      {r.ordinary.accepted ? "accept" : "reject"}
                    </Status>
                  </td>
                  <td>{r.proofforge.binary === undefined ? "not recorded" : r.proofforge.binary === "PASS" ? "accept" : "reject"}</td>
                  <td>
                    <Status value={r.proofforge.accepted === (r.label === "good") ? "PASS" : "REFUTED"}>
                      {r.proofforge.accepted ? "accept" : "reject"}
                    </Status>
                  </td>
                  <td className="mono">{r.proofforge.reason || "none"}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <p className="small muted">Green marks a correct decision; red marks a wrong one (a bad case accepted or a good case rejected).</p>
      </details>
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
