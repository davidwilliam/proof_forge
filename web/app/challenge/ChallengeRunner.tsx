"use client";

import { useEffect, useRef, useState } from "react";
import { postJson, type ChallengeResult } from "@/lib/api";
import { formatMs, prettyJson, shortHash } from "@/lib/format";
import { TARGET_MS, balanceRows, payoutWitness, type ChallengeVariant, type PayoutWitness } from "@/lib/challenge";
import { Code, ErrorBox, Status } from "@/components/ui";
import { Ticked } from "@/components/Ticked";

interface Run {
  result: ChallengeResult;
  roundTrip: number;
}

type Stage = "idle" | "running" | "done" | "refuted" | "clear" | "none";

/** Position on the 0 to 20 s gauge, in percent, rounded for a stable render. */
const pct = (ms: number) => Math.round(Math.min(100, Math.max(0, (ms / TARGET_MS) * 100)) * 100) / 100;

function VariantCards({
  variants,
  meta,
  value,
  onPick,
  runs,
  disabled,
}: {
  variants: string[];
  meta: ChallengeVariant[];
  value: string;
  onPick: (v: string) => void;
  runs: Record<string, Run>;
  disabled: boolean;
}) {
  const refs = useRef<(HTMLButtonElement | null)[]>([]);
  const move = (i: number, d: number) => {
    const j = (i + d + variants.length) % variants.length;
    onPick(variants[j]!);
    refs.current[j]?.focus();
  };
  return (
    <div className="ch-cards" role="radiogroup" aria-label="Variant">
      {variants.map((v, i) => {
        const m = meta.find((x) => x.id === v);
        const run = runs[v];
        const broken = new Set(Object.entries(run?.result.violations ?? {}).filter(([, n]) => n > 0).map(([k]) => k));
        const checked = v === value;
        return (
          <button
            key={v}
            ref={(el) => {
              refs.current[i] = el;
            }}
            type="button"
            role="radio"
            aria-checked={checked}
            tabIndex={checked ? 0 : -1}
            className="ch-card"
            disabled={disabled && !checked}
            onClick={() => onPick(v)}
            onKeyDown={(e) => {
              if (e.key === "ArrowRight" || e.key === "ArrowDown") (e.preventDefault(), move(i, 1));
              if (e.key === "ArrowLeft" || e.key === "ArrowUp") (e.preventDefault(), move(i, -1));
            }}
          >
            <span className="ch-card-top">
              <span className="ch-card-id mono">{v}</span>
              <span className="ch-card-check" aria-hidden="true" />
            </span>
            <span className="ch-card-meta">
              {m ? (
                <>
                  {m.family} family, <code>
                    {m.lib}.{m.definitions.join(", ")}
                  </code>{" "}
                  under repair, executable <code>{m.exe}</code>
                </>
              ) : (
                "Hidden payout variant"
              )}
            </span>
            {m ? (
              <span className="ch-card-reqs" aria-hidden="true">
                {m.requirements.map((r) => (
                  <span key={r} className={broken.has(r) ? "ch-rq ch-rq-bad" : run ? "ch-rq ch-rq-seen" : "ch-rq"} title={r} />
                ))}
              </span>
            ) : null}
            <span className="ch-card-foot">
              {run ? (
                <>
                  <Status value={run.result.status} /> <span className="mono">{formatMs(run.result.elapsed_ms)}</span>
                  {broken.size ? <span className="ch-card-note">{[...broken].join(", ")}</span> : null}
                </>
              ) : (
                <span className="ch-card-note">
                  {m ? `${m.requirements.length} locked requirements. ` : ""}The bug and its issue report stay hidden until you check it.
                </span>
              )}
            </span>
          </button>
        );
      })}
    </div>
  );
}

function StageMark({ s, n }: { s: Stage; n: number }) {
  const text = { idle: String(n), running: String(n), done: "✓", refuted: "!", clear: "✓", none: "–" }[s];
  return (
    <span className="ch-stage-mark" aria-hidden="true">
      {text}
    </span>
  );
}

function PipelineView({ busy, run, propertyCases }: { busy: boolean; run: Run | null; propertyCases: number }) {
  const r = run?.result ?? null;
  const violations = Object.entries(r?.violations ?? {}).filter(([, n]) => n > 0);
  const s1: Stage = busy ? "running" : r ? "done" : "idle";
  const s2: Stage = busy ? "running" : r ? (violations.length ? "refuted" : "clear") : "idle";
  const s3: Stage = busy ? "running" : r ? (r.witness ? "refuted" : "none") : "idle";
  const stages = [
    {
      s: s1,
      title: "Build the executable",
      body: "From the variant's Lean source, once, cached by its hash.",
      out: r ? (
        <>
          sha256 <span className="hash">{shortHash(r.executable_sha256, 16)}</span>
        </>
      ) : null,
    },
    {
      s: s2,
      title: `Run ${propertyCases} property cases`,
      body: "Generated inputs; an independent model checks every output against the locked requirements.",
      out: r ? (violations.length ? `Violations in ${violations.length} of the locked requirements` : "No violation found") : null,
    },
    {
      s: s3,
      title: "Return the witness",
      body: "The first input and output that break a locked requirement.",
      out: r ? (r.witness ? <span className="mono">{r.witness.requirement}</span> : "No witness: UNRESOLVED") : null,
    },
  ];
  return (
    <ol className={`ch-pipe${busy ? " ch-pipe-busy" : ""}`} aria-label="What the check does">
      {stages.map((st, i) => (
        <li key={st.title} className="ch-stage" data-state={st.s}>
          <StageMark s={st.s} n={i + 1} />
          <div className="ch-stage-text">
            <strong>{st.title}</strong>
            <span className="ch-stage-body">{st.body}</span>
            <span className="ch-stage-out" aria-live="polite">
              {st.out ?? (busy ? "Running" : "Waiting for a run")}
            </span>
          </div>
        </li>
      ))}
    </ol>
  );
}

function Gauge({ ms, roundTrip }: { ms: number; roundTrip: number | null }) {
  const p = pct(ms);
  return (
    <div className="ch-gauge" role="img" aria-label={`Check time ${formatMs(ms)} on a scale from 0 to the ${TARGET_MS / 1000} s target`}>
      <div className="ch-gauge-head">
        <span className="ch-gauge-big">{formatMs(ms)}</span>
        <span className="ch-gauge-alt">
          check time, {p < 1 ? "under 1%" : `${Math.round(p)}%`} of the {TARGET_MS / 1000} s target
          {roundTrip != null ? `; ${formatMs(roundTrip)} round trip from this browser` : ""}
        </span>
      </div>
      <div className="ch-gauge-track">
        <span className="ch-gauge-fill" style={{ width: `max(${p}%, 4px)` }} />
      </div>
      <div className="ch-gauge-scale" aria-hidden="true">
        <span>0 s</span>
        <span>10 s</span>
        <span>{TARGET_MS / 1000} s target</span>
      </div>
    </div>
  );
}

function RequirementMap({ ids, texts, run }: { ids: string[]; texts: Record<string, string>; run: Run | null }) {
  const v = run?.result.violations ?? {};
  const w = run?.result.witness?.requirement;
  return (
    <ul className="ch-reqs" aria-label="The locked requirements">
      {ids.map((id) => {
        const n = v[id] ?? 0;
        const state = !run ? "idle" : n > 0 ? "bad" : "seen";
        return (
          <li key={id} className="ch-req" data-state={state} data-witness={w === id ? "" : undefined}>
            <span className="ch-req-head">
              <code>{id}</code>
              {!run ? null : n > 0 ? <Status value="REFUTED">{`${n} violations`}</Status> : <span className="ch-req-none">no violation in this run</span>}
            </span>
            <span className="ch-req-text">
              <Ticked text={texts[id] || "No requirement text available."} />
            </span>
          </li>
        );
      })}
    </ul>
  );
}

function Balances({ w }: { w: PayoutWitness }) {
  const rows = balanceRows(w);
  const q = w.request;
  return (
    <div className="ch-pay">
      <p className="ch-pay-req">
        Payout <span className="mono">tx {q.txId}</span>: requester <span className="mono">{q.requester}</span> pays{" "}
        <span className="mono">{q.amount}</span> from account <span className="mono">{q.source}</span> to{" "}
        <span className="mono">{q.recipients.join(", ")}</span>. Outcome: <strong>{w.outcome}</strong>.
      </p>
      <div className="table-scroll">
        <table className="ch-pay-table">
          <caption className="small muted">Balances before the request and in the state the executable returned</caption>
          <thead>
            <tr>
              <th scope="col">Account</th>
              <th scope="col" className="num">
                Before
              </th>
              <th scope="col" className="num">
                After
              </th>
              <th scope="col" className="num">
                Change
              </th>
            </tr>
          </thead>
          <tbody>
            {rows.map((r) => (
              <tr key={r.account} data-changed={r.delta ? "" : undefined}>
                <th scope="row">
                  <span className="mono">{r.account}</span> {r.role ? <span className="ch-role">{r.role}</span> : null}
                </th>
                <td className="num">{r.before ?? "none"}</td>
                <td className="num">{r.after ?? "none"}</td>
                <td className="num ch-delta">{r.delta == null ? "" : r.delta === 0 ? "0" : r.delta > 0 ? `+${r.delta}` : `${r.delta}`}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p className="ch-pay-ids small">
        Applied transaction IDs: <span className="mono">[{w.state.applied.join(", ")}]</span> before,{" "}
        <span className="mono">{w.after ? `[${w.after.applied.join(", ")}]` : "none"}</span> after. Authorizations: {w.state.auth.length} {w.state.auth.length === 1 ? "pair" : "pairs"}.
      </p>
    </div>
  );
}

export function ChallengeRunner({
  variants,
  requirementTexts,
  meta = [],
  propertyCases = 300,
}: {
  variants: string[];
  requirementTexts: Record<string, string>;
  meta?: ChallengeVariant[];
  propertyCases?: number;
}) {
  const [variant, setVariant] = useState(variants[0] ?? "");
  const [busy, setBusy] = useState(false);
  const [runs, setRuns] = useState<Record<string, Run>>({});
  const [error, setError] = useState<string | null>(null);
  const [tick, setTick] = useState(0);
  const t0 = useRef(0);

  useEffect(() => {
    if (!busy) return;
    const t = setInterval(() => setTick(performance.now() - t0.current), 100);
    return () => clearInterval(t);
  }, [busy]);

  const run = async () => {
    setBusy(true);
    setError(null);
    setRuns(({ [variant]: _, ...rest }) => rest);
    t0.current = performance.now();
    setTick(0);
    try {
      // repair stays false: this page only runs the binary check, never a model session.
      const r = await postJson<ChallengeResult>("/api/challenge", { variant, repair: false });
      const roundTrip = performance.now() - t0.current;
      setRuns((all) => ({ ...all, [r.variant || variant]: { result: r, roundTrip } }));
    } catch (e) {
      setError((e as Error).message);
    } finally {
      setBusy(false);
    }
  };

  if (!variants.length) return <div className="notice">No hidden variants are available on this server.</div>;

  const current = runs[variant] ?? null;
  const result = current?.result ?? null;
  const roundTrip = current?.roundTrip ?? null;
  const w = result?.witness ?? null;
  const elapsed = result?.elapsed_ms ?? null;
  const within = elapsed != null ? elapsed <= TARGET_MS : null;
  const violations = Object.entries(result?.violations ?? {}).filter(([, n]) => n > 0);
  const reqIds = meta.find((m) => m.id === variant)?.requirements ?? Object.keys(requirementTexts);
  const issue = meta.find((m) => m.id === variant)?.issue ?? null;
  const pw = w ? payoutWitness(w.input, w.output) : null;

  return (
    <div className="ch-runner">
      <VariantCards variants={variants} meta={meta} value={variant} onPick={setVariant} runs={runs} disabled={busy} />

      <div className="ch-runbar">
        <button className="primary ch-run" onClick={run} disabled={busy || !variant}>
          {busy ? "Checking" : "Run check"}
        </button>
        <span className="ch-runbar-text">
          {busy ? (
            <span className="mono">{(tick / 1000).toFixed(1)} s of 20 s target</span>
          ) : (
            <>
              Checks <span className="mono">{variant}</span> on the live API, without a model session.
            </>
          )}
        </span>
      </div>

      <PipelineView busy={busy} run={busy ? null : current} propertyCases={propertyCases} />

      {error ? <ErrorBox title="Challenge failed" message={error} /> : null}

      {result ? (
        <div className="ch-result" data-status={result.status}>
          <div className="card ch-verdict">
            <p className="ch-verdict-line">
              {result.label}: variant <span className="mono">{result.variant}</span> is <Status value={result.status} />
            </p>
            {elapsed != null ? <Gauge ms={elapsed} roundTrip={roundTrip} /> : null}
            <dl className="kv ch-kv">
              <dt>Check time</dt>
              <dd>
                {formatMs(elapsed)} against the 20 s target:{" "}
                {within ? <Status value="PASS">within target</Status> : <Status value="UNRESOLVED">over target</Status>}
              </dd>
              {roundTrip != null ? (
                <>
                  <dt>Round trip</dt>
                  <dd>{formatMs(roundTrip)} including the request</dd>
                </>
              ) : null}
              <dt>Executable sha256</dt>
              <dd className="hash">{shortHash(result.executable_sha256, 16)}</dd>
              <dt>Violations</dt>
              <dd>{violations.length ? violations.map(([k, n]) => `${k} in ${n} cases`).join(", ") : "none found"}</dd>
            </dl>
          </div>

          {issue ? (
            <details className="card ch-issue" key={variant}>
              <summary>Show the bug this variant hides</summary>
              <p className="ch-issue-text">
                Issue report of <span className="mono">{variant}</span>: {issue}
              </p>
              <p className="small muted">The check above was run without it, from the locked requirements alone.</p>
            </details>
          ) : null}

          {w ? (
            <div className="card ch-witness">
              <h2>
                Violated requirement <span className="mono">{w.requirement}</span>
              </h2>
              <p className="ch-witness-req">
                <Ticked text={requirementTexts[w.requirement] || "No requirement text available."} />
              </p>
              <p className="ch-witness-msg">
                Witness: <strong>{w.message}</strong>
              </p>
              {pw ? <Balances w={pw} /> : null}
              <details className="ch-json" open={!pw}>
                <summary>Input and output as JSON</summary>
                <div className="split-results">
                  <div>
                    <h3>Input</h3>
                    <Code text={prettyJson(w.input)} />
                  </div>
                  <div>
                    <h3>Output of the variant&apos;s executable</h3>
                    <Code text={prettyJson(w.output)} />
                  </div>
                </div>
              </details>
            </div>
          ) : (
            <div className="notice">
              No witness was found in this run, so the variant is UNRESOLVED: the tests did not refute it, and nothing has been proved about it.
            </div>
          )}
        </div>
      ) : (
        <div className="ch-await" aria-live="polite">
          <p className="ch-await-text">
            {busy
              ? "Running the property cases. The witness appears here: the input, the variant's output and the locked requirement it breaks."
              : "The witness appears here after a run: the input, the variant's output and the locked requirement it breaks, timed against the 20 s target."}
          </p>
        </div>
      )}

      <div className="ch-reqs-wrap">
        <h3 className="ch-reqs-title">
          The {reqIds.length} locked requirements of <span className="mono">{variant}</span>
          {result ? ", as this run left them" : ""}
        </h3>
        <RequirementMap ids={reqIds} texts={requirementTexts} run={current} />
      </div>
    </div>
  );
}
