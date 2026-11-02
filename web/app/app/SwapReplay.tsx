"use client";

import { useEffect, useId, useRef, useState } from "react";
import { postJson } from "@/lib/api";
import { formatMs, shortHash } from "@/lib/format";
import {
  LIMITS,
  PRESETS,
  batchFromFields,
  describeSwap,
  fieldsFromBatch,
  formatBig,
  formatPct,
  outcome,
  pct,
  valueSeries,
  versionInfo,
  type BatchFields,
  type SwapBatch,
  type SwapResponse,
  type SwapResultOut,
  type SwapVersionOut,
} from "@/lib/swap";
import { Seal } from "@/components/Seal";
import { ErrorBox, Status } from "@/components/ui";
import { ValueChart, type StepState } from "./ValueChart";

interface Run {
  response: SwapResponse;
  batch: SwapBatch;
  tokens: [string, string];
  title: string;
}

const DEFAULT = PRESETS[0]!;

export function SwapReplay() {
  const [presetKey, setPresetKey] = useState<string>(DEFAULT.key);
  const [fields, setFields] = useState<BatchFields>(fieldsFromBatch(DEFAULT.batch));
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [run, setRun] = useState<Run | null>(null);
  const started = useRef(false);

  const preset = PRESETS.find((p) => p.key === presetKey);
  const tokens: [string, string] = preset?.tokens ?? ["token 0", "token 1"];
  const checked = batchFromFields(fields);

  const go = async (batch: SwapBatch, title: string, toks: [string, string]) => {
    setBusy(true);
    setError(null);
    try {
      const response = await postJson<SwapResponse>("/api/swap", batch);
      setRun({ response, batch, tokens: toks, title });
    } catch (e) {
      setError((e as Error).message);
    } finally {
      setBusy(false);
    }
  };

  useEffect(() => {
    if (started.current) return;
    started.current = true;
    void go(DEFAULT.batch, DEFAULT.title, DEFAULT.tokens);
  }, []);

  const pick = (key: string) => {
    const p = PRESETS.find((x) => x.key === key)!;
    setPresetKey(key);
    setFields(fieldsFromBatch(p.batch));
    void go(p.batch, p.title, p.tokens);
  };

  const edit = (patch: Partial<BatchFields>) => {
    setFields((f) => ({ ...f, ...patch }));
    if (preset) setPresetKey(`${preset.key}:edited`);
  };
  const editedFrom = presetKey.endsWith(":edited") ? PRESETS.find((p) => `${p.key}:edited` === presetKey) : null;
  const shownPreset = preset ?? editedFrom ?? null;

  return (
    <div>
      <div className="presets" role="group" aria-label="Preset batches">
        {PRESETS.map((p) => (
          <button key={p.key} aria-pressed={presetKey === p.key} onClick={() => pick(p.key)} disabled={busy}>
            {p.title}
          </button>
        ))}
      </div>
      {shownPreset ? (
        <p className="preset-summary">
          {editedFrom ? "Edited from: " : null}
          {shownPreset.summary}
        </p>
      ) : null}

      <details className="editor">
        <summary>Edit the batch</summary>
        <div className="editor-grid">
          <label>
            Pool math
            <select value={fields.math} onChange={(e) => edit({ math: e.target.value as BatchFields["math"] })}>
              <option value="product">constant product (proved to meet the contract)</option>
              <option value="stable">StableMath port (tested)</option>
            </select>
          </label>
          {fields.math === "stable" ? (
            <label>
              Amplification times 1000
              <input value={fields.amp} inputMode="numeric" onChange={(e) => edit({ amp: e.target.value })} />
            </label>
          ) : null}
          {[0, 1].map((i) => (
            <label key={`b${i}`}>
              Balance of token {i} ({tokens[i]}), wei
              <input
                value={fields.balances[i]}
                inputMode="numeric"
                onChange={(e) => edit({ balances: (i === 0 ? [e.target.value, fields.balances[1]] : [fields.balances[0], e.target.value]) as [string, string] })}
              />
            </label>
          ))}
          {[0, 1].map((i) => (
            <label key={`r${i}`}>
              Scaling factor of token {i}, 1e18 is 1.0
              <input
                value={fields.rates[i]}
                inputMode="numeric"
                onChange={(e) => edit({ rates: (i === 0 ? [e.target.value, fields.rates[1]] : [fields.rates[0], e.target.value]) as [string, string] })}
              />
            </label>
          ))}
          <label>
            Swap fee, 1e18 is 100%
            <input value={fields.fee} inputMode="numeric" onChange={(e) => edit({ fee: e.target.value })} />
          </label>
        </div>
        <label className="small muted" htmlFor="swaps" style={{ display: "block", margin: "14px 0 6px" }}>
          Swaps, one per line: kind (out for an exact amount out, in for an exact amount in), token in, token out, amount in wei. For example{" "}
          <code>out 0 1 17</code> takes 17 wei of token 1 out, paid in token 0. At most {LIMITS.swaps} swaps; amounts up to 10^30.
        </label>
        <textarea id="swaps" value={fields.swaps} spellCheck={false} onChange={(e) => edit({ swaps: e.target.value })} aria-invalid={!checked.ok} />
        {!checked.ok ? (
          <p role="status" style={{ color: "var(--bad)", margin: "6px 0 0" }}>
            {checked.error}
          </p>
        ) : null}
      </details>

      <div className="run-row">
        <button
          className="primary"
          disabled={!checked.ok || busy}
          onClick={() => checked.ok && go(checked.value, shownPreset ? `${shownPreset.title}${editedFrom ? ", edited" : ""}` : "Edited batch", tokens)}
        >
          {busy ? "Running on all three" : "Run on all three"}
        </button>
        <span className="small muted">Each run starts the three executables on the server; the first request after a restart can take longer.</span>
      </div>

      {error ? (
        <ErrorBox title="The replay did not run" message={error}>
          <p className="small" style={{ margin: "6px 0 0" }}>
            The figures on the version cards come from the committed Passports and do not depend on this request.
          </p>
        </ErrorBox>
      ) : null}
      {run ? <Results run={run} /> : busy ? <p className="muted">Running the batch on all three versions.</p> : null}
    </div>
  );
}

const SERIES_COLOR = (k: string) => `var(--series-${k})`;
/** Drawing order: the dashed plus-one line last, on top of the Muse repair it often overlaps. */
const ORDER = ["deployed", "repaired", "plus_one"];
/** Rows of the swap table shown before "Show all". */
const PREVIEW = 5;

/** What happened to each swap of the batch in one version. */
function stepStates(r: SwapResultOut, n: number): StepState[] {
  return Array.from({ length: n }, (_, k) => {
    const s = r.steps[k];
    if (!s) return "skipped";
    if (!s.ok) return "refused";
    return r.ok ? "kept" : "undone";
  });
}

/** The pool's value after the batch in percent of the start; the start when the batch reverted. */
function endPct(r: SwapResultOut): number | null {
  const o = outcome(r);
  return o.after != null && o.before ? pct(o.after, o.before) : null;
}

function Results({ run }: { run: Run }) {
  const { response, batch, tokens } = run;
  const n = batch.swaps.length;
  const repaired = response.versions.find((v) => v.version === "repaired") ?? null;
  const labels = batch.swaps.map((s) => describeSwap(s, tokens));
  const showChart = response.versions.some((v) => v.result.steps.length >= 3);
  const [all, setAll] = useState(false);
  const shown = all ? n : Math.min(n, PREVIEW);
  const tableId = useId();
  const scale = Math.max(100, ...response.versions.map((v) => endPct(v.result) ?? 0));
  return (
    <div aria-live="polite">
      <p className="small muted" style={{ marginTop: 0 }}>
        Result of: {run.title}. {n} {n === 1 ? "swap" : "swaps"}, {batch.math === "product" ? "constant-product math" : `StableMath, amplification ${Number(batch.amp) / 1000}`}, pool of{" "}
        {formatBig(batch.pool.balances[0])} {tokens[0]} and {formatBig(batch.pool.balances[1])} {tokens[1]} wei. Server time {formatMs(response.elapsed_ms)}.
      </p>
      <div className="outcomes">
        {response.versions.map((v) => (
          <OutcomeCard key={v.version} v={v} repaired={v.version === "repaired" ? null : repaired} batch={batch} tokens={tokens} scale={scale} />
        ))}
      </div>

      {showChart ? (
        <div className="card chart">
          <h3>Pool value after each swap, in percent of the start</h3>
          <div className="chart-legend">
            {response.versions.map((v) => (
              <span key={v.version}>
                <i className="legend-line" data-dash={v.version === "plus_one"} style={{ ["--swatch" as string]: SERIES_COLOR(v.version) }} />
                {versionInfo(v.version).short}
              </span>
            ))}
            <span className="muted">A line that stops early hit a refused swap; the whole batch then reverts.</span>
          </div>
          <ValueChart
            stepLabels={labels}
            stepKinds={batch.swaps.map((s) => s.kind)}
            series={[...response.versions]
              .sort((a, b) => ORDER.indexOf(a.version) - ORDER.indexOf(b.version))
              .map((v) => {
                const o = outcome(v.result);
                return {
                  key: v.version,
                  label: versionInfo(v.version).short,
                  color: SERIES_COLOR(v.version),
                  dashed: v.version === "plus_one",
                  values: valueSeries(v.result, n),
                  states: stepStates(v.result, n),
                  quotes: Array.from({ length: n }, (_, k) => (v.result.steps[k]?.ok ? (v.result.steps[k]!.quote ?? null) : null)),
                  final: endPct(v.result),
                  refusedAt: o.ok ? null : o.refusedAt,
                };
              })}
          />
          <ul className="strip-legend" aria-label="The strip under the chart, one row per version">
            <li>
              <span className="sl sl-kept" aria-hidden="true" /> went through
            </li>
            <li>
              <span className="sl sl-undone" aria-hidden="true" /> went through, undone when the batch reverted
            </li>
            <li>
              <span className="sl sl-refused" aria-hidden="true" /> refused
            </li>
            <li>
              <span className="sl sl-skipped" aria-hidden="true" /> not run
            </li>
          </ul>
        </div>
      ) : null}

      <div className="steps">
        <h3>Every swap</h3>
        <p className="small muted">Each cell is the amount the version charged (for an exact amount out) or paid (for an exact amount in), in wei, and below it the pool&apos;s value in percent of the start.</p>
        <div className="table-scroll" id={tableId}>
          <table className="small">
            <thead>
              <tr>
                <th className="num">Swap</th>
                <th>Request</th>
                {response.versions.map((v) => (
                  <th key={v.version} className="num">
                    {versionInfo(v.version).short}
                  </th>
                ))}
              </tr>
            </thead>
            <tbody>
              {batch.swaps.slice(0, shown).map((s, i) => (
                <tr key={i}>
                  <td className="num">{i + 1}</td>
                  <td>{labels[i]}</td>
                  {response.versions.map((v) => (
                    <StepCell key={v.version} r={v.result} i={i} />
                  ))}
                </tr>
              ))}
              {shown < n ? (
                <tr className="steps-more-row">
                  <td colSpan={2 + response.versions.length}>
                    {n - shown} more {n - shown === 1 ? "swap" : "swaps"}, shown with the button below
                  </td>
                </tr>
              ) : null}
              <tr>
                <th className="num">Batch</th>
                <th>Value after the batch</th>
                {response.versions.map((v) => {
                  const o = outcome(v.result);
                  return (
                    <th key={v.version} className="num">
                      {o.ok ? formatPct(o.after != null && o.before ? pct(o.after, o.before) : null) : "reverted"}
                    </th>
                  );
                })}
              </tr>
            </tbody>
          </table>
        </div>
        {n > PREVIEW ? (
          <button type="button" className="steps-toggle" aria-expanded={all} aria-controls={tableId} onClick={() => setAll((x) => !x)}>
            {all ? `Show the first ${PREVIEW} swaps` : `Show all ${n} swaps`}
          </button>
        ) : null}
      </div>

      <details style={{ marginTop: 16 }}>
        <summary className="small">Executables and Passports that answered</summary>
        <div className="table-scroll" style={{ marginTop: 8 }}>
          <table className="small">
            <thead>
              <tr>
                <th>Version</th>
                <th>Source sha256</th>
                <th>Executable sha256</th>
                <th>Passport of this source</th>
                <th className="num">Run time</th>
              </tr>
            </thead>
            <tbody>
              {response.versions.map((v) => (
                <tr key={v.version}>
                  <td>{versionInfo(v.version).name}</td>
                  <td className="hash">{shortHash(v.solution_sha256, 16)}</td>
                  <td className="hash">{shortHash(v.executable_sha256, 16)}</td>
                  <td>
                    {v.passport ? (
                      <>
                        <Status value={v.passport.status} /> <span className="hash">{shortHash(v.passport.passport_sha256)}</span>
                      </>
                    ) : (
                      <span className="muted">none recorded for this source</span>
                    )}
                  </td>
                  <td className="num">{formatMs(v.elapsed_ms)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </details>
    </div>
  );
}

function StepCell({ r, i }: { r: SwapResultOut; i: number }) {
  const s = r.steps[i];
  if (!s) return <td className="num" data-state="skipped">not run</td>;
  if (!s.ok) return <td className="num" data-state="refused">refused</td>;
  const before = r.value_before ? BigInt(r.value_before) : null;
  return (
    <td className="num mono">
      <div>{formatBig(s.quote)}</div>
      <div>{before && s.value != null ? formatPct(pct(BigInt(s.value), before)) : "none"}</div>
    </td>
  );
}

/** The first swap where this version and the Muse repair start from the same pool and differ. */
function firstDifference(v: SwapResultOut, rep: SwapResultOut) {
  const n = Math.max(v.steps.length, rep.steps.length);
  for (let i = 0; i < n; i++) {
    const a = v.steps[i];
    const b = rep.steps[i];
    if (!a || !b) return null;
    if (a.ok !== b.ok) return { i, kind: a.ok ? ("accepts" as const) : ("refuses" as const), a, b };
    if (!a.ok) return null;
    if (a.quote !== b.quote) return { i, kind: "quote" as const, a, b };
  }
  return null;
}

function OutcomeCard({ v, repaired, batch, tokens, scale }: { v: SwapVersionOut; repaired: SwapVersionOut | null; batch: SwapBatch; tokens: [string, string]; scale: number }) {
  const info = versionInfo(v.version);
  const o = outcome(v.result);
  const fell = o.ok && o.changePct != null && o.changePct < 0;
  const diff = repaired ? firstDifference(v.result, repaired.result) : null;
  let compare: string | null = null;
  if (repaired) {
    if (!diff) compare = "Same result as the Muse repair on every swap that ran.";
    else {
      const s = batch.swaps[diff.i]!;
      const what = s.kind === "out" ? "charged" : "paid";
      if (diff.kind === "refuses") compare = `Refuses swap ${diff.i + 1}, which the Muse repair accepts.`;
      else if (diff.kind === "accepts") compare = `Accepts swap ${diff.i + 1}, which the Muse repair refuses.`;
      else {
        const a = BigInt(diff.a.quote ?? "0");
        const b = BigInt(diff.b.quote ?? "0");
        const more = a > b;
        const rel = b > 0n ? formatPct(pct(a > b ? a - b : b - a, b)) : null;
        compare = `Swap ${diff.i + 1}: ${what} ${formatBig(a)} ${s.kind === "out" ? tokens[s.in] : tokens[s.out]} wei, ${formatBig(a > b ? a - b : b - a)} ${more ? "more" : "less"} than the Muse repair${rel ? ` (${rel})` : ""}.`;
      }
    }
  }
  // Red when the pool lost value or a swap the repair accepts is refused; green when the pool kept
  // its value and the version matches the repair (or is the repair); otherwise neutral.
  const tone = fell || diff?.kind === "refuses" ? "bad" : !diff ? "ok" : undefined;
  return (
    <div className="card outcome" data-tone={tone}>
      <h3>
        <span className="swatch" style={{ ["--swatch" as string]: SERIES_COLOR(v.version) }} aria-hidden="true" />
        {info.name}
      </h3>
      {o.ok ? (
        <>
          <p className="outcome-figure">{formatPct(o.changePct, true)}</p>
          <p>
            The batch went through. The pool&apos;s value went from {formatBig(o.before)} to {formatBig(o.after)}
            {fell ? <>, a loss the requirement REQ-BATCH-KEEPS-VALUE rules out.</> : "."}
          </p>
        </>
      ) : (
        <>
          <p className="outcome-figure">Swap {o.refusedAt} refused</p>
          <p>
            The batch reverts and the pool keeps its value of {formatBig(o.before)}.
            {o.ran > 0 && o.lowestPct != null
              ? o.lowestPct >= 100
                ? ` Over the ${o.ran} ${o.ran === 1 ? "swap" : "swaps"} before it, the value never fell below its start.`
                : ` Before the revert the value fell to ${formatPct(o.lowestPct)} of the start.`
              : ""}
          </p>
        </>
      )}
      <ValueBar end={endPct(v.result)} scale={scale} color={SERIES_COLOR(v.version)} reverted={!o.ok} />
      {compare ? <p>{compare}</p> : null}
      <p className="small muted">
        Passport: {info.verdict === "VERIFIED" ? <Seal size={24} /> : null}<Status value={info.verdict} />
      </p>
    </div>
  );
}

/** The pool's value after the batch as a bar, on one scale for the three cards, with the start marked. */
function ValueBar({ end, scale, color, reverted }: { end: number | null; scale: number; color: string; reverted: boolean }) {
  if (end == null) return null;
  const w = Math.max(0, Math.min(100, (end / scale) * 100));
  const start = (100 / scale) * 100;
  return (
    <div className="vbar" role="img" aria-label={`Value after the batch: ${formatPct(end)} of the start${reverted ? ", kept by the revert" : ""}`}>
      <div className="vbar-track">
        <span className="vbar-fill" style={{ width: `${w.toFixed(2)}%`, ["--swatch" as string]: color }} />
        <span className="vbar-start" style={{ left: `${start.toFixed(2)}%` }} />
      </div>
      <p className="vbar-label">
        <span>{formatPct(end)} of the start after the batch</span>
        {reverted ? <span>kept by the revert</span> : null}
      </p>
    </div>
  );
}
