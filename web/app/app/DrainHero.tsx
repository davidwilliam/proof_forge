"use client";

import { useState } from "react";
import { DRAIN, PRESETS, describeSwap, formatBig, formatPct, pct, versionInfo } from "@/lib/swap";
import { Status } from "@/components/ui";

const ATTACK = PRESETS.find((p) => p.key === "attack")!;
const BEFORE = BigInt(DRAIN.before);
const VALUES = [BEFORE, ...DRAIN.steps.map((s) => BigInt(s))];
const PCTS = VALUES.map((v) => pct(v, BEFORE));
const N = VALUES.length - 1;
const AFTER = VALUES[N]!;
const CHANGE = pct(AFTER - BEFORE, BEFORE);
const POOL = `${formatBig(ATTACK.batch.pool.balances[0])} wei of ${ATTACK.tokens[0]} and ${formatBig(ATTACK.batch.pool.balances[1])} wei of ${ATTACK.tokens[1]}`;

// Drawn in a 1000 x 300 box stretched to the container; marks and labels are HTML on top, placed in percent.
const TOP = 106;
const X = (i: number) => (i / N) * 1000;
const Y = (p: number) => 14 + (1 - p / TOP) * 272;
const xPct = (i: number) => `${((X(i) / 1000) * 100).toFixed(2)}%`;
const yPct = (p: number) => `${((Y(p) / 300) * 100).toFixed(2)}%`;
const r1 = (n: number) => Math.round(n * 10) / 10;

const line = PCTS.map((p, i) => `${r1(X(i))},${r1(Y(p))}`).join(" ");
const drained = `${r1(X(0))},${r1(Y(100))} ${r1(X(N))},${r1(Y(100))} ${PCTS.map((p, i) => `${r1(X(N - i))},${r1(Y(PCTS[N - i]!))}`).join(" ")}`;

function readout(i: number | null): string {
  if (i == null) return `Deployed code: ${formatBig(BEFORE)} at the start, ${formatBig(AFTER)} after swap ${N}. Focus or hover a point to read each swap.`;
  if (i === 0) return `Start: the pool's value is ${formatBig(BEFORE)}, from ${POOL}.`;
  const round = Math.ceil(i / 3);
  return `Swap ${i}, round ${round}: ${describeSwap(ATTACK.batch.swaps[i - 1]!, ATTACK.tokens)}. Value ${formatBig(VALUES[i]!)}, ${formatPct(PCTS[i]!)} of the start.`;
}

/** The drain at a glance: the deployed code's pool value over the four-round attack batch, against the floor the Muse repair proves. */
export function DrainHero() {
  const [hover, setHover] = useState<number | null>(null);
  const deployed = versionInfo("deployed");
  const repaired = versionInfo("repaired");
  return (
    <section className="drain card" aria-labelledby="drain-title">
      <div className="drain-text">
        <h2 id="drain-title">Four rounds of the attack, on the deployed code and on the Muse repair</h2>
        <div className="drain-fig drain-fig-bad">
          <p className="drain-who">
            <span className="swatch" style={{ ["--swatch" as string]: "var(--series-deployed)" }} aria-hidden="true" />
            {deployed.name}
          </p>
          <p className="drain-big">
            {formatBig(BEFORE)} <span aria-hidden="true">→</span>
            <span className="sr-only">to</span> {formatBig(AFTER)}
          </p>
          <p className="drain-sub">
            The pool&apos;s value, {formatPct(CHANGE, true)} in 12 swaps. Passport <Status value={deployed.verdict} />
          </p>
        </div>
        <div className="drain-fig drain-fig-ok">
          <p className="drain-who">
            <span className="swatch" style={{ ["--swatch" as string]: "var(--series-repaired)" }} aria-hidden="true" />
            {repaired.name}
          </p>
          <p className="drain-big">never below {formatBig(BEFORE)}</p>
          <p className="drain-sub">
            Proved for any batch that goes through (REQ-BATCH-KEEPS-VALUE), with this batch&apos;s constant-product math. Passport{" "}
            <Status value={repaired.verdict} />
          </p>
        </div>
      </div>

      <div className="drain-viz">
        <div className="drain-plot" onPointerLeave={() => setHover(null)}>
          <svg viewBox="0 0 1000 300" preserveAspectRatio="none" aria-hidden="true" focusable="false">
            {[0, 25, 50, 75].map((t) => (
              <line key={t} className="drain-grid" x1={0} x2={1000} y1={r1(Y(t))} y2={r1(Y(t))} vectorEffect="non-scaling-stroke" />
            ))}
            {[3, 6, 9].map((i) => (
              <line key={i} className="drain-round" x1={r1(X(i))} x2={r1(X(i))} y1={r1(Y(0))} y2={r1(Y(TOP))} vectorEffect="non-scaling-stroke" />
            ))}
            <polygon className="drain-area" points={drained} />
            <line className="drain-floor" x1={0} x2={1000} y1={r1(Y(100))} y2={r1(Y(100))} vectorEffect="non-scaling-stroke" />
            <polyline className="drain-line" points={line} vectorEffect="non-scaling-stroke" />
            {hover != null ? <line className="drain-cross" x1={r1(X(hover))} x2={r1(X(hover))} y1={r1(Y(0))} y2={r1(Y(TOP))} vectorEffect="non-scaling-stroke" /> : null}
          </svg>
          {[0, 25, 50, 75, 100].map((t) => (
            <span key={t} className="drain-tick" style={{ top: yPct(t) }} aria-hidden="true">
              {t}%
            </span>
          ))}
          <span className="drain-label drain-label-floor" style={{ top: yPct(100) }} aria-hidden="true">
            Muse repair: the proved floor
          </span>
          <span className="drain-label drain-label-loss" style={{ top: yPct(62) }} aria-hidden="true">
            <strong>{formatPct(-CHANGE)}</strong> of the value drained
          </span>
          <span className="drain-label drain-label-end" style={{ top: yPct(PCTS[N]!) }} aria-hidden="true">
            {formatBig(AFTER)}
          </span>
          {PCTS.map((p, i) => (
            <button
              key={i}
              type="button"
              className="drain-dot"
              style={{ left: xPct(i), top: yPct(p) }}
              aria-label={readout(i)}
              aria-pressed={hover === i}
              data-on={hover === i ? "" : undefined}
              onPointerEnter={() => setHover(i)}
              onFocus={() => setHover(i)}
              onBlur={() => setHover(null)}
            />
          ))}
        </div>
        <div className="drain-axis" aria-hidden="true">
          <span style={{ left: xPct(0) }}>start</span>
          {[3, 6, 9, 12].map((i) => (
            <span key={i} style={{ left: xPct(i - 1.5) }}>
              round {i / 3}
            </span>
          ))}
        </div>
        <p className="drain-readout" aria-live="polite">
          {readout(hover)}
        </p>
      </div>

      <details className="drain-table">
        <summary>The 12 values, as the Passport&apos;s witness records them</summary>
        <div className="table-scroll">
          <table className="small">
            <thead>
              <tr>
                <th className="num">Swap</th>
                <th>Request</th>
                <th className="num">Pool value, deployed code</th>
                <th className="num">Percent of the start</th>
              </tr>
            </thead>
            <tbody>
              {VALUES.map((v, i) => (
                <tr key={i}>
                  <td className="num">{i === 0 ? "start" : i}</td>
                  <td>{i === 0 ? POOL : describeSwap(ATTACK.batch.swaps[i - 1]!, ATTACK.tokens)}</td>
                  <td className="num mono">{formatBig(v)}</td>
                  <td className="num mono">{formatPct(PCTS[i]!)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </details>
    </section>
  );
}
