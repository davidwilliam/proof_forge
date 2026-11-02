"use client";

import { useState } from "react";
import { median, recordedLabel, type ReliabilityRun } from "@/lib/challenge";
import { Status } from "@/components/ui";

const MAX_S = 0.5;
const TICKS = [0, 0.1, 0.2, 0.3, 0.4, 0.5];

/** Two drawings of the same chart: wide for desktop, compact for a phone, so text stays legible. */
const GEOMETRY = {
  wide: { W: 960, pad: 20, r: 6, step: 13, laneGap: 26, top: 34, font: 14 },
  compact: { W: 360, pad: 12, r: 3, step: 7, laneGap: 18, top: 28, font: 12 },
};
type Geometry = (typeof GEOMETRY)["wide"];

/** Rounded so the server and the browser render the same coordinates. */
const xOf = (g: Geometry, s: number) => Math.round((g.pad + (Math.min(s, MAX_S) / MAX_S) * (g.W - 2 * g.pad)) * 10) / 10;

interface Dot {
  key: string;
  run: number;
  session: number;
  seconds: number;
  refuted: boolean;
  level: number;
}

/** Equal round trips stack upward, one dot per call. */
function stack(run: ReliabilityRun, ri: number): Dot[] {
  const seen = new Map<number, number>();
  return [...run.calls]
    .sort((a, b) => a.seconds - b.seconds || a.session - b.session)
    .map((c) => {
      const k = Math.round(c.seconds * 100);
      const level = seen.get(k) ?? 0;
      seen.set(k, level + 1);
      return { key: `${ri}-${c.session}`, run: ri, session: c.session, seconds: c.seconds, refuted: c.refuted, level };
    });
}

function Chart({
  g,
  lanes,
  med,
  cur,
  onPick,
  className,
}: {
  g: Geometry;
  lanes: { run: ReliabilityRun; dots: Dot[] }[];
  med: number;
  cur: Dot;
  onPick: (k: string) => void;
  className: string;
}) {
  const heights = lanes.map((l) => Math.max(1, ...l.dots.map((d) => d.level + 1)) * g.step + g.font * 2.4);
  const H = Math.round(g.top + heights.reduce((a, b) => a + b + g.laneGap, 0) + g.font);
  const n = lanes.reduce((a, l) => a + l.dots.length, 0);
  let y0 = g.top;
  return (
    <svg
      viewBox={`0 0 ${g.W} ${H}`}
      className={`swarm-svg ${className}`}
      role="img"
      aria-label={`Round trips of ${n} recorded challenge calls, on an axis from 0 to ${MAX_S} s`}
      style={{ fontSize: g.font }}
    >
      {TICKS.map((t) => (
        <g key={t}>
          <line x1={xOf(g, t)} x2={xOf(g, t)} y1={g.top - 6} y2={H - g.font - 4} className="swarm-grid" />
          <text x={xOf(g, t)} y={g.font + 2} className="swarm-tick" style={{ fontSize: g.font }} textAnchor={t === 0 ? "start" : t === MAX_S ? "end" : "middle"}>
            {t === 0 ? "0 s" : `${t.toFixed(1)} s`}
          </text>
        </g>
      ))}
      <line x1={xOf(g, med)} x2={xOf(g, med)} y1={g.top - 6} y2={H - g.font - 4} className="swarm-median" />
      {lanes.map((l, i) => {
        const h = heights[i]!;
        const top = y0;
        y0 += h + g.laneGap;
        const base = Math.round(top + h - g.r - 2);
        return (
          <g key={l.run.source}>
            <text x={g.pad} y={Math.round(top + g.font)} className="swarm-lane" style={{ fontSize: g.font }}>
              Run {i + 1}, {recordedLabel(l.run.recordedAt)}, {l.run.calls.filter((c) => c.refuted).length} of {l.run.calls.length} refuted
            </text>
            {l.dots.map((d) => (
              <circle
                key={d.key}
                cx={xOf(g, d.seconds)}
                cy={Math.round(base - d.level * g.step)}
                r={d.key === cur.key ? g.r + 1.5 : g.r}
                className={d.refuted ? "ch-dot" : "ch-dot ch-dot-open"}
                data-active={d.key === cur.key ? "" : undefined}
                tabIndex={0}
                aria-label={`Run ${i + 1}, session ${d.session}: ${d.seconds.toFixed(2)} s, ${d.refuted ? "REFUTED" : "not refuted"}`}
                onMouseEnter={() => onPick(d.key)}
                onFocus={() => onPick(d.key)}
              />
            ))}
          </g>
        );
      })}
      <text x={xOf(g, med) + 6} y={H - 4} className="swarm-label" style={{ fontSize: g.font }}>
        median {med.toFixed(2)} s
      </text>
    </svg>
  );
}

/** The recorded round trips of the deployed challenge: one dot per call, one lane per reliability run. */
export function RoundTrips({ runs }: { runs: ReliabilityRun[] }) {
  const lanes = runs.map((r, i) => ({ run: r, dots: stack(r, i) }));
  const all = lanes.flatMap((l) => l.dots);
  const slowest = all.reduce<Dot | undefined>((a, d) => (!a || d.seconds > a.seconds ? d : a), undefined);
  const [active, setActive] = useState(slowest?.key ?? "");
  if (!slowest) return null;
  const cur = all.find((d) => d.key === active) ?? slowest;
  const curRun = runs[cur.run]!;
  const med = median(all.map((d) => d.seconds));
  return (
    <figure className="swarm ch-trips">
      <Chart g={GEOMETRY.wide} lanes={lanes} med={med} cur={cur} onPick={setActive} className="ch-trips-wide" />
      <Chart g={GEOMETRY.compact} lanes={lanes} med={med} cur={cur} onPick={setActive} className="ch-trips-compact" />
      <figcaption className="gm-readout ch-readout" aria-live="polite">
        <p className="win-item-head">
          <strong>{cur.seconds.toFixed(2)} s round trip</strong>
          <Status value={cur.refuted ? "REFUTED" : "UNRESOLVED"}>{cur.refuted ? "REFUTED" : "not refuted"}</Status>
        </p>
        <p className="win-item-detail">
          Run {cur.run + 1}, session {cur.session}, recorded {curRun.recordedAt} against {curRun.api}; {curRun.source}.
        </p>
      </figcaption>
    </figure>
  );
}
