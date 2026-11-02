"use client";

import { useState } from "react";
import { Ticked } from "./Ticked";

export interface FactorPoint {
  key: string;
  id: string;
  lane: "cost" | "time";
  value: number;
  kind: string;
  kindLabel: string;
  model: string;
  detail: string;
}

const W = 960;
const PAD_L = 24;
const PAD_R = 24;
const LANE_H = 200;
const R = 5;
const MAX = 8;

const LANES = [
  { lane: "cost" as const, title: "Cheaper per verified run", unit: "cheaper" },
  { lane: "time" as const, title: "Faster, mean wall time of the verified runs", unit: "faster" },
];

/** Rounded so the server and the browser render the same coordinates. */
const xOf = (v: number) => Math.round((PAD_L + (Math.log(Math.min(v, MAX)) / Math.log(MAX)) * (W - PAD_L - PAD_R)) * 10) / 10;

/** Places each dot at its value and moves it up or down until it clears the dots already placed. */
function swarm(points: FactorPoint[]): Map<string, number> {
  const placed: { x: number; y: number }[] = [];
  const out = new Map<string, number>();
  const step = R * 2 + 2;
  for (const p of [...points].sort((a, b) => a.value - b.value)) {
    const x = xOf(p.value);
    let y = 0;
    for (let k = 0; k < 15; k++) {
      y = (k % 2 ? 1 : -1) * Math.ceil(k / 2) * step * 0.9;
      if (placed.every((q) => (q.x - x) ** 2 + (q.y - y) ** 2 >= step * step)) break;
    }
    y = Math.round(y * 10) / 10;
    placed.push({ x, y });
    out.set(p.key, y);
  }
  return out;
}

const median = (xs: number[]) => {
  const s = [...xs].sort((a, b) => a - b);
  const m = s.length >> 1;
  return s.length % 2 ? s[m]! : (s[m - 1]! + s[m]!) / 2;
};

/** The factors of the gains where both arms verified: one dot per comparison, on a log scale from 1x. */
export function FactorSwarm({ points }: { points: FactorPoint[] }) {
  const top = [...points].sort((a, b) => b.value - a.value)[0]!;
  const [active, setActive] = useState(top.key);
  const cur = points.find((p) => p.key === active) ?? top;
  const ticks = [1, 1.5, 2, 3, 4, 5, 6, 8];
  const H = LANES.length * LANE_H + 28;
  return (
    <figure className="swarm">
      <svg viewBox={`0 0 ${W} ${H}`} className="swarm-svg" role="img" aria-label="How much cheaper and how much faster with ProofForge, one dot per comparison">
        {ticks.map((t) => (
          <g key={t}>
            <line x1={xOf(t)} x2={xOf(t)} y1={8} y2={H - 22} className="swarm-grid" />
            <text x={xOf(t)} y={H - 6} className="swarm-tick" textAnchor="middle">
              {t}x
            </text>
          </g>
        ))}
        {LANES.map((l, i) => {
          const pts = points.filter((p) => p.lane === l.lane);
          const ys = swarm(pts);
          const cy = i * LANE_H + LANE_H / 2 + 18;
          const med = median(pts.map((p) => p.value));
          const best = pts.reduce((a, b) => (b.value > a.value ? b : a));
          return (
            <g key={l.lane}>
              <text x={PAD_L} y={i * LANE_H + 22} className="swarm-lane">
                {l.title}, {pts.length} comparisons, median {med.toFixed(2)}x
              </text>
              <line x1={xOf(med)} x2={xOf(med)} y1={cy - 66} y2={cy + 66} className="swarm-median" />
              {pts.map((p) => (
                <circle
                  key={p.key}
                  cx={xOf(p.value)}
                  cy={cy + (ys.get(p.key) ?? 0)}
                  r={p.key === cur.key ? R + 2 : R}
                  className="swarm-dot"
                  data-kind={p.kind}
                  data-active={p.key === cur.key ? "" : undefined}
                  tabIndex={0}
                  aria-label={`${p.id}: ${p.value.toFixed(2)}x ${l.unit}`}
                  onMouseEnter={() => setActive(p.key)}
                  onFocus={() => setActive(p.key)}
                />
              ))}
              <text x={xOf(best.value) - 12} y={cy + (ys.get(best.key) ?? 0) - 12} className="swarm-label" textAnchor="end">
                {best.value.toFixed(2)}x
              </text>
            </g>
          );
        })}
      </svg>
      <figcaption className="gm-readout swarm-readout" aria-live="polite">
        <p className="win-item-head">
          <span className="gm-swatch" data-kind={cur.kind} aria-hidden="true" />
          <strong>
            {cur.value.toFixed(2)}x {LANES.find((l) => l.lane === cur.lane)!.unit}
          </strong>
          <code>{cur.id}</code>
          <span className="win-item-meta">
            {cur.model}, {cur.kindLabel}
          </span>
        </p>
        <p className="win-item-detail">
          <Ticked text={cur.detail} />
        </p>
      </figcaption>
    </figure>
  );
}
