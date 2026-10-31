"use client";

import { useEffect, useRef, useState } from "react";
import { formatPct } from "@/lib/swap";

export interface ChartSeries {
  key: string;
  label: string;
  /** CSS color, a custom property of .replay. */
  color: string;
  dashed: boolean;
  /** Pool value in percent of the start, index 0 is the start; null once the batch stopped. */
  values: (number | null)[];
}


function niceStep(max: number): number {
  const raw = max / 5;
  const pow = 10 ** Math.floor(Math.log10(raw));
  for (const m of [1, 2, 2.5, 5, 10]) if (raw <= m * pow) return m * pow;
  return 10 * pow;
}

/** Pool value after each swap, one line per version, with a crosshair readout of every series. */
export function ValueChart({ series, stepLabels }: { series: ChartSeries[]; stepLabels: string[] }) {
  // Drawn at the box's own pixel width, so text stays at its set size on a phone.
  const box = useRef<HTMLDivElement>(null);
  const [W, setW] = useState(720);
  useEffect(() => {
    const el = box.current;
    if (!el) return;
    const ro = new ResizeObserver(() => setW(Math.max(280, Math.round(el.clientWidth))));
    ro.observe(el);
    return () => ro.disconnect();
  }, []);
  const narrow = W < 520;
  const H = narrow ? 220 : 260;
  const M = { top: 12, right: narrow ? 64 : 136, bottom: 28, left: 44 };
  const n = Math.max(...series.map((s) => s.values.length)) - 1;
  const all = series.flatMap((s) => s.values.filter((v): v is number => v != null));
  const top = Math.max(110, ...all) * 1.04;
  const step = niceStep(top);
  const ticks: number[] = [];
  for (let t = 0; t <= top; t += step) ticks.push(t);
  const x = (i: number) => M.left + (n === 0 ? 0 : (i / n) * (W - M.left - M.right));
  const y = (v: number) => M.top + (1 - v / top) * (H - M.top - M.bottom);
  const xTicks = n <= (narrow ? 6 : 12) ? Array.from({ length: n + 1 }, (_, i) => i) : Array.from({ length: narrow ? 4 : 7 }, (_, k) => Math.round((k * n) / (narrow ? 3 : 6)));

  const [hover, setHover] = useState<number | null>(null);
  const onMove = (e: React.PointerEvent<SVGSVGElement>) => {
    const r = e.currentTarget.getBoundingClientRect();
    const sx = ((e.clientX - r.left) / r.width) * W;
    const i = Math.round(((sx - M.left) / (W - M.left - M.right)) * n);
    setHover(Math.max(0, Math.min(n, i)));
  };

  // End labels: series that end at the same point share one label; labels are pushed apart.
  const ends: { keys: string[]; labels: string[]; color: string; i: number; v: number; ly: number }[] = [];
  for (const s of series) {
    let last = -1;
    s.values.forEach((v, i) => {
      if (v != null) last = i;
    });
    if (last < 0) continue;
    const v = s.values[last]!;
    const same = ends.find((e) => e.i === last && e.v === v);
    if (same) {
      same.keys.push(s.key);
      same.labels.push(s.label);
      same.color = s.color;
    } else ends.push({ keys: [s.key], labels: [s.label], color: s.color, i: last, v, ly: y(v) });
  }
  ends.sort((a, b) => a.ly - b.ly);
  for (let k = 1; k < ends.length; k++) if (ends[k]!.ly - ends[k - 1]!.ly < 14) ends[k]!.ly = ends[k - 1]!.ly + 14;

  const tipLeft = hover == null ? 0 : x(hover);
  const tipFlip = hover != null && hover > n / 2;

  return (
    <div className="chart-box" ref={box}>
      <svg
        viewBox={`0 0 ${W} ${H}`}
        role="img"
        aria-label="Pool value after each swap, in percent of the starting value, for each version"
        onPointerMove={onMove}
        onPointerLeave={() => setHover(null)}
      >
        <g className="grid">
          {ticks.map((t) => (
            <line key={t} x1={M.left} x2={W - M.right} y1={y(t)} y2={y(t)} />
          ))}
        </g>
        <g className="axis">
          {ticks.map((t) => (
            <text key={t} x={M.left - 8} y={y(t) + 4} textAnchor="end">
              {t}%
            </text>
          ))}
          {xTicks.map((i) => (
            <text key={i} x={x(i)} y={H - 8} textAnchor="middle">
              {i === 0 ? "start" : i}
            </text>
          ))}
        </g>
        {series.map((s) => {
          const pts = s.values.map((v, i) => (v == null ? null : `${x(i).toFixed(1)},${y(v).toFixed(1)}`)).filter(Boolean);
          return (
            <polyline
              key={s.key}
              className="series"
              points={pts.join(" ")}
              stroke={s.color}
              strokeDasharray={s.dashed ? "7 5" : undefined}
            />
          );
        })}
        {ends.map((e) => (
          <g key={e.keys.join(",")}>
            <circle cx={x(e.i)} cy={y(e.v)} r={4} fill={e.color} stroke="var(--surface)" strokeWidth={2} />
            <text className="end-label" x={x(e.i) + 8} y={e.ly + 4}>
              {narrow ? formatPct(e.v) : `${e.labels.join(" and ")} ${formatPct(e.v)}`}
            </text>
          </g>
        ))}
        {hover != null ? (
          <g>
            <line className="crosshair" x1={x(hover)} x2={x(hover)} y1={M.top} y2={H - M.bottom} />
            {series.map((s) =>
              s.values[hover] != null ? (
                <circle key={s.key} cx={x(hover)} cy={y(s.values[hover]!)} r={4} fill={s.color} stroke="var(--surface)" strokeWidth={2} />
              ) : null,
            )}
          </g>
        ) : null}
      </svg>
      {hover != null ? (
        <div className="chart-tip" style={tipFlip ? { right: `calc(100% - ${tipLeft - 12}px)` } : { left: tipLeft + 12 }}>
          <div className="tip-head">{hover === 0 ? "Start" : `After swap ${hover}: ${stepLabels[hover - 1] ?? ""}`}</div>
          {series.map((s) => (
            <div key={s.key}>
              <span>{s.label}</span>
              <strong>{s.values[hover] == null ? "stopped" : formatPct(s.values[hover]!)}</strong>
            </div>
          ))}
        </div>
      ) : null}
    </div>
  );
}
