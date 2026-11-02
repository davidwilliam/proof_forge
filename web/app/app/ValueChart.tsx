"use client";

import { useEffect, useRef, useState } from "react";
import { formatBig, formatPct } from "@/lib/swap";

/** What happened to one swap in one version: it went through and stands, went through and was undone by the batch's revert, was refused, or never ran. */
export type StepState = "kept" | "undone" | "refused" | "skipped";

export interface ChartSeries {
  key: string;
  label: string;
  /** CSS color, a custom property of .replay. */
  color: string;
  dashed: boolean;
  /** Pool value in percent of the start, index 0 is the start; null once the batch stopped. */
  values: (number | null)[];
  /** One per swap. */
  states: StepState[];
  /** Amount charged or paid on each swap, a decimal string; null when it did not go through. */
  quotes: (string | null)[];
  /** The value after the batch in percent of the start; the start (100) when it reverted. */
  final: number | null;
  /** 1-based index of the refused swap, when the batch reverted. */
  refusedAt: number | null;
}

function niceStep(max: number): number {
  const raw = max / 5;
  const pow = 10 ** Math.floor(Math.log10(raw));
  for (const m of [1, 2, 2.5, 5, 10]) if (raw <= m * pow) return m * pow;
  return 10 * pow;
}

const r1 = (n: number) => Math.round(n * 10) / 10;

const STATE_TEXT: Record<StepState, string> = {
  kept: "went through",
  undone: "went through, undone by the revert",
  refused: "refused",
  skipped: "not run",
};

/**
 * Pool value after each swap, one line per version, with the first refused swap marked, a per-swap strip
 * under the plot (one row per version) and a fixed-height readout. The plot takes keyboard focus; the
 * arrow keys, Home and End move between swaps.
 */
export function ValueChart({ series, stepLabels, stepKinds }: { series: ChartSeries[]; stepLabels: string[]; stepKinds: ("in" | "out")[] }) {
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
  const narrow = W < 560;
  const plotH = narrow ? 230 : 330;
  const M = { top: 30, right: narrow ? 52 : 168, left: narrow ? 74 : 92 };
  const n = Math.max(...series.map((s) => s.values.length)) - 1;
  const all = series.flatMap((s) => s.values.filter((v): v is number => v != null));
  const top = Math.max(110, ...all) * 1.04;
  const step = niceStep(top);
  const ticks: number[] = [];
  for (let t = 0; t <= top; t += step) ticks.push(t);
  const plotW = W - M.left - M.right;
  const x = (i: number) => r1(M.left + (n === 0 ? 0 : (i / n) * plotW));
  const y = (v: number) => r1(M.top + (1 - v / top) * plotH);
  const axisY = M.top + plotH;
  const xTicks = n <= (narrow ? 6 : 12) ? Array.from({ length: n + 1 }, (_, i) => i) : Array.from({ length: narrow ? 4 : 7 }, (_, k) => Math.round((k * n) / (narrow ? 3 : 6)));

  // The per-swap strip, one row per version, under the swap axis.
  const rowH = 12;
  const rowGap = 7;
  const stripTop = axisY + 34;
  const H = stripTop + series.length * (rowH + rowGap) + 2;
  const cw = Math.max(1.5, Math.min(18, plotW / Math.max(1, n) - (n > 40 ? 1 : 3)));

  // The first refused swap, and every version that refused it.
  const firstRefusal = series.reduce<number | null>((m, s) => (s.refusedAt != null && (m == null || s.refusedAt < m) ? s.refusedAt : m), null);
  const refusers = firstRefusal == null ? [] : series.filter((s) => s.refusedAt === firstRefusal);

  const [hover, setHover] = useState<number | null>(null);
  const onMove = (e: React.PointerEvent<SVGSVGElement>) => {
    const r = e.currentTarget.getBoundingClientRect();
    const sx = ((e.clientX - r.left) / r.width) * W;
    const i = Math.round(((sx - M.left) / plotW) * n);
    setHover(Math.max(0, Math.min(n, i)));
  };
  const onKey = (e: React.KeyboardEvent<SVGSVGElement>) => {
    const cur = hover ?? (firstRefusal ?? n);
    let next: number | null = null;
    if (e.key === "ArrowRight" || e.key === "ArrowUp") next = Math.min(n, cur + 1);
    else if (e.key === "ArrowLeft" || e.key === "ArrowDown") next = Math.max(0, cur - 1);
    else if (e.key === "Home") next = 0;
    else if (e.key === "End") next = n;
    else if (e.key === "Escape") return setHover(null);
    if (next != null) {
      e.preventDefault();
      setHover(next);
    }
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
  for (let k = 1; k < ends.length; k++) if (ends[k]!.ly - ends[k - 1]!.ly < 15) ends[k]!.ly = ends[k - 1]!.ly + 15;

  const refX = firstRefusal != null ? x(firstRefusal) : 0;
  const refLeft = refX > M.left + plotW * 0.55;
  const refText = firstRefusal == null ? "" : narrow ? `Swap ${firstRefusal} refused` : `Swap ${firstRefusal} refused by ${refusers.map((s) => s.label).join(" and ")}; the batch reverts`;

  const what = (i: number) => (stepKinds[i - 1] === "in" ? "paid" : "charged");

  return (
    <div className="chart-box" ref={box}>
      <svg
        viewBox={`0 0 ${W} ${H}`}
        role="img"
        tabIndex={0}
        aria-label="Pool value after each swap, in percent of the starting value, for each version, with a strip of what happened to each swap. Use the arrow keys to read each swap."
        onPointerMove={onMove}
        onPointerLeave={() => setHover(null)}
        onKeyDown={onKey}
        onFocus={() => setHover((h) => h ?? firstRefusal ?? n)}
        onBlur={() => setHover(null)}
      >
        <g className="grid">
          {ticks.map((t) => (
            <line key={t} x1={M.left} x2={M.left + plotW} y1={y(t)} y2={y(t)} />
          ))}
        </g>
        <line className="start-line" x1={M.left} x2={M.left + plotW} y1={y(100)} y2={y(100)} />
        <g className="axis">
          {ticks.map((t) => (
            <text key={t} x={M.left - 8} y={y(t) + 4} textAnchor="end">
              {t}%
            </text>
          ))}
          {xTicks.map((i) => (
            <text key={i} x={x(i)} y={axisY + 18} textAnchor="middle">
              {i === 0 ? "start" : i}
            </text>
          ))}
          {!narrow ? (
            <text x={M.left + plotW} y={axisY + 18} textAnchor="start" dx={10}>
              swap
            </text>
          ) : null}
        </g>

        {firstRefusal != null ? (
          <g className="refusal">
            <line x1={refX} x2={refX} y1={M.top - 14} y2={axisY} />
            <text x={refX} y={M.top - 18} dx={refLeft ? -6 : 6} textAnchor={refLeft ? "end" : "start"}>
              {refText}
            </text>
          </g>
        ) : null}

        {series.map((s) => {
          const pts = s.values.map((v, i) => (v == null ? null : `${x(i)},${y(v)}`)).filter(Boolean);
          return <polyline key={s.key} className="series" points={pts.join(" ")} stroke={s.color} strokeDasharray={s.dashed ? "7 5" : undefined} />;
        })}

        {/* A cross where each reverted version was refused, at the value it had reached. */}
        {series.map((s) => {
          if (s.refusedAt == null) return null;
          const last = s.values[s.refusedAt - 1];
          if (last == null) return null;
          const cx = x(s.refusedAt);
          const cy = y(last);
          return (
            <g key={s.key} className="refused-x" stroke={s.color}>
              <line x1={cx - 5} x2={cx + 5} y1={cy - 5} y2={cy + 5} />
              <line x1={cx - 5} x2={cx + 5} y1={cy + 5} y2={cy - 5} />
            </g>
          );
        })}

        {ends.map((e) => {
          // A line that stopped early is labelled above and to the left of its last point, clear of the refusal mark.
          const early = e.i < n;
          const text = narrow ? formatPct(e.v) : `${e.labels.join(" and ")} ${formatPct(e.v)}`;
          // When the label does not fit to the left, it goes to the right, above the refusal mark.
          const left = early && x(e.i) - 8 - text.length * 6.4 >= M.left;
          return (
            <g key={e.keys.join(",")}>
              <circle cx={x(e.i)} cy={y(e.v)} r={4} fill={e.color} stroke="var(--surface)" strokeWidth={2} />
              <text
                className="end-label"
                x={!early ? x(e.i) + 8 : left ? x(e.i) - 8 : x(e.i) + 4}
                y={!early ? e.ly + 4 : left ? y(e.v) - 8 : y(e.v) - 14}
                textAnchor={left ? "end" : "start"}
              >
                {text}
              </text>
            </g>
          );
        })}

        <g className="strip">
          {series.map((s, r) => {
            const ry = stripTop + r * (rowH + rowGap);
            return (
              <g key={s.key}>
                <text className="strip-label" x={M.left - 8} y={ry + rowH - 2} textAnchor="end">
                  {s.label}
                </text>
                <line className="strip-base" x1={M.left} x2={M.left + plotW} y1={ry + rowH / 2} y2={ry + rowH / 2} />
                {s.states.map((st, k) => {
                  const cx = x(k + 1);
                  if (st === "skipped") return null;
                  if (st === "refused") {
                    const h = rowH / 2 + 1;
                    return (
                      <g key={k} className="strip-refused">
                        <line x1={cx - h} x2={cx + h} y1={ry - 1} y2={ry + rowH + 1} />
                        <line x1={cx - h} x2={cx + h} y1={ry + rowH + 1} y2={ry - 1} />
                      </g>
                    );
                  }
                  return <rect key={k} className={`strip-cell strip-${st}`} x={r1(cx - cw / 2)} y={ry} width={r1(cw)} height={rowH} rx={cw > 6 ? 2 : 0} />;
                })}
              </g>
            );
          })}
        </g>

        {hover != null ? (
          <g className="hover">
            <line className="crosshair" x1={x(hover)} x2={x(hover)} y1={M.top} y2={H - 2} />
            {series.map((s) =>
              s.values[hover] != null ? <circle key={s.key} cx={x(hover)} cy={y(s.values[hover]!)} r={4.5} fill={s.color} stroke="var(--surface)" strokeWidth={2} /> : null,
            )}
          </g>
        ) : null}
      </svg>

      <div className="chart-readout" aria-live="polite">
        <p className="readout-head">
          {hover == null
            ? "After the batch. Hover the chart, or focus it and use the arrow keys, to read each swap."
            : hover === 0
              ? "Start"
              : `After swap ${hover}: ${stepLabels[hover - 1] ?? ""}`}
        </p>
        <dl className="readout-rows">
          {series.map((s) => {
            let amount = "";
            let value = "";
            if (hover == null) {
              amount = s.refusedAt != null ? `reverted at swap ${s.refusedAt}` : "went through";
              value = s.final == null ? "none" : formatPct(s.final);
            } else if (hover === 0) {
              amount = "";
              value = s.values[0] == null ? "none" : formatPct(s.values[0]);
            } else {
              const st = s.states[hover - 1]!;
              const q = s.quotes[hover - 1];
              amount = q != null ? `${what(hover)} ${formatBig(q)}` : STATE_TEXT[st];
              if (q != null && st === "undone") amount += ", undone";
              value = s.values[hover] == null ? "stopped" : formatPct(s.values[hover]!);
            }
            return (
              <div key={s.key}>
                <dt>
                  <i className="legend-line" data-dash={s.dashed} style={{ ["--swatch" as string]: s.color }} aria-hidden="true" />
                  {s.label}
                </dt>
                <dd className="readout-amount">{amount}</dd>
                <dd className="readout-value">{value}</dd>
              </div>
            );
          })}
        </dl>
      </div>
    </div>
  );
}
