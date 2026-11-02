"use client";

import Link from "next/link";
import { useEffect, useRef, useState, type KeyboardEvent } from "react";
import type { Passport } from "@/lib/api";
import type { Timeline } from "@/lib/forge-view";
import { formatDuration, formatInt, formatUsd, modelInfo, shortHash } from "@/lib/format";
import type { RecordingFacts } from "@/lib/recordings";
import { Seal } from "@/components/Seal";
import { Status } from "@/components/ui";

/** One square per requirement; the shape carries the state, colour only repeats it. */
export function ReqMarks({ marks, label }: { marks: { id: string; mark: string; word: string }[]; label: string }) {
  return (
    <span className="fs-marks" role="img" aria-label={label}>
      {marks.map((m) => (
        <span key={`${m.id}-${m.mark}`} className="fs-sq" data-mark={m.mark} title={`${m.id}: ${m.word}`} />
      ))}
    </span>
  );
}

const reducedMotion = () => typeof window !== "undefined" && !!window.matchMedia?.("(prefers-reduced-motion: reduce)").matches;

/** A counter that eases to its new value; it jumps when the viewer prefers reduced motion. */
export function CountUp({ value }: { value: number }) {
  const [shown, setShown] = useState(value);
  const from = useRef(value);
  useEffect(() => {
    if (reducedMotion() || from.current === value) {
      from.current = value;
      setShown(value);
      return;
    }
    const a = from.current;
    const t0 = performance.now();
    let raf = 0;
    const step = (t: number) => {
      const k = Math.min(1, (t - t0) / 380);
      const v = Math.round(a + (value - a) * (1 - (1 - k) ** 3));
      from.current = v;
      setShown(v);
      if (k < 1) raf = requestAnimationFrame(step);
    };
    raf = requestAnimationFrame(step);
    return () => cancelAnimationFrame(raf);
  }, [value]);
  return <>{formatInt(shown)}</>;
}

/** A recorded session on the start screen: who worked, how long, and how far it got in session. */
export function RecordingCard({
  id,
  facts,
  requirements,
  selected,
  speed,
  disabled,
  onReplay,
}: {
  id: string;
  facts: RecordingFacts | null;
  requirements: { id: string; theorem: string }[];
  selected: boolean;
  speed: number;
  disabled: boolean;
  onReplay: () => void;
}) {
  const reqOf = (theorem: string) => requirements.find((r) => r.theorem.endsWith(`.${theorem}`))?.id ?? theorem;
  const openIds = facts ? new Set(facts.open.map(reqOf)) : new Set<string>();
  const model = facts ? modelInfo(facts.model).name : null;
  const planner = facts?.planner ? modelInfo(facts.planner).name : null;
  return (
    <li className="fs-rec" data-selected={selected ? "" : undefined}>
      <div className="fs-rec-head">
        <h3 className="mono">{id}</h3>
        {facts ? (
          <p className="fs-rec-who">
            {model} as repairer and prover{planner ? `, ${planner} as lemma planner` : ""}, task {facts.task}, arm {facts.arm}
          </p>
        ) : null}
      </div>
      {facts ? (
        <>
          <div className="fs-rec-proof">
            <span className="fs-rec-big">
              {facts.proved}
              <span> of {facts.theorems}</span>
            </span>
            <span className="fs-rec-proof-text">
              <ReqMarks
                marks={requirements.map((r) => ({ id: r.id, mark: openIds.has(r.id) ? "pending" : "proved", word: openIds.has(r.id) ? "open" : "proved in session" }))}
                label={`${facts.proved} of ${facts.theorems} requirements proved in session`}
              />
              <span>
                requirements proved in session
                {facts.acceptedInSession
                  ? `; the in-session judge accepted version ${facts.versions}`
                  : `; ${[...openIds].join(", ")} open when the session ended`}
              </span>
            </span>
          </div>
          <dl className="fs-rec-stats">
            <div>
              <dt>model turns</dt>
              <dd>{formatInt(facts.turns)}</dd>
            </div>
            <div>
              <dt>tool calls</dt>
              <dd className={facts.toolCalls == null ? "fs-none" : undefined}>{facts.toolCalls == null ? "not recorded" : formatInt(facts.toolCalls)}</dd>
            </div>
            <div>
              <dt>versions</dt>
              <dd>{formatInt(facts.versions)}</dd>
            </div>
            <div>
              <dt>recorded time</dt>
              <dd>{formatDuration(facts.elapsedS)}</dd>
            </div>
          </dl>
          {facts.usdList != null || facts.evidence ? (
            <p className="fs-rec-note">
              {facts.usdList != null ? `Model spend ${formatUsd(facts.usdList)} at list price, ${formatUsd(facts.usdBilled)} billed.` : ""}
              {facts.evidence ? (
                <>
                  Evidence in <code>{facts.evidence}</code>.
                </>
              ) : null}
            </p>
          ) : null}
        </>
      ) : null}
      <button className={selected ? "primary" : undefined} onClick={onReplay} disabled={disabled}>
        Replay at {speed}x
      </button>
    </li>
  );
}

/** The verdict of the fresh check, with what it checked and the hashes that pin it. */
export function PassportCard({
  summary,
  passport,
}: {
  summary: { sha: string; status: string; requirements: Record<string, string> };
  passport: Passport | null;
}) {
  const kernels = passport?.checks.comparator_kernels ?? [];
  const pt = passport?.checks.property_tests;
  const violations = pt?.violations ? Object.values(pt.violations).reduce((a, b) => a + b, 0) : null;
  return (
    <section className="fs-passport" data-status={summary.status} aria-label="Passport from the fresh check">
      <div className="fs-pp-head">
        <Seal size={52} lit={kernels.length} />
        <div>
          <p className="fs-pp-title">Passport from the fresh check</p>
          <p className="fs-pp-status">
            Component <Status value={summary.status} />
          </p>
        </div>
      </div>
      {passport ? (
        <dl className="fs-pp-facts">
          <div>
            <dt>Kernels accepted</dt>
            <dd>
              {kernels.length ? kernels.length : "none"}
              {kernels.length ? <span className="fs-pp-sub">{kernels.join(", ")}</span> : null}
            </dd>
          </div>
          <div>
            <dt>Property cases</dt>
            <dd>
              {formatInt(pt?.cases)}
              {pt?.followup_cases != null ? <span className="fs-pp-sub">and {formatInt(pt.followup_cases)} follow-up cases, {formatInt(violations)} violations</span> : null}
            </dd>
          </div>
          <div>
            <dt>Proof check</dt>
            <dd>
              {passport.proof_check.accepted ? "accepted" : "not accepted"}
              {passport.proof_check.reasons.length ? <span className="fs-pp-sub mono">{passport.proof_check.reasons.join("; ")}</span> : null}
            </dd>
          </div>
          <div>
            <dt>Executable</dt>
            <dd>
              <Status value={passport.executable.status} />
              <span className="fs-pp-sub">{passport.toolchain.lean}</span>
            </dd>
          </div>
          <div className="fs-pp-hashes">
            <dt>Hashes</dt>
            <dd>
              <span>Passport</span>
              <span className="hash">{shortHash(passport.passport_sha256, 12)}</span>
              <span>Solution tree</span>
              <span className="hash">{shortHash(passport.solution.solution_tree_sha256, 12)}</span>
              <span>Manifest</span>
              <span className="hash">{shortHash(passport.locked.manifest_sha256, 12)}</span>
              <span>Executable</span>
              <span className="hash">{shortHash(passport.executable.sha256, 12)}</span>
            </dd>
          </div>
        </dl>
      ) : null}
      <Link className="fs-pp-link" href={`/passport/${summary.sha}`}>
        Open Passport {shortHash(summary.sha)}
      </Link>
    </section>
  );
}

const W = 300;
const H = 146;
const TOP = 14;
const BASE = 100;
const LEFT = 4;
const SERIES = [
  ["turns", "model turns"],
  ["tools", "tool calls"],
  ["versions", "versions"],
] as const;

const minutes = (s: number) => formatDuration(s);

/** Model turns, tool calls and versions over recorded time, with the moment each requirement was proved. */
export function ActivityTimeline({ timeline, hasTools, recorded }: { timeline: Timeline | null; hasTools: boolean; recorded: boolean }) {
  const [active, setActive] = useState<number | null>(null);
  if (!timeline) {
    return (
      <figure className="fs-tl">
        <figcaption className="fs-tl-cap">Recorded timeline</figcaption>
        <div className="fs-tl-empty">The timeline fills in as the replay runs.</div>
        <p className="fs-tl-readout">Each bar will show the model turns, tool calls and versions of one slice of the recorded session.</p>
      </figure>
    );
  }
  const n = timeline.bins.length;
  const bw = (W - LEFT) / n;
  const y = (v: number) => Math.round(((BASE - TOP) * v) / timeline.max * 10) / 10;
  const nowX = Math.round((LEFT + ((W - LEFT) * timeline.now) / timeline.span) * 10) / 10;
  const totals = timeline.bins.reduce((a, b) => ({ turns: a.turns + b.turns, tools: a.tools + b.tools, versions: a.versions + b.versions }), { turns: 0, tools: 0, versions: 0 });
  const onKey = (e: KeyboardEvent) => {
    if (e.key === "ArrowRight" || e.key === "ArrowLeft") {
      e.preventDefault();
      setActive((a) => Math.max(0, Math.min(n - 1, (a ?? (e.key === "ArrowRight" ? -1 : n)) + (e.key === "ArrowRight" ? 1 : -1))));
    } else if (e.key === "Escape") setActive(null);
  };
  const b = active != null ? timeline.bins[active]! : null;
  return (
    <figure className="fs-tl">
      <figcaption className="fs-tl-cap">
        Recorded timeline, {minutes(timeline.span)}
        {recorded ? "" : " so far"}
      </figcaption>
      <ul className="fs-tl-legend" aria-label="Legend">
        {SERIES.map(([k, l]) => (
          <li key={k}>
            <span className="fs-tl-key" data-series={k} />
            {l}
            {k === "tools" && !hasTools ? " (not recorded)" : ""}
          </li>
        ))}
        <li>
          <span className="fs-tl-key" data-series="proved" />
          requirement proved
        </li>
      </ul>
      <svg
        className="fs-tl-svg"
        viewBox={`0 0 ${W} ${H}`}
        tabIndex={0}
        role="img"
        aria-label={`Activity over ${minutes(timeline.span)} of recorded time: ${totals.turns} model turns, ${totals.tools} tool calls, ${totals.versions} versions. Use the arrow keys to read each slice.`}
        onKeyDown={onKey}
        onMouseLeave={() => setActive(null)}
        onBlur={() => setActive(null)}
      >
        <line className="fs-tl-grid" x1={LEFT} x2={W} y1={TOP} y2={TOP} />
        <text className="fs-tl-tick" x={W} y={TOP - 4} textAnchor="end">
          {timeline.max} per slice
        </text>
        <rect className="fs-tl-future" x={Math.min(W, nowX)} y={TOP} width={Math.max(0, W - nowX)} height={BASE - TOP} />
        {timeline.bins.map((bin, i) => {
          const x = Math.round((LEFT + i * bw + 0.6) * 10) / 10;
          const w = Math.max(1, Math.round((bw - 1.2) * 10) / 10);
          let acc = 0;
          return (
            <g key={i} data-active={active === i ? "" : undefined} onMouseEnter={() => setActive(i)}>
              <rect className="fs-tl-hit" x={Math.round((LEFT + i * bw) * 10) / 10} y={TOP} width={Math.round(bw * 10) / 10} height={H - TOP} />
              {SERIES.map(([k]) => {
                const v = bin[k];
                if (!v) return null;
                const h = y(v);
                acc += h;
                return <rect key={k} className="fs-tl-bar" data-series={k} x={x} y={Math.round((BASE - acc) * 10) / 10} width={w} height={h} />;
              })}
              {bin.proved.map((rid, j) => {
                const cx = Math.round((x + w / 2 + (j % 2 ? 3.5 : -3.5) * (bin.proved.length > 1 ? 1 : 0)) * 10) / 10;
                const cy = BASE + 10 + Math.floor(j / 2) * 7;
                return <rect key={rid} className="fs-tl-proved" x={cx - 2.5} y={cy - 2.5} width={5} height={5} transform={`rotate(45 ${cx} ${cy})`} />;
              })}
            </g>
          );
        })}
        <line className="fs-tl-base" x1={LEFT} x2={W} y1={BASE} y2={BASE} />
        {timeline.now < timeline.span ? <line className="fs-tl-now" x1={nowX} x2={nowX} y1={TOP - 2} y2={BASE + 2} /> : null}
        <text className="fs-tl-tick" x={LEFT} y={H - 2}>
          0
        </text>
        <text className="fs-tl-tick" x={W} y={H - 2} textAnchor="end">
          {minutes(timeline.span)}
        </text>
      </svg>
      <p className="fs-tl-readout" aria-live="polite">
        {b ? (
          <>
            <strong>
              {minutes(b.from)} to {minutes(b.to)}
            </strong>
            : {b.turns} model turns, {hasTools ? `${b.tools} tool calls` : "tool calls not recorded"}, {b.versions} versions
            {b.proved.length ? `; ${b.proved.join(", ")} proved in session` : ""}.
          </>
        ) : (
          <>
            {formatInt(totals.turns)} model turns, {hasTools ? `${formatInt(totals.tools)} tool calls` : "tool calls not recorded"} and {formatInt(totals.versions)} versions over{" "}
            {minutes(timeline.now)} of recorded time. Point at a bar, or focus the chart and use the arrow keys.
          </>
        )}
      </p>
    </figure>
  );
}
