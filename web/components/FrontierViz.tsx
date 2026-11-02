import { DIMENSIONS, type Catches, type Dimension, type Outcome, type WinsData } from "@/lib/wins";

export interface StripArm {
  verified: number;
  runs: number;
}

export interface Strip {
  key: string;
  title: string;
  context: string;
  /** What one dot is: a run, or a task with one run per arm. */
  unit: "run" | "task";
  alone: StripArm;
  proofforge: StripArm;
  figure: string;
  figureAlt: string;
  stats: { value: string; label: string }[];
  text: string;
  note: string;
  links: { label: string; href: string }[];
}

function Dots({ arm, unit }: { arm: StripArm; unit: Strip["unit"] }) {
  return (
    <span className={`strip-dots strip-dots-${arm.runs > 20 ? "dense" : "wide"}`} aria-hidden="true">
      {Array.from({ length: arm.runs }, (_, i) => (
        <span key={i} className={i < arm.verified ? "sd sd-on" : "sd"} data-unit={unit} />
      ))}
    </span>
  );
}

/** The headline experiments as runs: one dot per run (or per task), filled when it ended with a VERIFIED Passport. */
export function RunStrips({ items }: { items: Strip[] }) {
  return (
    <ol className="strips" aria-label="The largest gains, run by run">
      {items.map((s) => {
        const noun = s.unit === "run" ? "runs" : "tasks";
        return (
          <li key={s.key} className="strip" id={`gain-${s.key}`}>
            <div className="strip-head">
              <h3>{s.title}</h3>
              <p className="strip-context">{s.context}</p>
            </div>
            <div className="strip-rows">
              {(
                [
                  ["On its own", s.alone, "alone"],
                  ["With ProofForge", s.proofforge, "pf"],
                ] as const
              ).map(([label, arm, k]) => (
                <div key={k} className={`strip-row strip-row-${k}`} role="img" aria-label={`${label}: ${arm.verified} of ${arm.runs} ${noun} verified`}>
                  <span className="strip-arm">{label}</span>
                  <Dots arm={arm} unit={s.unit} />
                  <span className="strip-count">
                    {arm.verified} <span>of {arm.runs}</span>
                  </span>
                </div>
              ))}
            </div>
            <p className="strip-figure">
              <span className="strip-big">{s.figure}</span>
              <span className="strip-alt">{s.figureAlt}</span>
            </p>
            <dl className="strip-stats">
              {s.stats.map((x) => (
                <div key={x.label}>
                  <dt>{x.label}</dt>
                  <dd>{x.value}</dd>
                </div>
              ))}
            </dl>
            <details className="strip-more">
              <summary>What was measured</summary>
              <p>{s.text}</p>
              <p>{s.note}</p>
              <p className="win-links">
                {s.links.map((l) => (
                  <a key={l.href} href={l.href}>
                    {l.label}
                  </a>
                ))}
              </p>
            </details>
          </li>
        );
      })}
    </ol>
  );
}

/** The ledger's totals as figures. */
export function KpiStrip({ d }: { d: WinsData }) {
  const c = d.counts;
  const items = [
    { value: c.runs.toLocaleString("en-US"), label: "measured runs" },
    { value: String(c.comparisons), label: "comparisons, same model and caps" },
    { value: String(c.wins_group_1), label: "verified only with ProofForge", href: "#group-1" },
    { value: String(c.wins_group_2), label: "verified either way, cheaper or faster with ProofForge", href: "#group-2" },
    { value: String(c.wins_group_3), label: "gains of other kinds", href: "#group-3" },
  ];
  return (
    <ul className="kpis" aria-label="The ledger in figures">
      {items.map((k) => (
        <li key={k.label}>
          {k.href ? (
            <a href={k.href}>
              <span className="kpi-v">{k.value}</span>
              <span className="kpi-l">{k.label}</span>
            </a>
          ) : (
            <>
              <span className="kpi-v">{k.value}</span>
              <span className="kpi-l">{k.label}</span>
            </>
          )}
        </li>
      ))}
    </ul>
  );
}

const SEGMENTS: { o: Outcome; label: string }[] = [
  { o: "win", label: "Better" },
  { o: "tie", label: "Same" },
  { o: "loss", label: "Worse" },
  { o: "n/a", label: "Not applicable" },
];

/** Each dimension as one bar over all comparisons, ordered by the share better with ProofForge. */
export function DimensionBars({ d }: { d: WinsData }) {
  const cls = d.counts.classification;
  const total = d.counts.comparisons;
  const ratio = (k: Dimension) => cls[k].win / Math.max(1, cls[k].win + cls[k].loss);
  const dims = [...DIMENSIONS].sort((a, b) => ratio(b.key) - ratio(a.key));
  return (
    <div className="dimbars">
      <ul className="dimbars-legend" aria-hidden="true">
        {SEGMENTS.map((s) => (
          <li key={s.o}>
            <span className="dimbar-key" data-outcome={s.o} />
            {s.label}
          </li>
        ))}
      </ul>
      {dims.map((dim) => {
        const v = cls[dim.key];
        const head = v.win + v.loss ? Math.round((100 * v.win) / (v.win + v.loss)) : 0;
        return (
          <div key={dim.key} className="dimbar">
            <p className="dimbar-label">
              <span>{dim.label}</span>
              <span className="dimbar-share">
                better in {v.win}, worse in {v.loss}
                {v.win + v.loss ? ` (${head}% of those that differ)` : ""}
              </span>
            </p>
            <div className="dimbar-track" role="img" aria-label={`${dim.label}: better ${v.win}, same ${v.tie}, worse ${v.loss}, not applicable ${v["n/a"]} of ${total}`}>
              {SEGMENTS.map((s) =>
                v[s.o] ? (
                  <span key={s.o} className="dimbar-seg" data-outcome={s.o} style={{ flexGrow: v[s.o] }} title={`${s.label}: ${v[s.o]}`}>
                    {v[s.o] / total >= 0.06 ? v[s.o] : ""}
                  </span>
                ) : null,
              )}
            </div>
          </div>
        );
      })}
    </div>
  );
}

/**
 * The E2 attacks: one dot per seeded bad candidate, filled when the check accepted it. Only the
 * bad-case counts are read, so the /results page can pass figures aggregated from GET /api/results.
 */
export function CatchWaffles({ e }: { e: Pick<Catches, "badCases" | "badAccepted"> }) {
  const panels = [
    { label: "Ordinary checking", sub: "the build passes, the theorem names exist, the axioms are clean", n: e.badAccepted.ordinary },
    { label: "Rebuild and property tests", sub: "the executable rebuilt from the file, with the property tests", n: e.badAccepted.rebuildAndTests },
    { label: "ProofForge", sub: "locked statements, six kernels, leanchecker, axiom audit, rebuild and property tests", n: e.badAccepted.proofforge },
  ];
  return (
    <ul className="waffles" aria-label="Seeded bad candidates accepted">
      {panels.map((p, i) => (
        <li key={p.label} className={i === panels.length - 1 ? "waffle waffle-pf" : "waffle"}>
          <p className="waffle-figure">
            <span className="strip-big">{p.n}</span> <span className="strip-alt">of {e.badCases} accepted</span>
          </p>
          <span className="waffle-grid" role="img" aria-label={`${p.label}: ${p.n} of ${e.badCases} bad candidates accepted`}>
            {Array.from({ length: e.badCases }, (_, k) => (
              <span key={k} className={k < p.n ? "wd wd-on" : "wd"} />
            ))}
          </span>
          <p className="waffle-label">{p.label}</p>
          <p className="waffle-sub">{p.sub}</p>
        </li>
      ))}
    </ul>
  );
}
