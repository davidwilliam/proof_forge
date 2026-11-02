import Link from "next/link";
import type { Metadata } from "next";
import { githubFile } from "@/lib/flagships";
import { MEASURED, REQUIREMENTS, TASK, VERSIONS, statusCounts, type VersionInfo } from "@/lib/swap";
import { shortHash } from "@/lib/format";
import { Status } from "@/components/ui";
import { Seal } from "@/components/Seal";
import { RunStrips, type Strip } from "@/components/FrontierViz";
import { DrainHero } from "./DrainHero";
import { SwapReplay } from "./SwapReplay";
import "./replay.css";

export const metadata: Metadata = {
  title: "Balancer exploit replay, ProofForge",
  description:
    "Replay the November 2025 Balancer V2 rounding exploit on the deployed swap code, the obvious plus-one hotfix and the repair Muse proved with ProofForge.",
};

const usd = (n: number) => `$${n.toFixed(2)}`;

/** One mark per requirement, in the order of the list at the end of the page; shape and text carry the status. */
function ReqMarks({ v, compact = false }: { v: VersionInfo; compact?: boolean }) {
  const c = statusCounts(v);
  return (
    <span
      className={compact ? "req-marks req-marks-compact" : "req-marks"}
      role="img"
      aria-label={`${v.name}: ${c.verified} of ${c.total} requirements proved, ${c.refuted} refuted, ${c.unresolved} not proved`}
    >
      {REQUIREMENTS.map((r) => {
        const s = v.passport.requirements[r.id] ?? "UNRESOLVED";
        return <span key={r.id} className="rm" data-s={s} title={`${r.id}: ${s}`} />;
      })}
    </span>
  );
}

function verdictFigure(v: VersionInfo): string {
  const c = statusCounts(v);
  return v.verdict === "VERIFIED" ? `${c.verified} of ${c.total} proved` : `${c.refuted} of ${c.total} refuted`;
}

function measuredStrip(): Strip {
  const a = MEASURED.alone;
  const f = MEASURED.forge;
  return {
    key: "balancer-task",
    title: "rw-balancer-upscale",
    context: "Muse Spark alone, and Muse with ProofForge and the Muse Wonder planner, on the task behind this page.",
    unit: "run",
    alone: { verified: a.verified, runs: a.runs },
    proofforge: { verified: f.verified, runs: f.runs },
    figure: `${usd(a.usdPerVerified)} → ${usd(f.usdPerVerified)}`,
    figureAlt: "list per verified run",
    stats: [
      { value: `${usd(a.usdTotal)} → ${usd(f.usdTotal)}`, label: "spent over all runs, list prices" },
      { value: `$${MEASURED.capUsd} and ${MEASURED.capHours} hours`, label: "the same caps on every run" },
      { value: `p = ${MEASURED.fisherP}`, label: "one-sided Fisher exact test on the verification rate" },
    ],
    text: `Muse Spark alone verified ${a.verified} of ${a.runs} runs, ${usd(a.usdPerVerified)} list per verified run. Muse with ProofForge and the Muse Wonder planner verified ${f.verified} of ${f.runs} runs, ${usd(f.usdPerVerified)} list per verified run.`,
    note: `Every run had the same caps: $${MEASURED.capUsd} at list prices and ${MEASURED.capHours} hours. The three Muse-alone runs that did not verify ended at a cap with code that passes all ${MEASURED.failedAloneCases.toLocaleString("en-US")} generated property cases and none of the eight requirements proved, so the check reports them UNRESOLVED, not refuted. One-sided Fisher exact test on the verification rate: p = ${MEASURED.fisherP}.`,
    links: [
      { label: "Runs and costs", href: githubFile(MEASURED.source) },
      ...MEASURED.failedAlone.map((p) => ({ label: p.replace(/^results\//, ""), href: githubFile(`${p}/passport.json`) })),
    ],
  };
}

export default function BalancerReplayPage() {
  const alone = MEASURED.alone;
  const forge = MEASURED.forge;
  const repaired = VERSIONS.find((v) => v.key === "repaired")!;
  const rc = statusCounts(repaired);
  return (
    <main id="main" className="page replay">
      <h1>The Balancer V2 rounding exploit, replayed</h1>
      <p className="lead">
        On November 3, 2025, attackers drained Balancer V2 Composable Stable Pools and their forks of more than $120 million (
        <a href="https://www.openzeppelin.com/news/understanding-the-balancer-v2-exploit">OpenZeppelin</a>). A swap for an exact amount out rounded
        that amount down before pricing it, and at balances of a few wei one unit of rounding is a large part of a balance: 17 wei of osETH, worth
        17.988 of the pool&apos;s units, was priced as 17. The obvious fix, adding one unit, stops the drain but overcharges whole amounts and refuses
        valid swaps.
      </p>

      <DrainHero />

      <ul className="kpis replay-kpis" aria-label="The Muse repair and the measured runs in figures">
        <li>
          <a href="#proves">
            <span className="kpi-v">
              {rc.verified} of {rc.total}
            </span>
            <span className="kpi-l">requirements proved by the repair Muse Spark wrote with ProofForge, checked by six kernels</span>
          </a>
        </li>
        <li>
          <a href="#measured">
            <span className="kpi-v">
              {forge.verified} of {forge.runs}
            </span>
            <span className="kpi-l">
              runs verified by Muse with ProofForge, {alone.verified} of {alone.runs} by Muse alone
            </span>
          </a>
        </li>
        <li>
          <a href="#measured">
            <span className="kpi-v">{usd(forge.usdPerVerified)}</span>
            <span className="kpi-l">list per verified run with ProofForge, {usd(alone.usdPerVerified)} alone</span>
          </a>
        </li>
      </ul>

      <section aria-labelledby="versions">
        <h2 id="versions">Three versions of the swap code</h2>
        <p className="section-lead">
          Each version is Lean code compiled to the same <code>swap-sidecar</code> executable and checked against the same eight locked requirements
          of <a href={githubFile(`${TASK}/README.md`)}>rw-balancer-upscale</a>. Only the given-out path differs; the lines below are the difference.
        </p>
        <p className="req-legend small">
          <span>
            The eight squares on each card are the eight requirements, in the order of <a href="#proves">the list at the end of the page</a>.
          </span>
          <span className="req-legend-item">
            <span className="rm" data-s="REFUTED" aria-hidden="true" /> refuted by a kernel-checked counterexample
          </span>
          <span className="req-legend-item">
            <span className="rm" data-s="UNRESOLVED" aria-hidden="true" /> not proved
          </span>
          <span className="req-legend-item">
            <span className="rm" data-s="VERIFIED" aria-hidden="true" /> proved
          </span>
        </p>
        <div className="versions">
          {VERSIONS.map((v) => (
            <article key={v.key} className="card version" data-verdict={v.verdict}>
              <h3>
                <span className="swatch" style={{ ["--swatch" as string]: `var(--series-${v.key})` }} aria-hidden="true" />
                {v.name}
              </h3>
              <p className="origin">{v.origin}</p>
              <pre>
                <code>
                  {v.code.map((l, i) => (
                    <span key={i} className={l.trim().startsWith("--") ? "code-note" : /upscale/.test(l) ? "code-key" : undefined}>
                      {l}
                      {i < v.code.length - 1 ? "\n" : ""}
                    </span>
                  ))}
                </code>
              </pre>
              <div className="version-verdict">
                <ReqMarks v={v} />
                <p className="version-figure">
                  {v.verdict === "VERIFIED" ? <Seal size={26} /> : null}
                  {verdictFigure(v)}
                </p>
              </div>
              <p className="finding">
                The check says <Status value={v.verdict} />. {v.finding}
              </p>
              <p className="links">
                <a href={githubFile(v.passport.path)}>Passport {shortHash(v.passport.sha256)}</a>
                {v.counterexamples.map((c) => (
                  <a key={c.path} href={githubFile(c.path)}>
                    {c.label}
                  </a>
                ))}
                <a href={githubFile(v.source)}>source</a>
              </p>
            </article>
          ))}
        </div>
      </section>

      <section aria-labelledby="replay">
        <h2 id="replay">Replay a batch on all three</h2>
        <p className="section-lead">
          Pick a batch and run it. The server runs it through the executable built from each version and reports, after every swap, the amount
          charged and the pool&apos;s value: the invariant of its balances, which for a Composable Stable Pool is the D behind the BPT price. A
          batch with a refused swap reverts as a whole, as Balancer&apos;s <code>batchSwap</code> does.
        </p>
        <SwapReplay />
      </section>

      <section aria-labelledby="measured" id="measured-section">
        <h2 id="measured">Muse alone and Muse with ProofForge on this task</h2>
        <p className="section-lead">
          Each dot is one run, filled when it ended with a <Status value="VERIFIED" /> Passport. The Muse-alone runs that did not verify are{" "}
          <Status value="UNRESOLVED" />, not refuted: their code passes all {MEASURED.failedAloneCases.toLocaleString("en-US")} generated property
          cases and proves none of the eight requirements.
        </p>
        <RunStrips items={[measuredStrip()]} />
      </section>

      <section aria-labelledby="proves">
        <h2 id="proves">What the Muse repair proves</h2>
        <p className="section-lead">
          For any pool math that meets the contract stated in the specification. The constant-product math is proved to meet it; StableMath is not,
          so the StableMath replays above are tested, not proved.
        </p>
        <ol className="reqs">
          {REQUIREMENTS.map((r, k) => (
            <li key={r.id}>
              <p className="req-head">
                <span className="req-n" aria-hidden="true">
                  {k + 1}
                </span>
                <code>{r.id}</code>
              </p>
              <p className="req-text">{r.text}</p>
              <ul className="req-status" aria-label={`${r.id} in each version's Passport`}>
                {VERSIONS.map((v) => {
                  const s = v.passport.requirements[r.id] ?? "UNRESOLVED";
                  return (
                    <li key={v.key}>
                      <span className="rm" data-s={s} aria-hidden="true" />
                      <span>
                        {v.short} <span className="req-s">{s === "VERIFIED" ? "proved" : s === "REFUTED" ? "refuted" : "not proved"}</span>
                      </span>
                    </li>
                  );
                })}
              </ul>
            </li>
          ))}
        </ol>
      </section>

      <p className="replay-foot">
        The earlier demo, splitting a payout on a buggy and a repaired build, is at <Link href="/app/payout">/app/payout</Link>.
      </p>
    </main>
  );
}
