import type { Metadata } from "next";
import { KpiStrip } from "@/components/FrontierViz";
import { inlineCode } from "@/components/InlineCode";
import { githubFile } from "@/lib/flagships";
import { METHODS, byGain, commitUrl, methodsCounts, pooledSentence, resultSentence, taskModel, type MethodsArm, type Preregistration } from "@/lib/methods";
import "./methods.css";

const counts = methodsCounts(METHODS);
const description = `Every preregistered ProofForge experiment: ${counts.plans} plans committed before their first run, ${counts.runs} runs fixed in advance, each with its question, commit, primary test, status and result.`;

export const metadata: Metadata = {
  title: "Preregistrations and methods, ProofForge",
  description,
  openGraph: { title: "Preregistrations and methods, ProofForge", description },
};

const md = inlineCode;

const longDay = (iso: string) =>
  new Date(`${iso}T00:00:00Z`).toLocaleDateString("en-GB", { day: "numeric", month: "short", timeZone: "UTC" });

function Dots({ arm }: { arm: MethodsArm }) {
  return (
    <span className="strip-dots strip-dots-wide" aria-hidden="true">
      {Array.from({ length: arm.runs }, (_, i) => (
        <span key={i} className={i < arm.verified ? "sd sd-on" : "sd"} />
      ))}
    </span>
  );
}

function Result({ e }: { e: Preregistration }) {
  const tasks = byGain(e.tasks);
  return (
    <div className="mt-result">
      {tasks.map((c) => (
        <div className="mt-task" key={c.id}>
          <p className="mt-task-name">
            <code>{c.task}</code>
            <span className="muted">, {taskModel(c)} in Muse Code</span>
          </p>
          <div className="mt-rows">
            {(
              [
                ["With ProofForge", c.proofforge, "pf"],
                ["On its own", c.alone, "alone"],
              ] as const
            ).map(([label, arm, k]) => (
              <div key={k} className={`strip-row strip-row-${k}`} role="img" aria-label={`${label}: ${arm.verified} of ${arm.runs} runs verified`}>
                <span className="strip-arm">{label}</span>
                <Dots arm={arm} />
                <span className="strip-count">
                  {arm.verified} <span>of {arm.runs}</span>
                </span>
              </div>
            ))}
          </div>
          <p className="mt-sentence">{resultSentence(c)}</p>
        </div>
      ))}
      {e.pooled.map((c) => (
        <p className="mt-pooled" key={c.id}>
          Pooled ({c.id}): {pooledSentence(c)}
        </p>
      ))}
    </div>
  );
}

function Entry({ e, n, lead }: { e: Preregistration; n: number; lead: boolean }) {
  const best = byGain(e.tasks)[0];
  return (
    <li className={`mt-entry mt-${e.status}${lead ? " mt-lead" : ""}`} id={e.id}>
      <header className="mt-head">
        <span className="mt-n" aria-hidden="true">
          {n}
        </span>
        <div className="mt-title">
          <h2>{e.id}</h2>
          <p className="mt-meta">
            Written {e.written}, committed in <a href={commitUrl(e.commitFull)}>{e.commit}</a> before its first run
          </p>
        </div>
        <p className={`mt-status mt-status-${e.status}`}>
          <span className="mt-status-mark" aria-hidden="true" />
          {e.label}
        </p>
        {best ? (
          <p className="mt-big">
            <span className="strip-big">
              {best.alone.verified} → {best.proofforge.verified}
            </span>
            <span className="strip-alt">runs verified, on its own → with ProofForge</span>
          </p>
        ) : null}
      </header>

      {e.status === "finished" ? <Result e={e} /> : <p className="mt-note">{md(e.note)}</p>}

      <div className="mt-question">
        <h3>Question</h3>
        <p>{md(e.question)}</p>
      </div>

      <dl className="mt-facts">
        <div>
          <dt>Runs fixed in advance</dt>
          <dd>{e.runs}</dd>
        </div>
        <div>
          <dt>Primary test</dt>
          <dd className="mt-dd-text">{e.testName}</dd>
        </div>
        <div>
          <dt>Plan commit</dt>
          <dd>
            <a href={commitUrl(e.commitFull)} className="hash">
              {e.commit}
            </a>
          </dd>
        </div>
        <div>
          <dt>Addenda</dt>
          <dd>{e.addenda.length}</dd>
        </div>
      </dl>

      <details className="mt-more">
        <summary>The plan in full</summary>
        {e.questionMore.map((p, i) => (
          <p key={i}>{md(p)}</p>
        ))}
        <p>
          <strong>Runs.</strong> {md(e.runsText)}
        </p>
        <p>
          <strong>Primary analysis.</strong> {md(e.primaryTest.replace(/^Primary analysis[^:]*:\s*/, ""))}
        </p>
        {e.addenda.length ? (
          <ul>
            {e.addenda.map((a) => (
              <li key={a}>{a}</li>
            ))}
          </ul>
        ) : null}
        {e.status === "finished" ? <p className="muted">{md(e.note)}</p> : null}
      </details>

      <p className="win-links mt-links">
        <a href={githubFile(e.prereg)}>Preregistration</a>
        {e.readme ? <a href={githubFile(e.readme)}>Results README</a> : null}
        <a href={commitUrl(e.commitFull)}>Commit {e.commit}</a>
      </p>
    </li>
  );
}

const gain = (e: Preregistration) => {
  const b = byGain(e.tasks)[0];
  return b ? b.proofforge.verified - b.alone.verified : -1;
};
const bestP = (e: Preregistration) => Math.min(1, ...e.tasks.map((c) => c.test?.p ?? 1));
/** The plans, largest gain first, then the smaller p; the first carries the page's one Forge accent. */
const ORDERED = [...METHODS.entries].sort((a, b) => gain(b) - gain(a) || bestP(a) - bestP(b));
const leadId = ORDERED[0]?.id;

export default function MethodsPage() {
  const d = METHODS;
  return (
    <main id="main" className="page methods-page">
      <h1>Preregistrations and methods</h1>
      <p className="lead">
        Every experiment below was planned in a file committed before its first run: the question, the arms, the caps, the number of runs and
        the primary test. A plan changes only through dated addenda, and every run is reported whatever its outcome. Results come from each
        experiment&apos;s README and the wins ledger, with the largest gain for ProofForge first.
      </p>
      <KpiStrip
        label="The preregistrations in figures"
        items={[
          { value: String(counts.plans), label: "plans committed before their runs" },
          { value: String(counts.runs), label: "runs fixed in advance" },
          { value: String(counts.finished), label: "finished, with every run reported", href: "#plans" },
          ...(counts.running ? [{ value: String(counts.running), label: "running now" }] : []),
          ...(counts.queued ? [{ value: String(counts.queued), label: "queued" }] : []),
        ]}
      />

      <nav className="mt-rail" aria-label="The preregistrations, largest gain first">
        <ol>
          {ORDERED.map((e) => (
            <li key={e.id} className={`mt-rail-${e.status}`}>
              <a href={`#${e.id}`}>
                <span className="mt-rail-mark" aria-hidden="true" />
                <span className="mt-rail-id">{e.id}</span>
                <span className="mt-rail-meta">
                  {longDay(e.written)}, {e.label.toLowerCase()}
                </span>
              </a>
            </li>
          ))}
        </ol>
      </nav>

      <ol className="mt-list" id="plans" aria-label="Preregistrations">
        {ORDERED.map((e, i) => (
          <Entry key={e.id} e={e} n={i + 1} lead={e.id === leadId} />
        ))}
      </ol>

      <p className="muted small mt-source">
        Generated by <code>{d.generator}</code> from <code>{d.source}</code>, the experiments&apos; READMEs and <code>{d.ledger}</code>. An
        experiment without a README result shows its status as of {d.asOf}.
      </p>
    </main>
  );
}
