import Link from "next/link";
import { Pipeline } from "@/components/Pipeline";
import { Status } from "@/components/ui";
import { E1, E2 } from "@/lib/evidence";
import { readRealworld, readRepairedPassport } from "@/lib/generated";
import { EXPECTED_PROJECTS, describeInput, listWords, pendingProjects, type RwProject, type RwVersion } from "@/lib/realworld";

const fmt = (n: number) => n.toLocaleString("en-US");

// formal/task.json (issue): the flagship's buggy split; "The existing unit tests pass, but ... cents disappear."
const BUGGY_SPLIT = [33, 33, 33];
// formal/evidence/muse-repair-002/provenance.json: "$1.00 to 3 recipients -> 34 + 33 + 33"
const REPAIRED_SPLIT = [34, 33, 33];
const TOTAL = 100;

export default function Home() {
  const passport = readRepairedPassport();
  const rw = readRealworld();
  return (
    <main className="page home">
      <section className="home-hero" aria-labelledby="home-title">
        <div className="home-hero-text">
          <h1 id="home-title">AI repairs to payment code, accepted only with a Lean proof</h1>
          <p className="home-problem">
            Code that splits money can lose a cent while every share looks right, and the usual checks still pass.
          </p>
          <p className="home-sub">
            A Meta Muse Spark agent repairs Lean 4 payment and accounting code and proves each locked requirement. ProofForge checks the
            result in a fresh sandbox and issues a Passport: <Status value="VERIFIED" />, <Status value="REFUTED" /> or{" "}
            <Status value="UNRESOLVED" />.
          </p>
          <KeyFigures />
          <div className="home-actions">
            <Link className="btn btn-primary" href="/forge">
              Open the live forge session
            </Link>
            <Link className="btn" href="/results">
              Read the results
            </Link>
          </div>
        </div>
        <SplitExample />
      </section>

      <section className="home-band" aria-labelledby="home-steps">
        <div className="home-steps card">
          <div className="home-steps-intro">
            <h2 id="home-steps">How a repair counts</h2>
            <p>The agent writes the repair and its proofs. It never decides whether the repair is accepted.</p>
          </div>
          <div className="home-steps-body">
            <Pipeline className="pipeline-lg" />
            <p className="home-steps-detail">
              The check runs a tree check, an implementation scan, a fresh project, <code>lake comparator --paranoid</code> with six
              kernels, leanchecker and an axiom audit, then rebuilds the executable and runs property tests.
            </p>
          </div>
        </div>
      </section>

      <section className="home-section" aria-labelledby="home-evidence">
        <h2 id="home-evidence">What the measurements show</h2>
        <div className="home-evidence">
          <E2Card />
          <E1Card />
        </div>
      </section>

      <RealWorld projects={rw.projects} pending={pendingProjects(rw)} />

      <section className="home-section" aria-labelledby="home-next">
        <h2 id="home-next">Check the evidence yourself</h2>
        <div className="home-ctas">
          <Link className="home-cta" href="/forge">
            <strong>Open the live forge session</strong>
            <span>Replay a recorded Muse Spark repair, then watch a fresh check of its final candidate assign every status.</span>
          </Link>
          <Link className="home-cta" href={passport ? `/passport/${passport.passport_sha256}` : "/forge"}>
            <strong>Open a Passport</strong>
            <span>
              {passport
                ? "The Passport for the stored Muse Spark repair of the payout splitter: statuses, hashes, kernels, axioms and the command that reproduces it."
                : "Run the forge session to the end; its Passport lists statuses, hashes, kernels, axioms and the command that reproduces it."}
            </span>
          </Link>
          <Link className="home-cta" href="/results">
            <strong>Read the results</strong>
            <span>E1 and E2 per arm, per task family and per case, with the seeded attacks named.</span>
          </Link>
        </div>
      </section>
    </main>
  );
}

/** Three headline figures, each restated with its context in the evidence section below. */
function KeyFigures() {
  const arm = (k: string) => E2.arms.find((a) => a.key === k)!;
  const harness = E1.arms.find((a) => a.key === "A1")!;
  return (
    <dl className="key-figures">
      <div>
        <dt>
          {arm("ordinary").badAccepted} <span>of {E2.bad}</span>
        </dt>
        <dd>seeded bad repairs pass ordinary checking</dd>
      </div>
      <div>
        <dt>
          {arm("proofforge").badAccepted} <span>of {E2.bad}</span>
        </dt>
        <dd>
          pass ProofForge; it rejects {arm("proofforge").goodRejected} of {E2.good} correct ones
        </dd>
      </div>
      <div>
        <dt>
          {harness.completed} <span>of {E1.tasks}</span>
        </dt>
        <dd>frozen test tasks repaired by Muse Spark with the harness</dd>
      </div>
    </dl>
  );
}

function Shares({ values, highlight }: { values: readonly number[]; highlight?: number }) {
  return (
    <span className="shares">
      {values.map((v, i) => (
        <span key={i} className="share" data-highlight={i === highlight ? "true" : undefined}>
          {v}
        </span>
      ))}
    </span>
  );
}

function SplitExample() {
  const buggyTotal = BUGGY_SPLIT.reduce((a, b) => a + b, 0);
  return (
    <figure className="home-split card" aria-labelledby="split-caption">
      <figcaption id="split-caption">Splitting {TOTAL} cents among 3 parties</figcaption>
      <div className="split-row" data-outcome="bad">
        <div className="split-label">Code under repair</div>
        <div className="split-values">
          <Shares values={BUGGY_SPLIT} />
          <span className="split-total">= {buggyTotal}</span>
          <span className="split-verdict">
            ProofForge <Status value="REFUTED" />
          </span>
        </div>
        <p className="split-note">One cent is lost. Each share is within a cent of a third, and the existing unit tests pass.</p>
      </div>
      <div className="split-row" data-outcome="ok">
        <div className="split-label">Muse Spark 1.3 repair</div>
        <div className="split-values">
          <Shares values={REPAIRED_SPLIT} highlight={0} />
          <span className="split-total">= {REPAIRED_SPLIT.reduce((a, b) => a + b, 0)}</span>
          <span className="split-verdict">
            ProofForge <Status value="VERIFIED" />
          </span>
        </div>
        <p className="split-note">The proved specification requires shares that add up to the total and differ by at most one.</p>
      </div>
    </figure>
  );
}

function Bar({ label, detail, count, of, tone }: { label: string; detail?: string; count: number; of: number; tone: "bad" | "accent" }) {
  const pct = of ? (100 * count) / of : 0;
  return (
    <li className="bar-row">
      <div className="bar-label">
        <span>{label}</span>
        {detail ? <span className="bar-detail">{detail}</span> : null}
      </div>
      <div className="bar-figure">
        <span className="bar-track" aria-hidden="true">
          <span className="bar-fill" data-tone={tone} style={{ width: `${pct}%` }} />
        </span>
        <span className="bar-count">
          <strong>{count}</strong> of {of}
        </span>
      </div>
    </li>
  );
}

function E2Card() {
  return (
    <article className="card home-card">
      <h3>Seeded bad repairs accepted, out of {E2.bad}</h3>
      <p className="home-card-lead">E2 checks the same candidate artifacts three ways.</p>
      <ul className="bars">
        {E2.arms.map((a) => (
          <Bar key={a.key} label={a.label} detail={a.detail} count={a.badAccepted} of={E2.bad} tone="bad" />
        ))}
      </ul>
      <p className="home-card-note">
        Correct repairs rejected: {E2.arms.every((a) => a.goodRejected === 0) ? `0 of ${E2.good} by every method` : E2.arms.map((a) => `${a.label} ${a.goodRejected}`).join(", ")}.
        The one bad repair the tests accept drops the remainder for seven or more recipients; the test generator never produces more than
        five. Every bad case is a seeded attack written by the build team, so these counts describe this suite, not repairs in general.
      </p>
    </article>
  );
}

function E1Card() {
  return (
    <article className="card home-card">
      <h3>Test tasks repaired by Muse Spark 1.3, out of {E1.tasks}</h3>
      <p className="home-card-lead">E1 runs three agent setups on the frozen test tasks under the same budget.</p>
      <ul className="bars">
        {E1.arms.map((a) => (
          <Bar key={a.key} label={`${a.key}: ${a.label}`} detail={a.detail} count={a.completed} of={E1.tasks} tone="accent" />
        ))}
      </ul>
      <p className="home-card-note">
        A repair counts when the judge accepts the final candidate and its rebuilt executable passes {fmt(E1.propertyCases)} property
        cases. The arms do not differ significantly (McNemar exact p = {E1.mcnemarP.toFixed(2)} for A1 or A2 against A0), so this shows
        that Muse Spark reliably produces repairs that pass the check, not that one setup beats another. The {E1.tasks * E1.arms.length}{" "}
        runs cost ${E1.batchUsdList.toFixed(2)} at standard list prices.
      </p>
    </article>
  );
}

function RealWorld({ projects, pending }: { projects: RwProject[]; pending: string[] }) {
  const names = [...EXPECTED_PROJECTS.map((e) => e.name), ...projects.map((p) => p.name)].filter((n, i, all) => all.indexOf(n) === i);
  return (
    <section className="home-section" aria-labelledby="home-realworld">
      <h2 id="home-realworld">Released bugs in {listWords(names)}</h2>
      <p className="home-section-lead">
        These bugs shipped in released versions of open-source money code. Each release&apos;s own code, at a pinned commit, was run on
        generated inputs and its outputs compared with a reference implementation whose requirements are proved in Lean 4. The projects&apos;
        code was tested against the proved reference; it was not itself proved.
      </p>
      {projects.length === 0 ? (
        <div className="notice">
          These results are still being produced. This section fills in when <code>web/scripts/realworld.mjs</code> has read{" "}
          <code>results/realworld-1/summary.json</code>.
        </div>
      ) : (
        <div className="rw-projects">
          {projects.map((p) => (
            <RwCard key={p.key} p={p} />
          ))}
        </div>
      )}
      {projects.length > 0 && pending.length > 0 ? (
        <p className="small muted" style={{ marginTop: 12 }}>
          Results for {listWords(pending)} are not in the generated file yet.
        </p>
      ) : null}
    </section>
  );
}

function RwCard({ p }: { p: RwProject }) {
  const refutedPorts = p.ports.filter((x) => x.binary === "REFUTED");
  return (
    <article className="card rw-card">
      <div className="rw-head">
        <h3>{p.repository ? <a href={p.repository}>{p.project}</a> : p.project}</h3>
        {p.function ? (
          <p className="muted">
            Function <code>{p.function}</code>, tested at {p.versions.length === 1 ? "one release" : `${p.versions.length} releases`}.
          </p>
        ) : null}
      </div>
      <ul className="rw-versions">
        {p.versions.map((v) => (
          <RwVersionRow key={v.tag} v={v} />
        ))}
      </ul>
      <p className="home-card-note">
        {p.referenceCandidate ? <>Proved reference: {p.referenceCandidate}. </> : null}
        {p.leanConfirmation ? (
          <>
            Lean confirms {p.leanConfirmation.checked} of {p.leanConfirmation.goals} recorded violations.{" "}
          </>
        ) : null}
        {p.ports.length ? (
          <>
            ProofForge refutes {refutedPorts.length} of {p.ports.length} Lean ports of the buggy releases
            {refutedPorts.every((x) => x.kernel_refutation_checked) && refutedPorts.length ? ", each with a kernel-checked counterexample" : ""}.{" "}
          </>
        ) : null}
        {p.references.length ? (
          <>
            Reports:{" "}
            {p.references.map((r, i) => (
              <span key={r}>
                {i ? ", " : null}
                <a href={r}>{shortRef(r)}</a>
              </span>
            ))}
            .
          </>
        ) : null}
      </p>
    </article>
  );
}

function RwVersionRow({ v }: { v: RwVersion }) {
  const violating = v.violating_cases ?? 0;
  const w = v.witness;
  return (
    <li className="rw-version">
      <div className="rw-version-head">
        <span className="rw-tag mono">{v.tag}</span>
        {v.commit ? <span className="hash muted">{v.commit.slice(0, 10)}</span> : null}
        <span className="spacer" />
        {violating > 0 ? <Status value="REFUTED" /> : v.cases ? <Status value="PASS" /> : null}
      </div>
      <p className="rw-count">
        {v.status === "fixed" ? "The fixed release. " : v.status === "buggy" ? "Released with the bug. " : null}
        {v.cases != null ? (
          <>
            <strong>{fmt(violating)}</strong> of {fmt(v.cases)} inputs violate a requirement.
          </>
        ) : null}
      </p>
      {violating > 0 && w ? (
        <div className="rw-witness">
          <p className="rw-witness-input">
            Example: {describeInput(w.input)}
            {w.requirement ? (
              <>
                , violates <span className="req-id">{w.requirement}</span>
              </>
            ) : null}
            {w.confirmed_in_lean ? ", confirmed in Lean" : null}
          </p>
          <dl className="rw-outputs">
            <dt>Release output</dt>
            <dd data-outcome="bad">
              {w.output.shares ? (
                <>
                  <Shares values={w.output.shares} /> <span className="split-total">sum {w.output.shares.reduce((a, b) => a + b, 0)}</span>
                </>
              ) : (
                <code className="rw-failure">{w.output.failure ?? "no output"}</code>
              )}
            </dd>
            {w.proved_output ? (
              <>
                <dt>Proved reference</dt>
                <dd data-outcome="ok">
                  <Shares values={w.proved_output} /> <span className="split-total">sum {w.proved_output.reduce((a, b) => a + b, 0)}</span>
                </dd>
              </>
            ) : null}
          </dl>
        </div>
      ) : null}
    </li>
  );
}

function shortRef(url: string): string {
  const m = /github\.com\/[^/]+\/[^/]+\/(pull|issues)\/(\d+)/.exec(url);
  if (!m) return url;
  return `${m[1] === "pull" ? "pull request" : "issue"} ${m[2]}`;
}
