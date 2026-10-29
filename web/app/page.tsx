import Link from "next/link";
import type { Metadata } from "next";
import { Pipeline } from "@/components/Pipeline";
import { Status } from "@/components/ui";
import { E1, E2 } from "@/lib/evidence";
import {
  BENCHMARK,
  FEATURED,
  FLAGSHIPS,
  HEADLINE,
  IMPLEMENTS,
  IMPLEMENTED_FLAGSHIPS,
  SUMMARY,
  githubFile,
  incidentsSentence,
  repairCosts,
  requirementCount,
  verifiedCount,
  type Flagship,
  type PassportRef,
  type RealCodeRow,
} from "@/lib/flagships";
import { readRealworld } from "@/lib/generated";
import { EXPECTED_PROJECTS, describeInput, listWords, pendingProjects, type RwProject, type RwVersion } from "@/lib/realworld";

const fmt = (n: number) => n.toLocaleString("en-US");
const usd = (n: number) => `$${n < 0.1 ? n.toFixed(n < 0.045 ? 3 : 2) : n.toFixed(2)}`;
const words = ["no", "one", "two", "three", "four", "five", "six"];
const count = (n: number) => words[n] ?? String(n);
const capital = (s: string) => s.charAt(0).toUpperCase() + s.slice(1);
const lowerFirst = (s: string) => s.charAt(0).toLowerCase() + s.slice(1);

const metaDescription = `Meta's Muse Spark repaired the logic behind the ${incidentsSentence()} exploits and proved every locked requirement in Lean 4; ProofForge rechecked each proof in a fresh sandbox and issued a Passport.`;

export const metadata: Metadata = {
  title: `ProofForge: ${HEADLINE.replace(/\.$/, "")}`,
  description: metaDescription,
  openGraph: {
    type: "website",
    siteName: "ProofForge",
    title: HEADLINE,
    description: metaDescription,
  },
  twitter: { card: "summary", title: HEADLINE, description: metaDescription },
  alternates: { types: { "application/json": "/evidence.json", "text/plain": "/llms.txt" } },
};

// formal/task.json (issue): the flagship's buggy split; "The existing unit tests pass, but ... cents disappear."
const BUGGY_SPLIT = [33, 33, 33];
// formal/evidence/muse-repair-002/provenance.json: "$1.00 to 3 recipients -> 34 + 33 + 33"
const REPAIRED_SPLIT = [34, 33, 33];

export default function Home() {
  const rw = readRealworld();
  const costs = repairCosts();
  return (
    <main className="page home">
      <section className="hero" aria-labelledby="home-title">
        <h1 id="home-title">{HEADLINE}</h1>
        <p className="hero-sub">{SUMMARY.replace("Lean 4", "Lean\u00a04")}</p>
        <ul className="scoreboard" aria-label={`${capital(count(FLAGSHIPS.length))} exploits, repaired and proved`}>
          {FLAGSHIPS.map((f) => (
            <ScoreCard key={f.key} f={f} />
          ))}
        </ul>
        <div className="hero-foot">
          <p>
            Muse Spark 1.3 produced each repair{FLAGSHIPS.every((f) => f.repair.attempt === 1) ? " on its first attempt" : ""}, for{" "}
            {usd(costs.minList)} to {usd(costs.maxList)} at list prices.
            {IMPLEMENTED_FLAGSHIPS.length === FLAGSHIPS.length && IMPLEMENTED_FLAGSHIPS.every((i) => i.passport.status === "VERIFIED")
              ? " Starting from the specification alone, with no vulnerable code to work from, it also wrote all three from scratch, each VERIFIED."
              : ""}{" "}
            Lean proves the ports, repairs and implementations, not the real Solidity and
            Move code: <a href="#claims">what is and is not proved</a>.
          </p>
          <div className="hero-actions">
            <a className="btn btn-primary" href={githubFile(FEATURED.repair.passport.path)}>
              Open the {FEATURED.incident} Passport
            </a>
            <Link className="btn" href="/forge">
              Open the live forge session
            </Link>
            <Link className="btn" href="/results">
              Read the results
            </Link>
          </div>
        </div>
      </section>

      <FeaturedCase f={FEATURED} />

      <section className="home-section" aria-labelledby="home-cases">
        <h2 id="home-cases">{listWords(FLAGSHIPS.filter((f) => f !== FEATURED).map((f) => f.incident))}, step by step</h2>
        <div className="cases">
          {FLAGSHIPS.filter((f) => f !== FEATURED).map((f) => (
            <CaseCard key={f.key} f={f} />
          ))}
        </div>
      </section>

      <Claims />

      <section className="home-section" aria-labelledby="home-breadth">
        <h2 id="home-breadth">
          The benchmark: {BENCHMARK.tasks} repair tasks in {count(BENCHMARK.families.length)} areas
        </h2>
        <p className="home-section-lead">
          Beyond the incidents, the benchmark has {BENCHMARK.splits.dev} development, {BENCHMARK.splits.val} validation and{" "}
          {BENCHMARK.splits.test} test tasks. The test areas never appear in development or in any prompt used to build the agents. Every
          task has two reference solutions, a buggy start candidate and seeded attacks.
        </p>
        <ul className="families">
          {BENCHMARK.families.map((x) => (
            <li key={x.key}>
              <strong>{x.tasks}</strong> {x.label.toLowerCase()}
            </li>
          ))}
          {IMPLEMENTS ? (
            <li>
              <strong>
                {IMPLEMENTS.value} of {IMPLEMENTS.of}
              </strong>{" "}
              {IMPLEMENTS.label}
            </li>
          ) : null}
        </ul>
        <div className="home-evidence">
          <E2Card />
          <E1Card />
        </div>
        <SplitExample />
      </section>

      <RealWorld projects={rw.projects} pending={pendingProjects(rw)} />

      <section className="home-section" aria-labelledby="home-next">
        <h2 id="home-next">Check the evidence yourself</h2>
        <div className="home-ctas">
          <a className="home-cta" href={githubFile(FEATURED.repair.passport.path)}>
            <strong>Open the {FEATURED.incident} Passport</strong>
            <span>
              Statuses for all {requirementCount(FEATURED.repair.passport)} requirements, hashes, kernels, axioms and the command that
              reproduces it. sha256 <span className="hash">{FEATURED.repair.passport.sha256.slice(0, 16)}</span>
            </span>
          </a>
          <Link className="home-cta" href="/forge">
            <strong>Open the live forge session</strong>
            <span>Replay a recorded Muse Spark repair, then watch a fresh check of its final candidate assign every status.</span>
          </Link>
          <Link className="home-cta" href="/results">
            <strong>Read the results</strong>
            <span>E1 and E2 per arm, per task family and per case, with the seeded attacks named.</span>
          </Link>
        </div>
        <div className="reproduce card">
          <h3>Reproduce a Passport</h3>
          <p className="muted small">
            From a clone of the repository with the pinned Lean image built (see the README). <code>verify</code> rebuilds the project,
            reruns every check and compares each hash and status.
          </p>
          <pre>
            <code>{FLAGSHIPS.map((f) => f.repair.passport.reproduce).join("\n")}</code>
          </pre>
          <p className="muted small" style={{ margin: 0 }}>
            For agents: <a href="/llms.txt">llms.txt</a> and <a href="/evidence.json">evidence.json</a> list every claim, figure, Passport
            hash, source file and command on this page.
          </p>
        </div>
      </section>
    </main>
  );
}

function PassportLink({ p, label }: { p: PassportRef; label?: string }) {
  return (
    <a className="passport-link" href={githubFile(p.path)}>
      {label ?? "Passport"} <span className="hash">{p.sha256.slice(0, 12)}</span>
    </a>
  );
}

function ScoreCard({ f }: { f: Flagship }) {
  const p = f.repair.passport;
  return (
    <li className="score">
      <h2 className="score-title">
        <a href={`#case-${f.key}`}>
          {f.incident}, {f.year}
        </a>
      </h2>
      <p className="score-loss">
        <strong>{capital(f.loss.amount)}</strong> {f.loss.short}
      </p>
      <p className="score-prop">
        <span className="score-prop-lead">Proved for all inputs: </span>
        {f.property}
      </p>
      <dl className="score-verdicts">
        <div className="sv" data-verdict={f.vulnerable.verdict}>
          <dt>Vulnerable code</dt>
          <dd>
            <Status value={f.vulnerable.verdict} />
            <span className="sv-note">kernel-checked counterexample</span>
          </dd>
        </div>
        <svg className="sv-arrow" viewBox="0 0 16 16" aria-hidden="true">
          <path d="M3 8h9M8.5 4.5L12 8l-3.5 3.5" fill="none" stroke="currentColor" strokeWidth="1.6" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
        <div className="sv" data-verdict={f.repair.verdict}>
          <dt>Muse Spark repair</dt>
          <dd>
            <Status value={f.repair.verdict} />
            <span className="sv-note">
              {verifiedCount(p)} of {requirementCount(p)} requirements
            </span>
          </dd>
        </div>
      </dl>
      <p className="score-real">
        {capital(f.realCode.short)}: {f.realCode.result}.
      </p>
      <p className="score-foot">
        <PassportLink p={p} />
      </p>
    </li>
  );
}

function minutesBetween(a: string, b: string) {
  return (Date.parse(b) - Date.parse(a)) / 60000;
}

function FeaturedCase({ f }: { f: Flagship }) {
  const merged = f.timeline.filter((v) => v.merged);
  const gap = merged.length >= 2 ? Math.round(minutesBetween(merged[0]!.merged!, merged[merged.length - 1]!.merged!) / 10) * 10 : null;
  return (
    <section className="home-section featured" id={`case-${f.key}`} aria-labelledby="featured-title">
      <h2 id="featured-title">
        {f.incident}, {f.year}: four versions of one function, one locked statement
      </h2>
      <p className="home-section-lead">
        On {longDate(f.date)} an attacker drained the {f.system}: {f.loss.amount} {f.loss.basis}. {f.bug} {f.incident} merged a hotfix
        that day and a final fix {gap ? `about ${gap} minutes later` : "later"}. ProofForge checked all three, and an independent Muse
        Spark repair of the original, against the same locked Lean statement.
      </p>
      <ol className="timeline">
        {f.timeline.map((v) => (
          <li key={v.key} className="tl" data-verdict={v.verdict} data-author={v.commit ? "upstream" : "muse"}>
            <div className="tl-head">
              <h3>{v.title}</h3>
              <Status value={v.verdict} />
            </div>
            <p className="tl-detail">{v.detail}</p>
            <pre className="tl-code">
              <code>{v.code.join("\n")}</code>
            </pre>
            <p className="tl-finding">{v.finding}</p>
            <p className="tl-foot">
              <PassportLink p={v.passport} />
              <span className="hash muted">{v.commit ? `commit ${v.commit.slice(0, 7)}` : `run ${f.repair.run.split("/").pop()}`}</span>
            </p>
          </li>
        ))}
      </ol>
      <div className="featured-grid">
        <RealCode f={f} />
        <RepairFacts f={f} />
      </div>
    </section>
  );
}

function RepairFacts({ f }: { f: Flagship }) {
  const r = f.repair;
  return (
    <div className="card facts">
      <h3>The Muse repair run</h3>
      <dl className="facts-list">
        <div>
          <dt>Model</dt>
          <dd>
            {r.model}, {r.tier} tier, harness without a planner
          </dd>
        </div>
        <div>
          <dt>Accepted</dt>
          <dd>
            attempt {r.attempt}, {fmt(r.seconds)} s, {r.calls} model calls
          </dd>
        </div>
        <div>
          <dt>Cost</dt>
          <dd>
            {usd(r.usdList)} at list prices, {usd(r.usdCharged)} charged
          </dd>
        </div>
        <div>
          <dt>Check</dt>
          <dd>
            {r.kernels} kernels in Comparator, leanchecker, {fmt(r.propertyCases)} property cases on the rebuilt executable
          </dd>
        </div>
      </dl>
      {f.equivalence ? (
        <div className="equivalence">
          <p className="small">Proved separately: the repair and the final fix agree on every input.</p>
          <pre>
            <code>{f.equivalence.theorem}</code>
          </pre>
          <p className="small muted">
            Axioms: {f.equivalence.axioms}. <a href={githubFile(f.equivalence.file)}>Equivalence.lean</a>
          </p>
        </div>
      ) : null}
      <p className="small muted" style={{ margin: 0 }}>
        <code>bin/proofforge verify</code> reproduced every hash and status. <PassportLink p={r.passport} label="Open the Passport" />
      </p>
    </div>
  );
}

function RealCode({ f }: { f: Flagship }) {
  const rc = f.realCode;
  const allMatch = rc.rows.every((r) => r.sameAsPort === null || r.sameAsPort === rc.total);
  return (
    <div className="card realcode">
      <h3>Against the real {f.language} code</h3>
      <p className="small muted">{rc.how}</p>
      <ul className="bars">
        {rc.rows.map((row) => (
          <RealBar key={row.label} row={row} total={rc.total} unit={rc.unit} />
        ))}
      </ul>
      <p className="small muted" style={{ margin: "14px 0 0" }}>
        {allMatch && rc.rows.some((r) => r.sameAsPort !== null) ? (
          <>The real code&apos;s output equals its Lean port&apos;s on every one of the {fmt(rc.total)} {rc.unit}. </>
        ) : null}
        Recorded violations restated as Lean goals and checked in the kernel: {rc.confirmedInLean.checked} of {rc.confirmedInLean.goals}.{" "}
        <a href={githubFile(rc.report)}>Report</a>
      </p>
    </div>
  );
}

function RealBar({ row, total, unit }: { row: RealCodeRow; total: number; unit: string }) {
  const pct = total ? (100 * row.violating) / total : 0;
  return (
    <li className="bar-row">
      <div className="bar-label">
        <span>{row.label}</span>
        <span className="bar-detail">{row.note}</span>
      </div>
      <div className="bar-figure">
        <span className="bar-track" aria-hidden="true">
          <span className="bar-fill" data-tone="bad" style={{ width: `${Math.max(pct, row.violating ? 1 : 0)}%` }} />
        </span>
        <span className="bar-count">
          <strong>{fmt(row.violating)}</strong> of {fmt(total)}
        </span>
      </div>
      <span className="sr-only">
        {fmt(row.violating)} of {fmt(total)} {unit} break a requirement
      </span>
    </li>
  );
}

function CaseCard({ f }: { f: Flagship }) {
  return (
    <article className="card case" id={`case-${f.key}`}>
      <h3>
        {f.incident}, {f.year}
      </h3>
      <p className="case-loss">
        <strong>{capital(f.loss.amount)}</strong> {f.loss.basis}.{" "}
        {f.loss.citations.map((c, i) => (
          <span key={c.url}>
            {i ? ", " : null}
            <a href={c.url}>{c.label}</a>
          </span>
        ))}
      </p>
      <p className="case-bug">{f.bug}</p>
      <h4>The attack, with the state after each step</h4>
      <ol className="attack">
        {f.attack.map((s, i) => (
          <li key={i}>
            <span>{s.text}</span>
            {s.after ? <span className="attack-after">{s.after}</span> : null}
          </li>
        ))}
      </ol>
      <div className="verdict-box" data-verdict="REFUTED">
        <div className="verdict-head">
          <Status value="REFUTED" />
          <span>{f.vulnerable.label}</span>
        </div>
        <p>{f.outcome}</p>
        <p className="small">
          <a href={githubFile(f.vulnerable.witness)}>Kernel-checked counterexample</a>
          {f.vulnerable.passport ? (
            <>
              {" "}
              and <PassportLink p={f.vulnerable.passport} />
            </>
          ) : null}
        </p>
      </div>
      <div className="verdict-box" data-verdict="VERIFIED">
        <div className="verdict-head">
          <Status value="VERIFIED" />
          <span>Muse Spark 1.3 repair</span>
        </div>
        <p>
          The repair {f.repair.change}. It proves all {requirementCount(f.repair.passport)} requirements, among them that{" "}
          {lowerFirst(f.property)} Attempt {f.repair.attempt}, {fmt(f.repair.seconds)} s, {usd(f.repair.usdList)} at list prices.
        </p>
        <p className="small">
          <PassportLink p={f.repair.passport} />
        </p>
      </div>
      <RealCode f={f} />
    </article>
  );
}

function Claims() {
  const reconstruction = FLAGSHIPS.map((f) => f.reconstruction).filter((x): x is string => !!x);
  return (
    <section className="home-section" id="claims" aria-labelledby="home-claims">
      <h2 id="home-claims">What is proved, and what is not</h2>
      <div className="claims-grid">
        <div className="card claims-col">
          <h3>Proved</h3>
          <ul>
            <li>
              Each requirement is a Lean 4 statement about the Lean port of the vulnerable logic, locked by hash. A VERIFIED requirement
              holds for every input, not a sample.
            </li>
            <li>
              A VERIFIED status comes only from ProofForge&apos;s own check: <code>lake comparator --paranoid</code> with six kernels in a
              fresh sandbox, leanchecker, an axiom audit, and property tests on the executable rebuilt from the same source.
            </li>
            <li>Each REFUTED port has a counterexample checked by the Lean kernel.</li>
          </ul>
        </div>
        <div className="card claims-col">
          <h3>Not proved</h3>
          <ul>
            <li>The Solidity and Move code are not themselves proved.</li>
            <li>
              The Lean ports are reviewed hand translations. They are tested against the real code on the stated inputs (
              {listWords(FLAGSHIPS.map((f) => `${fmt(f.realCode.total)} ${f.realCode.unit} for ${f.incident}`))}); the translation is not
              machine-checked.
            </li>
            <li>
              Each port models only the logic its task README names: for example, Euler has one asset and no interest, and Hundred&apos;s
              borrowing is not modeled.
            </li>
            {reconstruction.map((r) => (
              <li key={r}>{r}</li>
            ))}
            <li>Loss figures are quoted from the sources each task README cites.</li>
          </ul>
        </div>
      </div>
      <div className="card claims-steps">
        <h3>How a repair counts</h3>
        <Pipeline className="pipeline-lg" />
      </div>
    </section>
  );
}

function longDate(iso: string) {
  return new Date(`${iso}T00:00:00Z`).toLocaleDateString("en-GB", { day: "numeric", month: "long", year: "numeric", timeZone: "UTC" });
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
  const sum = (xs: number[]) => xs.reduce((a, b) => a + b, 0);
  return (
    <figure className="split-mini card" aria-labelledby="split-caption">
      <figcaption id="split-caption">
        The smallest task: a payout splitter pays 100 cents to three recipients. The code under repair loses a cent while each share
        looks right; Muse Spark&apos;s proved repair conserves the total.
      </figcaption>
      <div className="split-mini-rows">
        <div className="split-values" data-outcome="bad">
          <Shares values={BUGGY_SPLIT} />
          <span className="split-total">= {sum(BUGGY_SPLIT)}</span>
          <Status value="REFUTED" />
        </div>
        <div className="split-values" data-outcome="ok">
          <Shares values={REPAIRED_SPLIT} highlight={0} />
          <span className="split-total">= {sum(REPAIRED_SPLIT)}</span>
          <Status value="VERIFIED" />
        </div>
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
        <div className="notice small muted">
          These results are not in this build yet. They appear here when <code>web/scripts/realworld.mjs</code> has read{" "}
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
