import Link from "next/link";
import type { Metadata } from "next";
import type { ReactNode } from "react";
import { CheckFix } from "@/components/CheckFix";
import { Pipeline } from "@/components/Pipeline";
import { HeroLenses } from "@/components/HeroLenses";
import { Seal } from "@/components/Seal";
import { Status } from "@/components/ui";
import {
  CETUS_HOTFIX,
  COMPARISON,
  COST_PER_VERIFIED,
  COUNTEREXAMPLES,
  HACKATHON,
  LIBRARY,
  LIBRARY_COMPOUND,
  LIBRARY_RUN,
  OPEN_WEIGHTS,
  PLANNER,
  RUN_CAPS,
  SCOPE,
  SPEC_STRENGTH,
  aloneRuns,
  plannerRuns,
  type ComparisonRow,
  type Runs,
} from "@/lib/contribution";
import { E1, E2 } from "@/lib/evidence";
import {
  BENCHMARK,
  FEATURED,
  FLAGSHIPS,
  HEADLINE,
  IMPLEMENTS,
  SUMMARY,
  githubFile,
  lossTotalPhrase,
  requirementCount,
  type Flagship,
  type PassportRef,
  type RealCodeRow,
} from "@/lib/flagships";
import { readRealworld } from "@/lib/generated";
import { PROOF_GRAPH, layoutGraph } from "@/lib/proofgraph";
import { GRAPH_TASK, bellOf, guarantees, layoutLayers } from "@/lib/lenses";
import { holeRun } from "@/lib/hole";
import { EXPECTED_PROJECTS, describeInput, listWords, pendingProjects, type RwProject, type RwVersion } from "@/lib/realworld";
import { WinsHeadline } from "@/components/Wins";
import { countsSentence, headlines } from "@/lib/wins";
import { WINS } from "@/lib/wins-data";

const fmt = (n: number) => n.toLocaleString("en-US");
const usd = (n: number) => `$${n < 0.1 ? n.toFixed(n < 0.045 ? 3 : 2) : n.toFixed(2)}`;
const words = ["no", "one", "two", "three", "four", "five", "six"];
const count = (n: number) => words[n] ?? String(n);
const capital = (s: string) => s.charAt(0).toUpperCase() + s.slice(1);
const lowerFirst = (s: string) => s.charAt(0).toLowerCase() + s.slice(1);
const andListOf = (xs: string[]) => (xs.length <= 1 ? xs.join("") : `${xs.slice(0, -1).join("; ")}; and ${xs[xs.length - 1]}`);

const pr6 = FEATURED.timeline.find((v) => v.key === "pr6")!;
const metaDescription = `ProofForge refuted the Cetus same-day hotfix with a counterexample six Lean kernels check, then accepted the final fix and a Muse Spark repair with proofs for every input. Locked specifications of ${count(FLAGSHIPS.length)} real financial failures, kernel-checked counterexamples and hash-bound Passports anyone can re-run.`;

export const metadata: Metadata = {
  title: `ProofForge: ${HEADLINE.replace(/\.$/, "")}`,
  description: metaDescription,
  openGraph: {
    type: "website",
    siteName: "ProofForge",
    title: HEADLINE,
    description: metaDescription,
  },
  twitter: { card: "summary_large_image", title: HEADLINE, description: metaDescription },
  alternates: { types: { "application/json": "/evidence.json", "text/plain": "/llms.txt" } },
};

// formal/task.json (issue): the flagship's buggy split; "The existing unit tests pass, but ... cents disappear."
const BUGGY_SPLIT = [33, 33, 33];
// formal/evidence/muse-repair-002/provenance.json: "$1.00 to 3 recipients -> 34 + 33 + 33"
const REPAIRED_SPLIT = [34, 33, 33];

const longDay = (iso: string) =>
  new Date(`${iso}T00:00:00Z`).toLocaleDateString("en-GB", { day: "numeric", month: "long", year: "numeric", timeZone: "UTC" });

export default function Home() {
  const rw = readRealworld();
  return (
    <main id="main" className="home">
      <section className="hero-band tone-dark" aria-labelledby="home-title">
        <div className="hero-band-inner">
          <HeroGraph />
          <HeadlineFacts />
          <GraphCaption />
        </div>
      </section>

      <div className="page home-body">
      <HomeWins />

      <div className="hero-grid">
        <HeroCase f={FEATURED} />
        <TrustModel />
      </div>
      <div className="hero-foot">
        <div className="hero-facts">
          <p>
            Built during the {HACKATHON.event}: everything in the repository, from the judge, the Passport and the counterexample stage to the
            real-world tasks, the ProofForgeFin library and this site, was created on or after the day of the first commit, {longDay(HACKATHON.firstCommit)};
            submissions close {longDay(HACKATHON.submissionsDue)} (<a href={githubFile("ORIGIN.md")}>ORIGIN.md</a>).
          </p>
          <p>{SCOPE}</p>
        </div>
      </div>

      <Comparison />

      <section className="home-section" id="check" aria-labelledby="home-check">
        <h2 id="home-check">Check a fix against its locked specification</h2>
        <p className="home-section-lead">
          Pick a real failure and a version of its code, and the ProofForge API judges it now. If the API is slow or down, the panel shows the
          committed Passport of the same file and says so.
        </p>
        <CheckFix />
      </section>

      <Lift />

      <Library />

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
      </div>
    </main>
  );
}

/** The hero: the headline beside the proof graph of the verified Balancer repair (generated/proof-graph.json)
 * in three lenses, all computed on the server: the whole proof, its layers, and one guarantee. */
function HeroGraph() {
  const g = PROOF_GRAPH;
  const gs = guarantees(g);
  const counts = g.counts;
  return (
    <HeroLenses
      radial={layoutGraph(g)}
      layers={layoutLayers(g)}
      guarantees={gs}
      bells={gs.map((x) => bellOf(x.node, g))}
      hole={holeRun()}
      initial={gs.findIndex((x) => x.size === Math.max(...gs.map((y) => y.size)))}
      uses={g.edges}
      readings={{
        passport: g.passport.sha256,
        status: g.passport.status,
        requirements: g.passport.requirements,
        verified: g.passport.verified,
        kernels: g.passport.kernels,
        propertyCases: g.passport.propertyCases,
        axioms: g.passport.axioms,
        declarations: counts.nodes,
      }}
      passportHref={githubFile(g.passport.file)}
      text={{
        headline: HEADLINE,
        summary: SUMMARY,
        layersTitle: "Muse writes the fix. Lean proves it for every input.",
        layersText: `The ${counts.requirements} requirements on top are theorems over every input, the ${counts.lemmas} lemmas in the middle are the steps Muse proved to reach them, and the ${counts.definitions + counts.types} definitions and types at the bottom are the repaired code and the locked specification.`,
        guaranteeTitle: "The shape of a guarantee.",
        task: GRAPH_TASK.name,
      }}
      figures={<HeroFigures key="figures" />}
      actions={
        <div key="actions" className="hero-actions">
          <a className="btn btn-primary" href="#check">
            Check a fix now
          </a>
          <a className="btn" href={githubFile(CETUS_HOTFIX.passport)}>
            Open the hotfix Passport
          </a>
          <Link className="btn" href="/frontier">
            How far ProofForge takes Muse
          </Link>
        </div>
      }
    />
  );
}

/** The largest gains of the ledger (results/wins/ledger.json), right after the hero, with the counts and the way to every comparison. */
function HomeWins() {
  return (
    <section className="home-section home-wins" id="wins" aria-labelledby="home-wins">
      <h2 id="home-wins">How far ProofForge takes Meta&apos;s models</h2>
      <p className="home-section-lead">
        The same Meta model on the same tasks and caps, on its own and with ProofForge, both judged against the same locked specification.{" "}
        {countsSentence(WINS)} Every run is in the ledger with its Passport.
      </p>
      <WinsHeadline items={headlines(WINS)} />
      <p className="home-wins-more">
        <Link className="btn btn-primary" href="/frontier">
          Every comparison
        </Link>
        <a className="btn" href={githubFile(WINS.readme)}>
          The ledger on GitHub
        </a>
      </p>
    </section>
  );
}

/** The graph's caption, under the facts so the first screen holds the figures. */
function GraphCaption() {
  const g = PROOF_GRAPH;
  return (
    <p id="pg-caption" className="pg-caption">
      The graph: the verified Muse repair of Balancer V2 (Passport {g.passport.sha256.slice(0, 8)}), its {g.passport.requirements} requirement
      theorems and the {g.counts.nodes - g.passport.requirements} lemmas, definitions and types they use, extracted from the Lean kernel&apos;s
      record of what each declaration uses. One guarantee shows the declarations a requirement theorem uses, directly or through others, one
      ring per level of dependency depth, each ring as wide as the number of declarations on it. Kernels: {g.passport.kernels.join(", ")}.{" "}
      <a href={githubFile("web/generated/proof-graph.json")}>Graph data</a>
    </p>
  );
}

/** Short incident names for running text: "Euler Finance" becomes "Euler". */
const shortIncident = (name: string) => name.replace(/ (Finance|V2|Proposal 62)$/, "");

interface HeadlineFact {
  key: string;
  figure: ReactNode;
  text: ReactNode;
  note: ReactNode;
  source: ReactNode;
}

/** The four strongest measured facts, each with its evidence. */
function headlineFacts(): HeadlineFact[] {
  const refutedFailures = COMPARISON.filter((r) => r.refutations.some((x) => x.kernelChecked > 0));
  const refuted = COMPARISON.reduce((n, r) => n + r.refutations.reduce((m, x) => m + x.refuted, 0), 0);
  const checked = COMPARISON.reduce((n, r) => n + r.refutations.reduce((m, x) => m + x.kernelChecked, 0), 0);
  const e2 = (key: string) => E2.arms.find((a) => a.key === key)!;
  const balancer = COST_PER_VERIFIED.find((c) => c.key === "balancer")!;
  const ss = SPEC_STRENGTH;
  return [
    {
      key: "refuted",
      figure: (
      <>
            {refutedFailures.length} of {COMPARISON.length}
      </>
    ),
      text: (
      <>
            Real failures, {lossTotalPhrase()} in reported losses, refuted with counterexamples the Lean kernel checks.
      </>
    ),
      note: (
      <>
            {listWords(COMPARISON.map((r) => shortIncident(r.incident)))}. The losses are quoted for {count(FLAGSHIPS.length)} of them and
            measure different things; see the notes under <a href="#compare">the comparison</a>. {checked} of the {refuted} refuted requirements
            have a kernel-checked counterexample.
      </>
    ),
      source: (
      <>
            <a href={githubFile("results/counterexamples-1/README.md")}>results/counterexamples-1</a>
      </>
    ),
    },
    {
      key: "e2",
      figure: (
      <>
            {e2("proofforge").badAccepted} of {E2.bad}
      </>
    ),
      text: (
      <>
            Bad repairs accepted by ProofForge. Ordinary checking accepted {e2("ordinary").badAccepted}.
      </>
    ),
      note: (
      <>
            Ordinary checking: the build passes, the theorem names exist, the axioms are clean. ProofForge rejected {e2("proofforge").goodRejected}{" "}
            of {E2.good} correct repairs. The bad repairs are the seeded attacks of the E2 suite.
      </>
    ),
      source: (
      <>
            <a href={githubFile(E2.source.replace("e2.json", "e2.md"))}>results/e2-all-1</a>
      </>
    ),
    },
    {
      key: "cost",
      figure: (
      <>
            ${balancer.planner.usdPerVerified.toFixed(2)} <span className="fact-figure-alt">vs ${balancer.alone.usdPerVerified.toFixed(2)}</span>
      </>
    ),
      text: (
      <>
            Per verified {shortIncident(balancer.incident)} fix: Muse with ProofForge verified {balancer.planner.verified} of{" "}
            {balancer.planner.runs} runs, Muse alone {balancer.alone.verified} of {balancer.alone.runs}, at the same caps.
      </>
    ),
      note: (
      <>
            List prices; caps of ${RUN_CAPS.usdList} and {RUN_CAPS.seconds / 3600} hours per run; Muse Spark 1.3, with the Muse Wonder planner
            in the ProofForge arm: two Meta models working together on one budget.
      </>
    ),
      source: (
      <>
            <a href={githubFile("results/library-1/README.md")}>results/library-1</a>
      </>
    ),
    },
    {
      key: "spec",
      figure: (
      <>
            {fmt(ss.rejected)} of {fmt(ss.compiled)}
      </>
    ),
      text: (
      <>
            Wrong variants of the reference code rejected by the {ss.specifications} locked specifications, {fmt(ss.kernelChecked)} with
            kernel-checked counterexamples.
      </>
    ),
      note: (
      <>
            Each variant is a compiling mutant with one change. Of the {ss.compiled - ss.rejected} that pass, {ss.survivedDiffers} behave differently from the reference and are reported as
            specification gaps.
      </>
    ),
      source: (
      <>
            <a href={githubFile(ss.doc)}>{ss.doc}</a>
      </>
    ),
    },
  ];
}

/** The facts as cards in the hero band: figure and sentence first, then the note and the source. */
function HeadlineFacts() {
  return (
    <ul className="headline-facts" aria-label="Measured results">
      {headlineFacts().map((f) => (
        <li key={f.key} className="card fact">
          <p className="fact-figure">{f.figure}</p>
          <p className="fact-text">{f.text}</p>
          <p className="fact-note">{f.note}</p>
          <p className="fact-source">{f.source}</p>
        </li>
      ))}
    </ul>
  );
}

/** Narrow screens only: the four figures and their sentences right under the headline, in a 2 by 2 grid.
 * The same facts follow in full as cards, so this copy is hidden from assistive technology. */
function HeroFigures() {
  return (
    <ul className="hero-figures" aria-hidden="true">
      {headlineFacts().map((f) => (
        <li key={f.key}>
          <p className="fact-figure">{f.figure}</p>
          <p className="fact-text">{f.text}</p>
        </li>
      ))}
    </ul>
  );
}

function PassportLink({ p, label }: { p: PassportRef; label?: string }) {
  return (
    <a className="passport-link" href={githubFile(p.path)}>
      {label ?? "Passport"} <span className="hash">{p.sha256.slice(0, 12)}</span>
    </a>
  );
}

/** The hardest real result, on the first screen: four versions of Cetus's overflow check against one locked specification. */
function HeroCase({ f }: { f: Flagship }) {
  return (
    <figure className="hero-case card" aria-labelledby="hero-case-title">
      <figcaption id="hero-case-title">
        <strong>
          {f.incident}, {longDay(f.date)}: {f.loss.amount} {f.loss.short}.
        </strong>{" "}
        Four versions of its overflow check, one locked specification of five requirements.
      </figcaption>
      <ol className="hc-steps">
        {f.timeline.map((v) => (
          <li key={v.key} className="hc-step" data-verdict={v.verdict}>
            <span className="hc-title">
              {v.title} <span className="hc-detail">{v.detail}</span>
            </span>
            <code className="hc-code">{v.code.join("; ")}</code>
            <span className="hc-finding">
              <Status value={v.verdict} /> {v.short}
              {v.key === "pr6" ? (
                <>
                  {" "}
                  The counterexample is a Lean theorem, <code>{CETUS_HOTFIX.statement}</code>, accepted by all {CETUS_HOTFIX.kernels} kernels.
                </>
              ) : null}
            </span>
          </li>
        ))}
      </ol>
      <p className="hc-foot small">
        <PassportLink p={pr6.passport} label="Hotfix Passport" /> <PassportLink p={f.repair.passport} label="Muse repair Passport" />{" "}
        <a href="#case-cetus">The Cetus case in full</a>
      </p>
    </figure>
  );
}

function TrustModel() {
  const e2 = (key: string) => E2.arms.find((a) => a.key === key)!;
  return (
    <div className="trust card" aria-labelledby="trust-title">
      <h2 id="trust-title" className="trust-title">
        What ProofForge checks before it says VERIFIED
      </h2>
      <ol className="trust-list">
        <li>The requirements are Lean 4 statements, locked by hash before any model sees the task.</li>
        <li>
          Lean&apos;s Comparator checks the proof in a fresh sandbox with six independent kernels (Lean default and paranoid, lean4lean,
          nanoda, con-leche, con-ron); leanchecker replays it and an axiom audit rejects anything beyond <code>propext</code>,{" "}
          <code>Classical.choice</code> and <code>Quot.sound</code>.
        </li>
        <li>The executable rebuilt from the same source runs on 2,001 generated property cases.</li>
        <li>
          A refutation is a theorem too: the negation of the requirement on the failing input, checked by the same kernels.{" "}
          {COUNTEREXAMPLES.kernelChecked} of {COUNTEREXAMPLES.refuted} refuted requirements over {COUNTEREXAMPLES.candidates} candidates are
          refuted this way.
        </li>
        <li>
          The Passport binds the specification, the source, the executable and the judge image by hash. <code>bin/proofforge verify</code>{" "}
          re-runs it from a clone.
        </li>
      </ol>
      <p className="trust-e2">
        On {E2.bad} seeded bad repairs, ordinary checking (the build passes, the theorem names exist, the axioms are clean) accepted{" "}
        <strong>{e2("ordinary").badAccepted}</strong>. ProofForge accepted <strong>{e2("proofforge").badAccepted}</strong>, and rejected{" "}
        {e2("proofforge").goodRejected} of {E2.good} correct ones. The bad cases were written by the build team.
      </p>
      <p className="trust-spec">
        The specifications are measured too: changed at one site each, the reference solutions give {fmt(SPEC_STRENGTH.compiled)}{" "}
        compiling variants, and the {SPEC_STRENGTH.specifications} locked specifications reject {fmt(SPEC_STRENGTH.rejected)} of them,{" "}
        {fmt(SPEC_STRENGTH.kernelChecked)} with kernel-checked counterexamples. The {SPEC_STRENGTH.survivedDiffers} that pass while behaving
        differently are listed as specification gaps (<a href={githubFile(SPEC_STRENGTH.doc)}>SPEC_STRENGTH.md</a>,{" "}
        <a href={githubFile(`${SPEC_STRENGTH.source}/README.md`)}>results</a>).
      </p>
    </div>
  );
}

const accepted = (r: Runs) => `${r.accepted} of ${r.runs.length}`;
const armName: Record<Runs["arm"], string> = { A0: "alone", A1: "harness", A2: "with Wonder planner" };

function Comparison() {
  const failures = FLAGSHIPS.length;
  const compound = COMPARISON.find((r) => r.key === "compound")!;
  const compoundLibrary = (compound.library?.withLibrary.runs.length ?? 0) + (compound.library?.topdown?.runs.length ?? 0);
  // Tasks where every run of every arm was accepted.
  const easy = COMPARISON.filter((r) => [r.alone, ...r.harness].every((x) => x.accepted === x.runs.length) && !r.library);
  return (
    <section className="home-section" id="compare" aria-labelledby="home-compare">
      <h2 id="home-compare">Muse alone and Muse with ProofForge, on the real failures</h2>
      <p className="home-section-lead">
        Every run is Muse Spark 1.3, capped at ${RUN_CAPS.usdList} at list prices and {RUN_CAPS.seconds / 3600} hours, and judged by ProofForge
        against the same locked specification. Muse alone replies with whole files and sees only Lean&apos;s errors and the axiom audit. With the
        ProofForge harness it fixes behavior against the property tests first, then proves one obligation at a time with snippet checks; the
        second harness arm adds Muse Wonder 1.0 as lemma planner. On Compound, Knight and Balancer the counts include{" "}
        <a href={githubFile(`${LIBRARY_RUN.source}/README.md`)}>{LIBRARY_RUN.source}</a>, where the planner arm also imports the ProofForgeFin
        library.
      </p>
      <div className="ledger-wrap">
        <table className="ledger compare">
          <thead>
            <tr>
              <th scope="col">Failure</th>
              <th scope="col">Muse alone, accepted</th>
              <th scope="col">With the ProofForge harness, accepted</th>
              <th scope="col">Vulnerable code, kernel-checked counterexamples</th>
              <th scope="col">From the specification alone, accepted</th>
            </tr>
          </thead>
          <tbody>
            {COMPARISON.map((row) => (
              <CompareRow key={row.key} row={row} f={FLAGSHIPS.find((x) => x.key === row.key) ?? null} />
            ))}
          </tbody>
        </table>
      </div>
      <div className="compare-notes">
        <p>
          On {listWords(easy.map((r) => shortIncident(r.incident)))} both arms succeed: Muse alone and the harness were accepted in every run. On{" "}
          {listWords(COST_PER_VERIFIED.map((c) => shortIncident(c.incident)))} the arm with the Muse Wonder planner succeeds more often and at a
          lower list price per verified run, counting every run at the same caps:{" "}
          {COST_PER_VERIFIED.map(
            (c) =>
              `${shortIncident(c.incident)} ${c.planner.verified} of ${c.planner.runs} runs verified at $${c.planner.usdPerVerified.toFixed(2)} per verified run, against ${c.alone.verified} of ${c.alone.runs} at $${c.alone.usdPerVerified.toFixed(2)} for Muse alone`,
          ).join("; ")}
          .
        </p>
        <p>
          On Compound nothing succeeds: no run of any method has proved all {compound.requirements} of its requirements. Muse alone verified{" "}
          {accepted(aloneRuns(compound))} runs,{" "}
          {compound.harness
            .filter((h) => h.arm !== "A2")
            .map((h) => `the harness ${accepted(h)}`)
            .join(", ")}
          , the harness with the planner {accepted(plannerRuns(compound)!)} ({compoundLibrary} of them with the library) and implementation from
          the specification {accepted(compound.implement)}. The specification is provable: the build team&apos;s proof that uses the library is VERIFIED on the deployed judge (
          <a href={githubFile(LIBRARY.compoundLivePassportFile)}>Passport {LIBRARY.compoundLivePassport.slice(0, 8)}</a>). The two Muse-alone
          Compound runs in baseline-flagships-1 ended early, when one model call reached its 600 s timeout, a defect that treated it as the
          run&apos;s wall-clock stop; the {count(compound.library!.alone!.runs.length)} in library-1 ran the full {RUN_CAPS.seconds / 3600} hours.
        </p>
        <p>
          The figures that need ProofForge in every row are the specification each run proves, the counterexamples that refute the vulnerable
          code, and the check that makes an acceptance mean every requirement holds for every input.
        </p>
        <p>
          The {count(failures)} failures with quoted losses total {lossTotalPhrase()}. The figures measure different things: the amounts taken
          from Cetus and from Balancer and its forks, Hundred&apos;s reported losses, the net profit of Euler&apos;s attacker (later returned),
          and Knight Capital&apos;s realized trading loss, which was not an exploit and is reconstructed from the SEC order.
        </p>
        <p className="muted">
          Runs: <a href={githubFile("results/baseline-flagships-1/README.md")}>baseline-flagships-1</a>,{" "}
          <a href={githubFile(`${LIBRARY_RUN.source}/README.md`)}>library-1</a>,{" "}
          <a href={githubFile("results/library-live-1/README.md")}>library-live-1</a>,{" "}
          <a href={githubFile("results/counterexamples-1/README.md")}>counterexamples-1</a> and each task&apos;s results README.
        </p>
      </div>
    </section>
  );
}

function CompareRow({ row, f }: { row: ComparisonRow; f: Flagship | null }) {
  const refuted = row.refutations.reduce((n, r) => n + r.refuted, 0);
  const checked = row.refutations.reduce((n, r) => n + r.kernelChecked, 0);
  const alone = aloneRuns(row);
  const planner = plannerRuns(row);
  const arms = [...row.harness.filter((h) => h.arm !== "A2"), ...(planner ? [planner] : [])];
  const withLibrary = row.library ? row.library.withLibrary.runs.length + (row.library.topdown?.runs.length ?? 0) : 0;
  return (
    <tr>
      <td className="ledger-incident">
        {f ? (
          <a href={`#case-${f.key}`}>
            {row.incident}, {row.year}
          </a>
        ) : (
          <span className="compare-name">
            {row.incident}, {row.year}
          </span>
        )}
        <span className="ledger-sub">{f ? `${capital(f.loss.amount)} ${f.loss.short}` : "COMP rewards credited but never emitted"}</span>
      </td>
      <td className="compare-cell" data-label="Muse alone, accepted" data-zero={alone.accepted === 0 || undefined}>
        <strong>{accepted(alone)}</strong>
        <span className="ledger-sub">runs{row.library?.alone ? `, ${row.library.alone.runs.length} of them in library-1` : ""}</span>
      </td>
      <td className="compare-cell" data-label="With the ProofForge harness, accepted">
        {arms.map((h) => (
          <span key={h.arm} className="compare-arm" data-zero={h.accepted === 0 || undefined}>
            <strong>{accepted(h)}</strong> {armName[h.arm]}
          </span>
        ))}
        {withLibrary ? <span className="ledger-sub">{withLibrary} of the planner runs with the library</span> : null}
      </td>
      <td className="compare-cell" data-label="Vulnerable code, kernel-checked counterexamples">
        <Status value="REFUTED" />
        <span className="ledger-sub">
          {checked} of {refuted} requirements
          {row.refutations.length > 1 ? ` (${row.refutations.map((r) => `${r.label} ${r.kernelChecked} of ${r.refuted}`).join(", ")})` : ""}
        </span>
      </td>
      <td className="compare-cell" data-label="From the specification alone, accepted" data-zero={row.implement.accepted === 0 || undefined}>
        <strong>{accepted(row.implement)}</strong>
        <span className="ledger-sub">runs{row.implement.arm === "A2" ? ", with the planner" : ""}</span>
      </td>
    </tr>
  );
}

function Lift() {
  const [open, glimmer] = OPEN_WEIGHTS;
  const compoundLib = COMPARISON.find((r) => r.key === "compound")!.library!;
  const compoundLibraryRuns = compoundLib.withLibrary.runs.length + (compoundLib.topdown?.runs.length ?? 0);
  const pct = (x: number) => `${x >= 0 ? "+" : ""}${Math.round(x * 100)}`;
  return (
    <section className="home-section" id="lift" aria-labelledby="home-lift">
      <h2 id="home-lift">Where the harness and the planner change the outcome</h2>
      <p className="home-section-lead">
        Muse Spark 1.3 completes almost every benchmark task with or without the harness ({E1.arms.map((a) => `${a.key} ${a.completed}`).join(", ")}{" "}
        of {E1.tasks}). The gains show up with smaller open-weight models and on the hardest proofs.
      </p>
      <div className="lift-grid">
        {open ? (
          <article className="card lift-card">
            <h3>{open.model}, open weights</h3>
            <p className="lift-figure">
              <strong>
                {open.a0.completed} to {open.a1.completed}
              </strong>{" "}
              of {open.a0.n} test tasks completed, alone and with the harness
            </p>
            <p className="small">
              With the harness every final executable passed the property tests ({open.binaryPass.a1} of {open.a1.n}); alone, {open.binaryPass.a0}{" "}
              built. Difference {pct((open.a1.completed - open.a0.completed) / open.paired)} points, 95% interval {pct(open.ci95[0])} to{" "}
              {pct(open.ci95[1])}, McNemar p = {open.mcnemarP.toFixed(2)}.
            </p>
            <p className="small muted">
              {open.serving}. <a href={githubFile(open.source.replace("e1.json", "e1.md"))}>Report</a>
            </p>
          </article>
        ) : null}
        {glimmer ? (
          <article className="card lift-card">
            <h3>{glimmer.model}, open weights</h3>
            <p className="lift-figure">
              <strong>
                {glimmer.a0.completed} of {glimmer.a0.n}
              </strong>{" "}
              alone,{" "}
              <strong>
                {glimmer.outage?.a1Completed} of {glimmer.outage?.a1N}
              </strong>{" "}
              with the harness
            </p>
            <p className="small">
              Incomplete: the GPU host paused the workspace after 31 of 60 runs were scored, and {glimmer.outage?.runs.length} harness runs it
              ended are excluded ({glimmer.a1.completed} of {glimmer.a1.n} counting them). Alone, no version compiled; with the harness{" "}
              {glimmer.binaryPass.a1} final executables passed the property tests. McNemar p = {glimmer.mcnemarP.toFixed(2)} on{" "}
              {glimmer.paired} paired tasks.
            </p>
            <p className="small muted">
              {capital(glimmer.serving)}. <a href={githubFile(glimmer.source.replace("e1.json", "README.md"))}>Report</a>
            </p>
          </article>
        ) : null}
        <article className="card lift-card">
          <h3>Muse Wonder as planner</h3>
          <ul className="lift-list">
            {PLANNER.map((p) => (
              <li key={p.task}>
                <strong>{p.incident}</strong>: the harness alone proved {p.a1.join(" and ")} of {p.requirements} requirements in its two runs; with
                the planner, {p.a2.join(" and ")}
                {p.a2Accepted ? `, and the second run was VERIFIED` : `; neither was accepted`}.
              </li>
            ))}
          </ul>
          <p className="small">
            With the ProofForgeFin library ({LIBRARY_RUN.source}), the planner arm verified{" "}
            {COMPARISON.filter((r) => r.library && r.library.withLibrary.accepted > 0)
              .map((r) => `${shortIncident(r.incident)} in ${r.library!.withLibrary.accepted} of ${r.library!.withLibrary.runs.length}`)
              .join(" and ")}{" "}
            further runs, and Compound in none of {compoundLibraryRuns}.
          </p>
          <p className="small muted">
            Muse alone was also accepted on Knight in one of two runs. <a href={githubFile("results/compound-1/README.md")}>Compound runs</a>,{" "}
            <a href={githubFile("results/knight-1/README.md")}>Knight runs</a>,{" "}
            <a href={githubFile(`${LIBRARY_RUN.source}/README.md`)}>library-1</a>
          </p>
        </article>
      </div>
    </section>
  );
}

function Library() {
  const compound = COMPARISON.find((r) => r.key === "compound")!.library!;
  const libRuns = compound.withLibrary.runs.length + (compound.topdown?.runs.length ?? 0);
  const verifiedEvery = COMPARISON.filter((r) => r.library && r.library.withLibrary.accepted === r.library.withLibrary.runs.length).map((r) =>
    shortIncident(r.incident),
  );
  return (
    <section className="home-section" id="library" aria-labelledby="home-library">
      <h2 id="home-library">ProofForgeFin, the proved library behind the judge</h2>
      <div className="library card">
        <p>
          {fmt(LIBRARY.theorems)} theorems and {fmt(LIBRARY.definitions)} definitions in {LIBRARY.files} Lean files: floor and ceiling division,
          fixed point at any scale, share accounting, runs of operations with invariants over every reachable state, and conservation over
          accounts, with no dependency beyond Lean&apos;s core library. All {fmt(LIBRARY.constantsChecked)} constants of the library and its
          demonstrations are accepted by the six kernels, and leanchecker replays all {LIBRARY.modulesReplayed} modules. Candidates may import
          it; the judge vendors the exact version and every Passport records it.
        </p>
        <p>
          A Compound candidate whose three sequence bounds come from the library is VERIFIED, eight of eight requirements, on the deployed
          judge (Passport{" "}
          <Link className="hash" href={`/passport/${LIBRARY.compoundLivePassport}`}>
            {LIBRARY.compoundLivePassport.slice(0, 16)}
          </Link>
          , <a href={githubFile(LIBRARY.compoundLivePassportFile)}>committed</a>). The build team wrote it from the reference solution (
          <a href={githubFile(LIBRARY.compoundFixture)}>compound_lib.lean</a>). No Muse run has proved Compound yet: in{" "}
          <a href={githubFile(`${LIBRARY_RUN.source}/README.md`)}>{LIBRARY_RUN.source}</a>, {count(libRuns)} runs of Muse with ProofForge, the planner and
          the library proved at most {LIBRARY_COMPOUND.bestProved} of the eight requirements and{" "}
          {LIBRARY_COMPOUND.runsProvingABound === 0 ? "none" : LIBRARY_COMPOUND.runsProvingABound} of the three sequence bounds. With the
          library, the planner arm verified {listWords(verifiedEvery)} in every run.
        </p>
        <p className="small muted" style={{ margin: 0 }}>
          <a href={githubFile("lib/README.md")}>lib/README.md</a> lists every module, the axiom audit and the kernel check.
        </p>
      </div>
    </section>
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
            </div>
            <p className="tl-detail">{v.detail}</p>
            <pre className="tl-code">
              <code>{v.code.join("\n")}</code>
            </pre>
            <p className="tl-finding">
              <Status value={v.verdict} /> {v.finding}
            </p>
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
            {r.model}, {r.tier} tier, {r.planner ? `planned by ${r.planner}` : "harness without a planner"}
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
  if (!rc) return null;
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
      {f.context ? <p className="case-context small muted">{f.context}</p> : null}
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
          <Seal size={28} />
          <Status value="VERIFIED" />
          <span>
            {f.repair.model} repair{f.repair.planner ? `, planned by ${f.repair.planner}` : ""}
          </span>
        </div>
        <p>
          The repair {f.repair.change}. It proves all {requirementCount(f.repair.passport)} requirements, among them that{" "}
          {lowerFirst(f.property)} Attempt {f.repair.attempt}, {fmt(f.repair.seconds)} s, {usd(f.repair.usdList)} at list prices.
        </p>
        <p className="small">
          <PassportLink p={f.repair.passport} />
        </p>
      </div>
      {f.unresolved.length ? <Unresolved f={f} /> : null}
      <RealCode f={f} />
    </article>
  );
}

function Unresolved({ f }: { f: Flagship }) {
  const total = requirementCount(f.repair.passport);
  return (
    <div className="verdict-box" data-verdict="UNRESOLVED">
      <div className="verdict-head">
        <Status value="UNRESOLVED" />
        <span>Earlier attempts: tests passed, no Passport</span>
      </div>
      <p>
        {capital(count(f.unresolved.length))} earlier Muse attempts produced code whose rebuilt executable passed all{" "}
        {fmt(f.repair.propertyCases)} property cases, but none proved every requirement, so ProofForge issued no VERIFIED Passport:{" "}
        {andListOf(f.unresolved.map((u) => `${u.label} proved ${u.proved} of ${total} before its ${u.stop}`))}.
      </p>
      <p className="small">
        {f.unresolved.map((u, i) => (
          <span key={u.run}>
            {i ? ", " : null}
            <PassportLink p={u.passport} label={u.label} />
          </span>
        ))}
      </p>
    </div>
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
            <li>The deployed Solidity and Move code is not itself proved.</li>
            <li>
              The Lean ports are reviewed hand translations. They are tested against the real code on the stated inputs (
              {listWords(FLAGSHIPS.flatMap((f) => (f.realCode ? [`${fmt(f.realCode.total)} ${f.realCode.unit} for ${f.incident}`] : [])))}
              ); the translation is not machine-checked.
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
        five. Every bad case is a seeded attack of the E2 suite.
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
        cases. Muse Spark 1.3 produces repairs that pass the full check in every setup. The {E1.tasks * E1.arms.length}{" "}
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
