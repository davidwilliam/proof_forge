import Link from "next/link";
import type { Metadata } from "next";
import type { ReactNode } from "react";
import { CheckFix } from "@/components/CheckFix";
import { CreatorBand } from "@/components/CreatorBand";
import { CatchWaffles, KpiStrip, RunStrips } from "@/components/FrontierViz";
import { Pipeline } from "@/components/Pipeline";
import { HeroLenses } from "@/components/HeroLenses";
import { inlineCode } from "@/components/InlineCode";
import { Seal } from "@/components/Seal";
import { Status } from "@/components/ui";
import {
  CETUS_HOTFIX,
  COMPARISON,
  COMPOUND,
  COMPOUND_CASE,
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
import {
  COMPOUND_FRONTIER,
  caseTrail,
  compoundFrontier,
  compoundLead,
  compoundTabLoss,
  compoundTrail,
  homeKpis,
  homeStrips,
  lossParts,
  matrixRows,
  type TrailStep,
} from "@/lib/home-view";
import { LIBRARY_COUNTS } from "@/lib/library-data";
import { PROOF_GRAPH, layoutGraph } from "@/lib/proofgraph";
import { GRAPH_TASK, bellOf, guarantees, layoutLayers } from "@/lib/lenses";
import { holeRun } from "@/lib/hole";
import { EXPECTED_PROJECTS, describeInput, listWords, pendingProjects, type RwProject, type RwVersion } from "@/lib/realworld";
import { HEADLINE_IDS, comparison, countsSentence, headlines, modelName, pValue, runsOf } from "@/lib/wins";
import { WINS } from "@/lib/wins-data";
import { CaseViewer } from "./_home/CaseViewer";
import { CompareMatrix } from "./_home/CompareMatrix";
import "./home.css";

const fmt = (n: number) => n.toLocaleString("en-US");
const usd = (n: number) => `$${n < 0.1 ? n.toFixed(n < 0.045 ? 3 : 2) : n.toFixed(2)}`;
const words = ["no", "one", "two", "three", "four", "five", "six"];
const count = (n: number) => words[n] ?? String(n);
const capital = (s: string) => s.charAt(0).toUpperCase() + s.slice(1);
const lowerFirst = (s: string) => s.charAt(0).toLowerCase() + s.slice(1);
const andListOf = (xs: string[]) => (xs.length <= 1 ? xs.join("") : `${xs.slice(0, -1).join("; ")}; and ${xs[xs.length - 1]}`);

const pr6 = FEATURED.timeline.find((v) => v.key === "pr6")!;
const metaDescription = (() => {
  const { f3 } = compoundFrontier(WINS);
  const oz = comparison(WINS, HEADLINE_IDS.oz);
  return `With ProofForge as its MCP server, Muse Code, Meta's coding agent, running ${modelName(oz.model)} verified ${runsOf(oz.proofforge)} runs on OpenZeppelin Math.sqrt, against ${runsOf(oz.alone)} on its own, and ${runsOf(f3.proofforge)} on Compound Proposal 62, against ${runsOf(f3.alone)}. Locked Lean 4 specifications of ${count(COMPARISON.length)} real financial failures, kernel-checked counterexamples and hash-bound Passports anyone can re-run.`;
})();

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
        <Comparison />

        <section className="home-section" id="check" aria-labelledby="home-check">
          <h2 id="home-check">Check a fix against its locked specification</h2>
          <p className="home-section-lead">
            Pick a real failure and a version of its code, and the ProofForge API judges it now. If the API is slow or down, the panel shows the
            committed Passport of the same file and says so.
          </p>
          <CheckFix />
        </section>

        <Cases />

        <Lift />

        <Library />

        <Trust />

        <Benchmark />

        <RealWorld projects={rw.projects} pending={pendingProjects(rw)} />

        <Evidence />

        <CreatorBand />
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

function PassportLink({ p, label, digits = 12 }: { p: PassportRef; label?: string; digits?: number }) {
  return (
    <a className="passport-link" href={githubFile(p.path)}>
      {label ?? "Passport"} <span className="hash">{p.sha256.slice(0, digits)}</span>
    </a>
  );
}

/** The largest gains of the ledger (results/wins/ledger.json) as run strips, right after the hero, with the ledger's totals and the way to every comparison. */
function HomeWins() {
  return (
    <section className="home-section home-wins" id="wins" aria-labelledby="home-wins">
      <h2 id="home-wins">How far ProofForge takes Meta&apos;s models</h2>
      <p className="home-section-lead">
        The same Meta model on the same tasks and caps, on its own and with ProofForge, both judged against the same locked specification.{" "}
        {countsSentence(WINS)} Every run is in the ledger with its Passport. Below, every dot is a measured run, filled when it ended with a
        VERIFIED Passport.
      </p>
      <KpiStrip items={homeKpis(WINS)} label="The ledger in figures" />
      <div className="hw-strips">
        <RunStrips items={homeStrips(WINS)} />
      </div>
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

const accepted = (r: Runs) => `${r.accepted} of ${r.runs.length}`;
const armName: Record<Runs["arm"], string> = { A0: "alone", A1: "harness", A2: "with Wonder planner" };

function Comparison() {
  const failures = FLAGSHIPS.length;
  const compound = COMPARISON.find((r) => r.key === "compound")!;
  const compoundLibrary = (compound.library?.withLibrary.runs.length ?? 0) + (compound.library?.topdown?.runs.length ?? 0);
  // Tasks where every run of every arm was accepted.
  const easy = COMPARISON.filter((r) => [r.alone, ...r.harness].every((x) => x.accepted === x.runs.length) && !r.library);
  const rows = matrixRows(WINS, FLAGSHIPS);
  const { f3, pooled } = compoundFrontier(WINS);
  return (
    <section className="home-section" id="compare" aria-labelledby="home-compare">
      <h2 id="home-compare">Muse alone and Muse with ProofForge, on the real failures</h2>
      <p className="home-section-lead">
        Every run is Muse Spark 1.3, capped at ${RUN_CAPS.usdList} at list prices and {RUN_CAPS.seconds / 3600} hours, and judged by ProofForge
        against the same locked specification. Each dot is a run, filled when it was accepted; point at a group of dots, or focus it, to read its
        runs.
      </p>
      <details className="hm-more hm-arms">
        <summary>How the arms differ</summary>
        <p>
          Muse alone replies with whole files and sees only Lean&apos;s errors and the axiom audit. With the ProofForge harness it fixes behavior
          against the property tests first, then proves one obligation at a time with snippet checks; the second harness arm adds Muse Wonder 1.0
          as lemma planner. On Compound, Knight and Balancer the counts include{" "}
          <a href={githubFile(`${LIBRARY_RUN.source}/README.md`)}>{LIBRARY_RUN.source}</a>, where the planner arm also imports the ProofForgeFin
          library, and on Compound the runs of Muse Code (Muse Spark 1.3 in Muse Code, on its own and with ProofForge) in frontier-2 and
          frontier-3, at the same caps.
        </p>
      </details>
      <CompareMatrix rows={rows} initial={{ row: rows.findIndex((r) => r.key === "compound"), col: "proofforge", group: "f3-proofforge" }} />
      <div className="compare-notes hm-notes">
        <p className="hm-lead-note">
          <strong>{compoundLead(WINS)}</strong> Both verified runs prove the three sequence bounds (rewards, each account, no backdated rewards)
          that no earlier run of either arm proved, with ProofForgeFin.Accumulator.Market. Preregistered one-sided Fisher exact p ={" "}
          {pValue(f3.test!.p)}; pooled with frontier-2, p = {pValue(pooled.test!.p)} (
          <a href={githubFile(COMPOUND_FRONTIER.readme)}>frontier-3</a>).
        </p>
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
      </div>
      <details className="hm-more">
        <summary>The comparison as a table, the Compound runs before frontier-3 and the loss figures</summary>
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
            Before frontier-3, no run of any method had proved all {compound.requirements} of Compound&apos;s requirements. Muse alone verified{" "}
            {accepted(aloneRuns(compound))} runs,{" "}
            {compound.harness
              .filter((h) => h.arm !== "A2")
              .map((h) => `the harness ${accepted(h)}`)
              .join(", ")}
            , the harness with the planner {accepted(plannerRuns(compound)!)} ({compoundLibrary} of them with the library) and implementation from
            the specification {accepted(compound.implement)}; in frontier-2, Muse Code verified {runsOf(compoundFrontier(WINS).f2.alone)} on its own
            and {runsOf(compoundFrontier(WINS).f2.proofforge)} with ProofForge. The specification is provable: the build team&apos;s proof that uses
            the library is VERIFIED on the deployed judge (
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
            <a href={githubFile("results/counterexamples-1/README.md")}>counterexamples-1</a>,{" "}
            <a href={githubFile(COMPOUND_FRONTIER.earlier)}>frontier-2</a>, <a href={githubFile(COMPOUND_FRONTIER.readme)}>frontier-3</a> and each
            task&apos;s results README.
          </p>
        </div>
      </details>
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
  const mc = row.key === "compound" ? compoundFrontier(WINS) : null;
  return (
    <tr>
      <td className="ledger-incident">
        {f || row.key === COMPOUND.key ? (
          <a href={`#case-${row.key}`}>
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
        {mc ? (
          <span className="compare-arm">
            <strong>{runsOf(mc.pooled.alone)}</strong> Muse Code on its own, frontier-2 and frontier-3
          </span>
        ) : null}
        <strong>{accepted(alone)}</strong>
        <span className="ledger-sub">runs{row.library?.alone ? `, ${row.library.alone.runs.length} of them in library-1` : ""}</span>
      </td>
      <td className="compare-cell" data-label="With the ProofForge harness, accepted">
        {mc ? (
          <>
            <span className="compare-arm">
              <strong>{runsOf(mc.f3.proofforge)}</strong> Muse Code with ProofForge, frontier-3
            </span>
            <span className="compare-arm" data-zero={mc.f2.proofforge.verified === 0 || undefined}>
              <strong>{runsOf(mc.f2.proofforge)}</strong> Muse Code with ProofForge, frontier-2
            </span>
          </>
        ) : null}
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

/** One row of dots, filled for the completed ones. */
function DotRow({ label, on, n, note }: { label: string; on: number; n: number; note?: string }) {
  return (
    <div className="hm-dotrow" role="img" aria-label={`${label}: ${on} of ${n}${note ? `, ${note}` : ""}`}>
      <span className="hm-dotrow-l">{label}</span>
      <span className="hm-dots" aria-hidden="true">
        {Array.from({ length: n }, (_, i) => (
          <span key={i} className={i < on ? "hm-dot hm-dot-on" : "hm-dot"} />
        ))}
      </span>
      <span className="hm-dotrow-n">
        <strong>{on}</strong> of {n}
      </span>
    </div>
  );
}

/** One run's requirements: filled squares for the ones it proved. */
function ReqRow({ label, proved, of, verified }: { label: string; proved: number; of: number; verified: boolean }) {
  return (
    <div className="hm-dotrow" role="img" aria-label={`${label}: ${proved} of ${of} requirements proved${verified ? ", VERIFIED" : ""}`}>
      <span className="hm-dotrow-l">{label}</span>
      <span className="hm-dots" aria-hidden="true">
        {Array.from({ length: of }, (_, i) => (
          <span key={i} className={i < proved ? "hm-sq hm-sq-on" : "hm-sq"} />
        ))}
      </span>
      <span className="hm-dotrow-n">
        <strong>{proved}</strong> of {of}
        {verified ? <span className="hm-verified"> VERIFIED</span> : null}
      </span>
    </div>
  );
}

function Lift() {
  const [open, glimmer] = OPEN_WEIGHTS;
  const repeat = OPEN_WEIGHTS.find((o) => o.key === "spark-open-2");
  const compoundLib = COMPARISON.find((r) => r.key === "compound")!.library!;
  const compoundLibraryRuns = compoundLib.withLibrary.runs.length + (compoundLib.topdown?.runs.length ?? 0);
  const pct = (x: number) => `${x >= 0 ? "+" : ""}${Math.round(x * 100)}`;
  const { f3 } = compoundFrontier(WINS);
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
            <div className="hm-dotrows">
              <DotRow label="Alone" on={open.a0.completed} n={open.a0.n} note="test tasks completed" />
              <DotRow label="With the harness" on={open.a1.completed} n={open.a1.n} note="test tasks completed" />
            </div>
            {repeat ? (
              <p className="small">
                Preregistered repeat with the improved harness: {repeat.a0.completed} to {repeat.a1.completed} of {repeat.a0.n}, and every
                final executable with the harness passed the property tests ({repeat.binaryPass.a1} of {repeat.a1.n}).{" "}
                <a href={githubFile("results/e1-test-open-2/README.md")}>Report</a>
              </p>
            ) : null}
            <details className="hm-more">
              <summary>Tests and serving</summary>
              <p className="small">
                With the harness every final executable passed the property tests ({open.binaryPass.a1} of {open.a1.n}); alone, {open.binaryPass.a0}{" "}
                built. Difference {pct((open.a1.completed - open.a0.completed) / open.paired)} points, 95% interval {pct(open.ci95[0])} to{" "}
                {pct(open.ci95[1])}, McNemar p = {open.mcnemarP.toFixed(2)}.
              </p>
              <p className="small muted">
                {open.serving}. <a href={githubFile(open.source.replace("e1.json", "e1.md"))}>Report</a>
              </p>
            </details>
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
            <div className="hm-dotrows">
              <DotRow label="Alone" on={glimmer.a0.completed} n={glimmer.a0.n} note="test tasks completed" />
              <DotRow label="With the harness" on={glimmer.outage?.a1Completed ?? glimmer.a1.completed} n={glimmer.outage?.a1N ?? glimmer.a1.n} note="test tasks completed, runs ended by the outage excluded" />
            </div>
            <details className="hm-more">
              <summary>Tests, the outage and serving</summary>
              <p className="small">
                Incomplete: the GPU host paused the workspace after 31 of 60 runs were scored, and {glimmer.outage?.runs.length} harness runs it
                ended are excluded ({glimmer.a1.completed} of {glimmer.a1.n} counting them). Alone, no version compiled; with the harness{" "}
                {glimmer.binaryPass.a1} final executables passed the property tests. McNemar p = {glimmer.mcnemarP.toFixed(2)} on {glimmer.paired}{" "}
                paired tasks.
              </p>
              <p className="small muted">
                {capital(glimmer.serving)}. <a href={githubFile(glimmer.source.replace("e1.json", "README.md"))}>Report</a>
              </p>
            </details>
          </article>
        ) : null}
        <article className="card lift-card">
          <h3>Muse Wonder as planner</h3>
          <p className="lift-figure">Requirements proved per run, harness alone (A1) and with the planner (A2)</p>
          {PLANNER.map((p) => (
            <div key={p.task} className="hm-dotrows">
              <p className="hm-dotrows-h">{p.incident}</p>
              {p.a1.map((n, i) => (
                <ReqRow key={`a1-${i}`} label={`A1, run ${i + 1}`} proved={n} of={p.requirements} verified={false} />
              ))}
              {p.a2.map((n, i) => (
                <ReqRow key={`a2-${i}`} label={`A2, run ${i + 1}`} proved={n} of={p.requirements} verified={p.a2Accepted > 0 && i === p.a2.length - 1 && n === p.requirements} />
              ))}
            </div>
          ))}
          <details className="hm-more">
            <summary>The runs, with the library and since</summary>
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
              further runs, and Compound in none of {compoundLibraryRuns}. Compound was then verified by Muse Code with ProofForge in frontier-3,{" "}
              {runsOf(f3.proofforge)} runs.
            </p>
            <p className="small muted">
              Muse alone was also accepted on Knight in one of two runs. <a href={githubFile("results/compound-1/README.md")}>Compound runs</a>,{" "}
              <a href={githubFile("results/knight-1/README.md")}>Knight runs</a>,{" "}
              <a href={githubFile(`${LIBRARY_RUN.source}/README.md`)}>library-1</a>, <a href={githubFile(COMPOUND_FRONTIER.readme)}>frontier-3</a>
            </p>
          </details>
        </article>
      </div>
    </section>
  );
}

function Library() {
  const L = LIBRARY_COUNTS;
  const compound = COMPARISON.find((r) => r.key === "compound")!.library!;
  const libRuns = compound.withLibrary.runs.length + (compound.topdown?.runs.length ?? 0);
  const verifiedEvery = COMPARISON.filter((r) => r.library && r.library.withLibrary.accepted === r.library.withLibrary.runs.length).map((r) =>
    shortIncident(r.incident),
  );
  const { f3 } = compoundFrontier(WINS);
  return (
    <section className="home-section hm-lib" id="library" aria-labelledby="home-library">
      <h2 id="home-library">ProofForgeFin, the proved library behind the judge</h2>
      <p className="home-section-lead">
        Floor and ceiling division, fixed point at any scale, share accounting, runs of operations with invariants over every reachable state,
        and conservation over accounts, with no dependency beyond Lean&apos;s core library. With it, Muse Code with ProofForge verified Compound
        in {runsOf(f3.proofforge)} frontier-3 runs.
      </p>
      <KpiStrip
        label="ProofForgeFin in figures"
        items={[
          { value: fmt(L.theorems), label: "theorems" },
          { value: fmt(L.definitions), label: "definitions" },
          { value: String(L.files), label: "Lean files" },
          { value: fmt(L.latestFullRun.safeConstants), label: "constants of the library and its demonstrations, accepted by all six kernels" },
          { value: fmt(L.demoTheorems), label: `theorems in ${L.demoFiles} files of demonstrations` },
        ]}
      />
      <details className="hm-more">
        <summary>What the library holds, how it is checked, and Compound with it</summary>
        <div className="library">
          <p>
            {fmt(L.theorems)} theorems and {fmt(L.definitions)} definitions in {L.files} Lean files: floor and ceiling division, fixed point at
            any scale, share accounting, runs of operations with invariants over every reachable state, and conservation over accounts, with no
            dependency beyond Lean&apos;s core library. All {fmt(L.latestFullRun.safeConstants)} safe constants of the library and its
            demonstrations are accepted by the six kernels, with leanchecker exiting 0, in the latest full run{" "}
            <a href={githubFile(L.latestFullRun.source)}>lib/README.md</a> reports (with the additions of library-compound-gaps-1). The last full
            run committed with its record checked {fmt(L.committedFullRun.safeConstants)}, and leanchecker replayed all{" "}
            {L.committedFullRun.modulesReplayed} modules (<a href={githubFile(L.committedFullRun.file)}>{L.committedFullRun.file}</a>); the{" "}
            {fmt(L.latestModuleRun.constants)} constants of {listWords(L.latestModuleRun.modules)} with the additions were checked on their own (
            <a href={githubFile(L.latestModuleRun.file)}>{L.latestModuleRun.file}</a>). Candidates may import it; the judge vendors the exact
            version and every Passport records it.
          </p>
          <p>
            In <a href={githubFile(COMPOUND_FRONTIER.readme)}>frontier-3</a>, every ProofForge run imported ProofForgeFin.Accumulator.Market, and
            Muse Code with ProofForge verified Compound in {runsOf(f3.proofforge)} runs; both verified runs prove the three sequence bounds with it.{" "}
            <a href={githubFile(COMPOUND_FRONTIER.gaps)}>library-compound-gaps-1</a> reads the runs that did not verify and adds the list glue
            they wrote to the library. A Compound candidate whose three sequence bounds come from the library is VERIFIED, eight of eight
            requirements, on the deployed judge (Passport{" "}
            <Link className="hash" href={`/passport/${LIBRARY.compoundLivePassport}`}>
              {LIBRARY.compoundLivePassport.slice(0, 16)}
            </Link>
            , <a href={githubFile(LIBRARY.compoundLivePassportFile)}>committed</a>). The build team wrote it from the reference solution (
            <a href={githubFile(LIBRARY.compoundFixture)}>compound_lib.lean</a>). Before frontier-3, in{" "}
            <a href={githubFile(`${LIBRARY_RUN.source}/README.md`)}>{LIBRARY_RUN.source}</a>, {count(libRuns)} runs of Muse with ProofForge, the
            planner and the library proved at most {LIBRARY_COMPOUND.bestProved} of the eight requirements and{" "}
            {LIBRARY_COMPOUND.runsProvingABound === 0 ? "none" : LIBRARY_COMPOUND.runsProvingABound} of the three sequence bounds. With the
            library, the planner arm verified {listWords(verifiedEvery)} in every run.
          </p>
          <p className="small muted" style={{ margin: 0 }}>
            <a href={githubFile("lib/README.md")}>lib/README.md</a> lists every module, the axiom audit and the kernel check.
          </p>
        </div>
      </details>
    </section>
  );
}

function minutesBetween(a: string, b: string) {
  return (Date.parse(b) - Date.parse(a)) / 60000;
}

function longDate(iso: string) {
  return new Date(`${iso}T00:00:00Z`).toLocaleDateString("en-GB", { day: "numeric", month: "long", year: "numeric", timeZone: "UTC" });
}

/** The incidents, featured first and Compound Proposal 62 last, as one viewer: a tab per incident with its loss and verdict trail, a panel per incident. */
function Cases() {
  const cases = [FEATURED, ...FLAGSHIPS.filter((f) => f !== FEATURED)];
  const compound = compoundTrail(WINS);
  return (
    <section className="home-section" id="cases" aria-labelledby="home-cases">
      <h2 id="home-cases">{listWords([...cases.map((f) => f.incident), COMPOUND.incident])}, step by step</h2>
      <p className="home-section-lead">
        For each incident, the reported loss, every version of the code against the same locked requirements (one square per requirement:
        red when refuted, green when proved, filled in the text colour when an earlier attempt proved it without reaching a Passport, outlined when not proved) and the real code run against them. The attack itself is under each case; for {COMPOUND.incident}, what the proofs do not cover.
      </p>
      <CaseViewer
        keys={[...cases.map((f) => f.key), COMPOUND.key]}
        tabs={[
          ...cases.map((f) => <CaseTab key={f.key} incident={f.incident} year={f.year} loss={lossParts(f.loss.amount)} trail={caseTrail(f)} />),
          <CaseTab key={COMPOUND.key} incident={COMPOUND.incident} year={Number(COMPOUND.date.slice(0, 4))} loss={compoundTabLoss()} trail={compound} />,
        ]}
        panels={[...cases.map((f) => <CasePanel key={f.key} f={f} />), <CompoundPanel key={COMPOUND.key} trail={compound} />]}
      />
    </section>
  );
}

function CaseTab({ incident, year, loss, trail }: { incident: string; year: number; loss: { qualifier: string; figure: string }; trail: TrailStep[] }) {
  return (
    <>
      <span className="cv-tab-name">
        {incident} <span className="cv-tab-year">{year}</span>
      </span>{" "}
      <span className="cv-tab-loss">
        {loss.qualifier ? <span className="cv-tab-q">{loss.qualifier} </span> : null}
        {loss.figure}
      </span>{" "}
      <span className="cv-tab-trail" aria-hidden="true">
        {trail.map((s) => (
          <span key={s.key} className="cv-v" data-v={s.verdict} />
        ))}
      </span>
    </>
  );
}

/** A requirement per square, refuted first, then proved, then not proved; the words carry the counts. */
function ReqMarks({ s }: { s: TrailStep }) {
  const session = s.provedInSession ?? 0;
  const marks = [
    ...Array<string>(s.counts.refuted).fill("REFUTED"),
    ...Array<string>(s.counts.verified).fill("VERIFIED"),
    ...Array<string>(Math.min(session, s.counts.unresolved)).fill("SESSION"),
    ...Array<string>(s.counts.unresolved - Math.min(session, s.counts.unresolved)).fill("UNRESOLVED"),
  ];
  const words = [
    s.counts.refuted ? `${s.counts.refuted} refuted` : null,
    s.counts.verified ? `${s.counts.verified} proved` : null,
    session ? `${session} proved in its session without a Passport` : null,
    s.counts.unresolved - session > 0 ? `${s.counts.unresolved - session} not proved` : null,
  ].filter(Boolean);
  return (
    <span className="tr-marks" role="img" aria-label={`${s.total} requirements: ${words.join(", ")}`}>
      <span className="tr-squares" aria-hidden="true">
        {marks.map((m, i) => (
          <span key={i} className="tr-sq" data-s={m} />
        ))}
      </span>
      <span className="tr-count">
        {s.verdict === "VERIFIED"
          ? `${s.counts.verified} of ${s.total} proved`
          : s.verdict === "REFUTED"
            ? `${s.counts.refuted} of ${s.total} refuted`
            : `${session} of ${s.total} proved in its session, no Passport`}
      </span>
    </span>
  );
}

function CasePanel({ f }: { f: Flagship }) {
  const featured = f === FEATURED;
  const trail = caseTrail(f);
  const merged = f.timeline.filter((v) => v.merged);
  const gap = merged.length >= 2 ? Math.round(minutesBetween(merged[0]!.merged!, merged[merged.length - 1]!.merged!) / 10) * 10 : null;
  return (
    <article className="cp" aria-labelledby={`cp-title-${f.key}`}>
      <header className="cp-head">
        <div className="cp-loss">
          <p className="cp-loss-fig">{capital(f.loss.amount)}</p>
          <p className="cp-loss-basis">
            {f.loss.basis}.{" "}
            {f.loss.citations.map((c, i) => (
              <span key={c.url}>
                {i ? ", " : null}
                <a href={c.url}>{c.label}</a>
              </span>
            ))}
          </p>
        </div>
        <div className="cp-what">
          <h3 id={`cp-title-${f.key}`}>
            {f.incident}, {f.year}
            {featured ? ": four versions of one function, one locked statement" : ""}
          </h3>
          {featured ? (
            <p className="cp-bug">
              On {longDate(f.date)} an attacker drained the {f.system}: {f.loss.amount} {f.loss.basis}. {f.bug} {f.incident} merged a hotfix that
              day and a final fix {gap ? `about ${gap} minutes later` : "later"}. ProofForge checked all three, and an independent Muse Spark repair
              of the original, against the same locked Lean statement: four versions of its overflow check, one locked specification of{" "}
              {count(requirementCount(f.repair.passport))} requirements.
            </p>
          ) : (
            <p className="cp-bug">{f.bug}</p>
          )}
          {f.context ? <p className="cp-context">{f.context}</p> : null}
        </div>
      </header>

      <ol className="tr" aria-label={`${f.incident}: the versions of the code and their verdicts`}>
        {trail.map((s, i) => {
          const v = f.timeline.find((x) => x.key === s.key);
          return (
            <li key={s.key} className="tr-step" data-verdict={s.verdict} data-author={v ? (v.commit ? "upstream" : "muse") : s.key === "repair" ? "muse" : undefined}>
              {i > 0 ? <span className="tr-arrow" aria-hidden="true" /> : null}
              <p className="tr-title">
                {s.title} <Status value={s.verdict} />
              </p>
              <p className="tr-detail">{s.detail}</p>
              {v ? <code className="tr-code">{v.code.join("; ")}</code> : null}
              <ReqMarks s={s} />
              {v ? <p className="tr-short">{v.short}</p> : null}
              {s.passport ? (
                <p className="tr-foot">
                  <PassportLink p={s.passport} />
                </p>
              ) : null}
            </li>
          );
        })}
      </ol>

      {featured ? <FeaturedDetail f={f} /> : <CaseVerdicts f={f} />}

      <div className="cp-grid">
        <RealCode f={f} />
        {featured ? <RepairFacts f={f} /> : <Attack f={f} />}
      </div>
    </article>
  );
}

/** What the kernel checked on each version of the featured incident. */
function FeaturedDetail({ f }: { f: Flagship }) {
  return (
    <details className="hm-more">
      <summary>What the check shows on each version, with the commits and Passports</summary>
      <ul className="cp-findings">
        {f.timeline.map((v) => (
          <li key={v.key}>
            <strong>{v.title}</strong> ({v.detail}): <Status value={v.verdict} /> {v.finding}
            {v.key === "pr6" ? (
              <>
                {" "}
                The counterexample is a Lean theorem, <code>{CETUS_HOTFIX.statement}</code>, accepted by all {CETUS_HOTFIX.kernels} kernels.
              </>
            ) : null}{" "}
            <PassportLink p={v.passport} /> <span className="hash muted">{v.commit ? `commit ${v.commit.slice(0, 7)}` : `run ${f.repair.run.split("/").pop()}`}</span>
          </li>
        ))}
      </ul>
      <p className="small">
        <PassportLink p={pr6.passport} label="Hotfix Passport" /> <PassportLink p={f.repair.passport} label="Muse repair Passport" />
      </p>
    </details>
  );
}

/** The refutation of the vulnerable code and the verified repair, side by side. */
function CaseVerdicts({ f }: { f: Flagship }) {
  return (
    <div className="cp-verdicts">
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
    </div>
  );
}

/**
 * Compound Proposal 62, the sixth real failure: not a flagship record (its loss is not in the total),
 * shown with the same structure from COMPOUND and COMPOUND_CASE (lib/contribution.ts) and the
 * frontier-2 and frontier-3 counts of the wins ledger.
 */
function CompoundPanel({ trail }: { trail: TrailStep[] }) {
  const c = COMPOUND;
  const [figure, ...rest] = c.loss.amount.split(", ");
  return (
    <article className="cp" aria-labelledby={`cp-title-${c.key}`}>
      <header className="cp-head">
        <div className="cp-loss">
          <p className="cp-loss-fig">{capital(figure!)}</p>
          <p className="cp-loss-basis">
            {rest.join(", ")}, {c.loss.basis}.{" "}
            {COMPOUND_CASE.citations.map((s, i) => (
              <span key={s.url}>
                {i ? ", " : null}
                <a href={s.url}>{s.label}</a>
              </span>
            ))}
          </p>
        </div>
        <div className="cp-what">
          <h3 id={`cp-title-${c.key}`}>
            {c.incident}, {c.date.slice(0, 4)}
          </h3>
          <p className="cp-bug">{inlineCode(c.bug)}</p>
        </div>
      </header>

      <ol className="tr" aria-label={`${c.incident}: the versions of the code and their verdicts`}>
        {trail.map((s, i) => (
          <li key={s.key} className="tr-step" data-verdict={s.verdict} data-author={s.author}>
            {i > 0 ? <span className="tr-arrow" aria-hidden="true" /> : null}
            <p className="tr-title">
              {s.title} <Status value={s.verdict} />
            </p>
            <p className="tr-detail">{s.detail}</p>
            {s.runs ? (
              <p className="tr-count tr-runs">
                {s.runs.verified} of {s.runs.runs} runs verified
              </p>
            ) : null}
            {s.passport ? <ReqMarks s={s} /> : null}
            {s.runs ? <p className="tr-short">{s.runs.text}</p> : null}
            {s.passport ? (
              <p className="tr-foot">
                {s.passports ? (
                  s.passports.map((m, j) => (
                    <span key={m.label}>
                      {j ? " " : null}
                      <PassportLink p={m.passport} label={m.label} />
                    </span>
                  ))
                ) : (
                  <PassportLink p={s.passport} />
                )}
              </p>
            ) : null}
          </li>
        ))}
      </ol>

      <CompoundVerdicts trail={trail} />

      <div className="cp-grid">
        <CompoundRealCode />
        <div className="card cp-attack">
          <h4>What the proofs do not cover</h4>
          <ul className="cp-findings">
            {c.notProved.map((n) => (
              <li key={n}>{n}</li>
            ))}
          </ul>
          <p className="small muted" style={{ margin: 0 }}>
            <a href={githubFile(c.readme)}>Task README</a>
          </p>
        </div>
      </div>
    </article>
  );
}

/** The refuted Proposal 62 port and the verified Muse Code repairs of frontier-3. */
function CompoundVerdicts({ trail }: { trail: TrailStep[] }) {
  const c = COMPOUND;
  const C = COMPOUND_CASE;
  const { f3, model } = compoundFrontier(WINS);
  const total = trail.find((s) => s.key === "proofforge")!.total;
  return (
    <div className="cp-verdicts">
      <div className="verdict-box" data-verdict="REFUTED">
        <div className="verdict-head">
          <Status value="REFUTED" />
          <span>{c.vulnerable.label}</span>
        </div>
        <p>{c.vulnerable.finding}</p>
        <p className="small">
          <a href={githubFile(c.vulnerable.witness)}>Kernel-checked counterexample</a> and <PassportLink p={C.port} />
        </p>
      </div>
      <div className="verdict-box" data-verdict="VERIFIED">
        <div className="verdict-head">
          <Seal size={28} />
          <Status value="VERIFIED" />
          <span>{model} in Muse Code with ProofForge</span>
        </div>
        <p>
          Verified in {runsOf(f3.proofforge)} runs of frontier-3, at {listWords(C.repairs.map((r) => usd(r.usdList)))} at list prices. Both
          prove all {total} requirements, among them the three bounds over any sequence of operations ({listWords(C.bounds)}) that no earlier
          run of either arm proved. {c.property.requirement} says that {lowerFirst(c.property.text)}
        </p>
        <p className="small">
          {C.repairs.map((r, i) => (
            <span key={r.run}>
              {i ? " " : null}
              <PassportLink p={r.passport} label={r.run} digits={16} />
            </span>
          ))}
        </p>
      </div>
    </div>
  );
}

function CompoundRealCode() {
  const rc = COMPOUND.realCode;
  const rows: RealCodeRow[] = rc.rows.map((r) => ({ label: r.code, commit: null, violating: r.violating, sameAsPort: null, sameAsProved: null, note: r.note }));
  return (
    <div className="card realcode">
      <h3>Against the real Solidity code</h3>
      <p className="small muted">{rc.method}</p>
      <ul className="bars">
        {rows.map((row) => (
          <RealBar key={row.label} row={row} total={rc.sequences} unit="sequences" />
        ))}
      </ul>
      <p className="small muted" style={{ margin: "14px 0 0" }}>
        <a href={githubFile(rc.report)}>Report</a>
      </p>
    </div>
  );
}

function Attack({ f }: { f: Flagship }) {
  if (!f.attack.length) return null;
  return (
    <div className="card cp-attack">
      <h4>The attack, with the state after each step</h4>
      <details className="hm-more">
        <summary>
          {capital(count(f.attack.length))} steps: {f.attack[0]!.text}
        </summary>
        <ol className="attack">
          {f.attack.map((s, i) => (
            <li key={i}>
              <span>{s.text}</span>
              {s.after ? <span className="attack-after">{s.after}</span> : null}
            </li>
          ))}
        </ol>
      </details>
    </div>
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

/** What VERIFIED takes, the seeded attacks it stops, and what is proved and what is not. */
function Trust() {
  const e2 = (key: string) => E2.arms.find((a) => a.key === key)!;
  const catches = headlines(WINS).find((h) => h.key === "catches")!;
  const reconstruction = FLAGSHIPS.map((f) => f.reconstruction).filter((x): x is string => !!x);
  return (
    <section className="home-section" id="trust" aria-labelledby="trust-title">
      <h2 id="trust-title">What ProofForge checks before it says VERIFIED</h2>
      <p className="home-section-lead">
        Each square is one of the {WINS.catches.badCases} seeded bad candidates of the E2 suite, filled when the check accepted it. None of the
        three rejected any of the {WINS.catches.goodCases} good candidates.
      </p>
      <CatchWaffles e={WINS.catches} />
      <details className="hm-more">
        <summary>What was measured</summary>
        <p>{catches.text}</p>
        <p>{catches.note}</p>
        <p className="win-links">
          {catches.links.map((l) => (
            <a key={l.path} href={githubFile(l.path)}>
              {l.label}
            </a>
          ))}
        </p>
        <p className="trust-e2">
          On {E2.bad} seeded bad repairs, ordinary checking (the build passes, the theorem names exist, the axioms are clean) accepted{" "}
          <strong>{e2("ordinary").badAccepted}</strong>. ProofForge accepted <strong>{e2("proofforge").badAccepted}</strong>, and rejected{" "}
          {e2("proofforge").goodRejected} of {E2.good} correct ones. The bad cases were written by the build team.
        </p>
        <div className="hm-e2">
          <E2Card />
        </div>
      </details>
      <div className="card claims-steps">
        <h3>How a repair counts</h3>
        <Pipeline className="pipeline-lg" />
        <details className="hm-more">
          <summary>The checks in detail, and how the specifications are measured</summary>
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
              <p className="trust-spec">
                The specifications are measured too: changed at one site each, the reference solutions give {fmt(SPEC_STRENGTH.compiled)} compiling
                variants, and the {SPEC_STRENGTH.specifications} locked specifications reject {fmt(SPEC_STRENGTH.rejected)} of them,{" "}
                {fmt(SPEC_STRENGTH.kernelChecked)} with kernel-checked counterexamples. The {SPEC_STRENGTH.survivedDiffers} that pass while behaving
                differently are listed as specification gaps (<a href={githubFile(SPEC_STRENGTH.doc)}>SPEC_STRENGTH.md</a>,{" "}
                <a href={githubFile(`${SPEC_STRENGTH.source}/README.md`)}>results</a>).
              </p>
        </details>
      </div>
      <div className="card hm-claims" id="claims">
        <h3>What is proved, and what is not</h3>
        <div className="hm-claims-cols">
          <div>
              <h4>Proved</h4>
              <ul>
                <li>
                  Each requirement is a Lean 4 statement about the Lean port of the vulnerable logic, locked by hash. A VERIFIED requirement holds
                  for every input, not a sample.
                </li>
                <li>
                  A VERIFIED status comes only from ProofForge&apos;s own check: <code>lake comparator --paranoid</code> with six kernels in a fresh
                  sandbox, leanchecker, an axiom audit, and property tests on the executable rebuilt from the same source.
                </li>
                <li>Each REFUTED port has a counterexample checked by the Lean kernel.</li>
              </ul>
          </div>
          <div>
              <h4>Not proved</h4>
              <ul>
                <li>The deployed Solidity and Move code is not itself proved.</li>
                <li>
                  The Lean ports are reviewed hand translations. They are tested against the real code on the stated inputs (
                  {listWords(FLAGSHIPS.flatMap((f) => (f.realCode ? [`${fmt(f.realCode.total)} ${f.realCode.unit} for ${f.incident}`] : [])))}); the
                  translation is not machine-checked.
                </li>
                <li>
                  Each port models only the logic its task README names: for example, Euler has one asset and no interest, and Hundred&apos;s borrowing
                  is not modeled.
                </li>
                {reconstruction.map((r) => (
                  <li key={r}>{r}</li>
                ))}
                <li>Loss figures are quoted from the sources each task README cites.</li>
              </ul>
          </div>
        </div>
      </div>
    </section>
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
  const sum = (xs: number[]) => xs.reduce((a, b) => a + b, 0);
  return (
    <figure className="split-mini card" aria-labelledby="split-caption">
      <figcaption id="split-caption">
        The smallest task: a payout splitter pays 100 cents to three recipients. The code under repair loses a cent while each share looks
        right; Muse Spark&apos;s proved repair conserves the total.
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
        A repair counts when the judge accepts the final candidate and its rebuilt executable passes {fmt(E1.propertyCases)} property cases.
        Muse Spark 1.3 produces repairs that pass the full check in every setup. The {E1.tasks * E1.arms.length} runs cost $
        {E1.batchUsdList.toFixed(2)} at standard list prices.
      </p>
    </article>
  );
}

function Benchmark() {
  const splits = [
    { key: "dev", label: "development", n: BENCHMARK.splits.dev },
    { key: "val", label: "validation", n: BENCHMARK.splits.val },
    { key: "test", label: "test", n: BENCHMARK.splits.test },
  ];
  return (
    <section className="home-section" id="benchmark" aria-labelledby="home-breadth">
      <h2 id="home-breadth">
        The benchmark: {BENCHMARK.tasks} repair tasks in {count(BENCHMARK.families.length)} areas
      </h2>
      <p className="home-section-lead">
        Beyond the incidents, the benchmark has {BENCHMARK.splits.dev} development, {BENCHMARK.splits.val} validation and {BENCHMARK.splits.test}{" "}
        test tasks. The test areas never appear in development or in any prompt used to build the agents. Every task has two reference
        solutions, a buggy start candidate and seeded attacks.
      </p>
      <div className="hm-splits" role="img" aria-label={`${BENCHMARK.tasks} tasks: ${splits.map((s) => `${s.n} ${s.label}`).join(", ")}`}>
        {splits.map((s) => (
          <span key={s.key} className="hm-split" data-split={s.key} style={{ flexGrow: s.n }}>
            <strong>{s.n}</strong> {s.label}
          </span>
        ))}
      </div>
      <ul className="families hm-families">
        {BENCHMARK.families.map((x) => (
          <li key={x.key}>
            <span className="hm-tiles" aria-hidden="true">
              {Array.from({ length: x.tasks }, (_, i) => (
                <span key={i} className="hm-tile" />
              ))}
            </span>
            <span>
              <strong>{x.tasks}</strong> {x.label.toLowerCase()}
            </span>
          </li>
        ))}
        {IMPLEMENTS ? (
          <li>
            <span className="hm-tiles" aria-hidden="true">
              {Array.from({ length: IMPLEMENTS.of }, (_, i) => (
                <span key={i} className={i < IMPLEMENTS!.value ? "hm-tile hm-tile-on" : "hm-tile"} />
              ))}
            </span>
            <span>
              <strong>
                {IMPLEMENTS.value} of {IMPLEMENTS.of}
              </strong>{" "}
              {IMPLEMENTS.label}
            </span>
          </li>
        ) : null}
      </ul>
      <div className="home-evidence hm-bench">
        <E1Card />
        <SplitExample />
      </div>
    </section>
  );
}

function RealWorld({ projects, pending }: { projects: RwProject[]; pending: string[] }) {
  const names = [...EXPECTED_PROJECTS.map((e) => e.name), ...projects.map((p) => p.name)].filter((n, i, all) => all.indexOf(n) === i);
  return (
    <section className="home-section" id="released" aria-labelledby="home-realworld">
      <h2 id="home-realworld">Released bugs in {listWords(names)}</h2>
      <p className="home-section-lead">
        These bugs shipped in released versions of open-source money code. Each release&apos;s own code, at a pinned commit, was run on generated
        inputs and its outputs compared with a reference implementation whose requirements are proved in Lean 4. The projects&apos; code was
        tested against the proved reference; it was not itself proved.
      </p>
      {projects.length === 0 ? (
        <div className="notice small muted">
          These results are not in this build yet. They appear here when <code>web/scripts/realworld.mjs</code> has read{" "}
          <code>results/realworld-1/summary.json</code>.
        </div>
      ) : (
        <div className="rw-projects hm-rw">
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
  const pct = v.cases ? (100 * violating) / v.cases : 0;
  return (
    <li className="rw-version">
      <div className="rw-version-head">
        <span className="rw-tag mono">{v.tag}</span>
        {v.commit ? <span className="hash muted">{v.commit.slice(0, 10)}</span> : null}
        <span className="spacer" />
        {violating > 0 ? <Status value="REFUTED" /> : v.cases ? <Status value="PASS" /> : null}
      </div>
      {v.cases != null ? (
        <span className="bar-track hm-rw-bar" aria-hidden="true">
          <span className="bar-fill" data-tone="bad" style={{ width: `${Math.max(pct, violating ? 1 : 0)}%` }} />
        </span>
      ) : null}
      <p className="rw-count">
        {v.status === "fixed" ? "The fixed release. " : v.status === "buggy" ? "Released with the bug. " : null}
        {v.cases != null ? (
          <>
            <strong>{fmt(violating)}</strong> of {fmt(v.cases)} inputs violate a requirement.
          </>
        ) : null}
      </p>
      {violating > 0 && w ? (
        <details className="hm-more rw-witness">
          <summary>An input it fails on</summary>
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
        </details>
      ) : null}
    </li>
  );
}

function shortRef(url: string): string {
  const m = /github\.com\/[^/]+\/[^/]+\/(pull|issues)\/(\d+)/.exec(url);
  if (!m) return url;
  return `${m[1] === "pull" ? "pull request" : "issue"} ${m[2]}`;
}

function Evidence() {
  return (
    <section className="home-section" id="evidence" aria-labelledby="home-next">
      <h2 id="home-next">Check the evidence yourself</h2>
      <div className="home-ctas">
        <a className="home-cta" href={githubFile(FEATURED.repair.passport.path)}>
          <strong>Open the {FEATURED.incident} Passport</strong>
          <span>
            Statuses for all {requirementCount(FEATURED.repair.passport)} requirements, hashes, kernels, axioms and the command that reproduces
            it. sha256 <span className="hash">{FEATURED.repair.passport.sha256.slice(0, 16)}</span>
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
          From a clone of the repository with the pinned Lean image built (see the README). <code>verify</code> rebuilds the project, reruns
          every check and compares each hash and status.
        </p>
        <pre>
          <code>{FLAGSHIPS.map((f) => f.repair.passport.reproduce).join("\n")}</code>
        </pre>
        <p className="muted small" style={{ margin: 0 }}>
          For agents: <a href="/llms.txt">llms.txt</a> and <a href="/evidence.json">evidence.json</a> list every claim, figure, Passport hash,
          source file and command on this page.
        </p>
      </div>
      <div className="hero-facts hm-origin">
        <p>
          Built during the {HACKATHON.event}: everything in the repository, from the judge, the Passport and the counterexample stage to the
          real-world tasks, the ProofForgeFin library and this site, was created on or after the day of the first commit,{" "}
          {longDay(HACKATHON.firstCommit)}; submissions close {longDay(HACKATHON.submissionsDue)} (<a href={githubFile("ORIGIN.md")}>ORIGIN.md</a>).
        </p>
        <p>{SCOPE}</p>
      </div>
    </section>
  );
}
