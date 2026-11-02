import type { Metadata } from "next";
import Link from "next/link";
import { CREATOR } from "@/components/CreatorBand";
import { Email } from "@/components/Email";
import { KpiStrip } from "@/components/FrontierViz";
import { inlineCode } from "@/components/InlineCode";
import { Pipeline } from "@/components/Pipeline";
import { BUILT, DEPENDENCIES, KERNELS, KERNELS_SENTENCE, META, ORIGIN } from "@/lib/about";
import { HACKATHON, SCOPE } from "@/lib/contribution";
import { FLAGSHIPS, HEADLINE, REPO_URL, SUMMARY, githubFile, lossTotalPhrase } from "@/lib/flagships";
import { LIBRARY_COUNTS } from "@/lib/library-data";
import { WINS } from "@/lib/wins-data";
import "./about.css";

const description = `Who built ProofForge and why: ${CREATOR.name} built it with Meta's Muse models during the ${HACKATHON.event}. ${HEADLINE}`;

export const metadata: Metadata = {
  title: "About, ProofForge",
  description,
  openGraph: { title: "About ProofForge", description },
};

const fmt = (n: number) => n.toLocaleString("en-US");
const longDay = (iso: string) =>
  new Date(`${iso}T00:00:00Z`).toLocaleDateString("en-GB", { day: "numeric", month: "long", year: "numeric", timeZone: "UTC" });

export default function AboutPage() {
  const c = WINS.catches;
  return (
    <main id="main" className="page about-page">
      <section className="ab-hero" aria-labelledby="ab-title">
        <div className="ab-hero-text">
          <h1 id="ab-title">About ProofForge</h1>
          <p className="ab-headline">{HEADLINE}</p>
          <p className="lead">{SUMMARY}</p>
        </div>
        <aside className="ab-person" aria-labelledby="ab-person-name">
          <span className="ab-person-mark" aria-hidden="true">
            <img className="lockup-primary" src="/brand/proofforge-icon-primary.svg" alt="" width={56} height={56} />
            <img className="lockup-reversed" src="/brand/proofforge-icon-reversed.svg" alt="" width={56} height={56} />
          </span>
          <h2 id="ab-person-name" className="ab-person-name">
            {CREATOR.name}
          </h2>
          <p className="ab-person-event">
            Built ProofForge with Meta&apos;s Muse models during the {HACKATHON.event}, {longDay(HACKATHON.firstCommit)} to{" "}
            {longDay(HACKATHON.submissionsDue)}.
          </p>
          <ul className="ab-person-links">
            <li>
              <a href={CREATOR.github}>
                <svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true">
                  <path
                    fill="currentColor"
                    d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27.68 0 1.36.09 2 .27 1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.013 8.013 0 0 0 16 8c0-4.42-3.58-8-8-8Z"
                  />
                </svg>
                github.com/{CREATOR.githubUser}
              </a>
            </li>
            <li>
              <svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true">
                <path fill="none" stroke="currentColor" strokeWidth="1.4" d="M1.5 3.5h13v9h-13zM1.5 3.5 8 9l6.5-5.5" />
              </svg>
              <Email />
            </li>
          </ul>
        </aside>
      </section>

      <section className="ab-section" aria-labelledby="ab-why">
        <h2 id="ab-why">Why it exists: financial code fails in ways tests miss</h2>
        <div className="ab-why">
          <div className="ab-why-text">
            <p>
              The payout task in <code>formal/</code> is a splitter whose bug loses a cent: $1.00 to three recipients pays 33 + 33 + 33, and the
              existing unit tests pass. In the E2 suite, one seeded attack pays seven or more recipients without the remainder; the test generator
              never produces more than five, so the rebuild and its tests accept it. A proof covers every input; tests cover the inputs someone
              thought to generate.
            </p>
            <p>
              ProofForge turns Meta&apos;s Muse models into provers of financial code. Each requirement is written once as a Lean 4 statement and
              locked by hash. A fix counts only when its proof of every locked requirement is checked by six independent kernels in a
              fresh sandbox, <code>leanchecker</code> replays it, an axiom audit passes and the executable rebuilt from the same source passes
              property tests. No proof, no merge.
            </p>
          </div>
          <div className="ab-split" role="img" aria-label="$1.00 to three recipients: the buggy split pays 33, 33 and 33 cents and loses 1; the repaired split pays 34, 33 and 33.">
            <p className="ab-split-title">$1.00 to three recipients</p>
            {(
              [
                ["Buggy split", [33, 33, 33], "1 cent lost"],
                ["Repaired split", [34, 33, 33], "every cent paid"],
              ] as const
            ).map(([label, parts, note]) => (
              <div key={label} className="ab-split-row">
                <span className="ab-split-label">{label}</span>
                <span className="ab-split-bar">
                  {parts.map((p, i) => (
                    <span key={i} className="ab-split-part" style={{ flexGrow: p }}>
                      {p}
                    </span>
                  ))}
                  {parts.reduce((a, b) => a + b, 0) < 100 ? <span className="ab-split-lost" style={{ flexGrow: 100 - parts.reduce((a, b) => a + b, 0) }} /> : null}
                </span>
                <span className="ab-split-note">{note}</span>
              </div>
            ))}
          </div>
        </div>
        <Pipeline className="ab-pipeline" />
        <KpiStrip
          label="ProofForge in figures"
          items={[
            { value: lossTotalPhrase("more than").replace(/^more than /, ""), label: `and more, taken or lost in the ${FLAGSHIPS.length} real failures on the home page, as their sources report`, href: "/#cases" },
            { value: `${c.badAccepted.proofforge} of ${c.badCases}`, label: `seeded bad candidates accepted; ordinary checking accepted ${c.badAccepted.ordinary}` },
            { value: String(KERNELS.length), label: "independent kernels check every proof" },
            { value: fmt(WINS.counts.runs), label: `measured runs in ${WINS.counts.comparisons} comparisons of Meta models`, href: "/frontier" },
            { value: fmt(LIBRARY_COUNTS.theorems), label: "theorems in ProofForgeFin, the library candidates may import" },
          ]}
        />
        <p className="muted small ab-scope">{SCOPE}</p>
      </section>

      <section className="ab-section" aria-labelledby="ab-built">
        <h2 id="ab-built">Built during the event</h2>
        <p className="ab-lead">
          Everything in the repository was created on or after {longDay(HACKATHON.firstCommit)}, the kickoff of the {HACKATHON.event}.{" "}
          {inlineCode(ORIGIN.started)} {ORIGIN.agents} {ORIGIN.noEarlierCode}
        </p>
        <ol className="ab-timeline" aria-label="The event">
          <li>
            <span className="ab-tl-mark" aria-hidden="true" />
            <span className="ab-tl-when">{ORIGIN.kickoff}</span>
            <span className="ab-tl-what">Kickoff</span>
          </li>
          <li>
            <span className="ab-tl-mark" aria-hidden="true" />
            <span className="ab-tl-when">{ORIGIN.firstCommitAt}</span>
            <span className="ab-tl-what">
              First commit <a href={`${REPO_URL}/commit/${ORIGIN.firstCommit}`}>{ORIGIN.firstCommit}</a>
            </span>
          </li>
          <li>
            <span className="ab-tl-mark ab-tl-end" aria-hidden="true" />
            <span className="ab-tl-when">{ORIGIN.submissionsDue}</span>
            <span className="ab-tl-what">Submissions due</span>
          </li>
        </ol>
        <ul className="ab-built" aria-label="Built during the event">
          {BUILT.map((b) => (
            <li key={b}>
              <span>{inlineCode(b.charAt(0).toUpperCase() + b.slice(1))}</span>
            </li>
          ))}
        </ul>
        <details className="ab-details">
          <summary>Not built during the event: the dependencies</summary>
          <div className="table-scroll">
            <table>
              <thead>
                <tr>
                  <th scope="col">Dependency</th>
                  <th scope="col">Use</th>
                </tr>
              </thead>
              <tbody>
                {DEPENDENCIES.map((d) => (
                  <tr key={d.name}>
                    <td>{inlineCode(d.name)}</td>
                    <td>{d.use}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </details>
        <p className="ab-links">
          <a href={githubFile("ORIGIN.md")}>ORIGIN.md</a>
          <a href={REPO_URL}>The repository</a>
          <a href={githubFile("README.md")}>README.md</a>
        </p>
        <p className="muted small">
          ProofForge is open source under the <a href={githubFile("LICENSE")}>Apache License 2.0</a>. The ProofForge name and logo are not
          covered by it; <a href={githubFile("NOTICE")}>NOTICE</a> gives the terms.
        </p>
      </section>

      <section className="ab-section" aria-labelledby="ab-thanks">
        <h2 id="ab-thanks">Acknowledgments</h2>
        <div className="ab-thanks">
          <div className="ab-thanks-card ab-thanks-meta">
            <h3>Meta</h3>
            <p className="muted small">
              For the Muse models, Muse Code and the Meta Model API that every repair, proof and plan here runs on, and, with Cerebral Valley,
              for the {HACKATHON.event}.
            </p>
            <ul>
              {META.map((m) => (
                <li key={m.name}>
                  <strong>{m.name}</strong> {m.role}
                </li>
              ))}
            </ul>
          </div>
          <div className="ab-thanks-card">
            <h3>Lean and the Lean FRO</h3>
            <p className="muted small">
              Lean 4 v4.35.0, its kernel, compiler and Lake, with <code>lake comparator</code> and <code>leanchecker</code>: the judge is built on
              them.
            </p>
            <p className="ab-kernels-lead small">Comparator runs {KERNELS_SENTENCE}.</p>
            <ul className="ab-kernels" aria-label="The six kernels">
              {KERNELS.map((k) => (
                <li key={k}>{k}</li>
              ))}
            </ul>
          </div>
          <div className="ab-thanks-card">
            <h3>Open source underneath</h3>
            <ul>
              {DEPENDENCIES.filter((d) => !/^Lean 4|^Meta Model API/.test(d.name)).map((d) => (
                <li key={d.name}>
                  <strong>{d.name}</strong> {d.use}.
                </li>
              ))}
              <li>
                <strong>Instrument Serif, Space Grotesk, Inter and JetBrains Mono</strong> The type of the identity, under the SIL Open Font License.
              </li>
            </ul>
          </div>
        </div>
      </section>

      <section className="ab-section ab-next" aria-labelledby="ab-next">
        <h2 id="ab-next">Go further</h2>
        <ul className="ab-next-list">
          <li>
            <Link href="/verify">
              <strong>Verify a Passport yourself</strong>
              <span>The commands that rerun every check.</span>
            </Link>
          </li>
          <li>
            <Link href="/methods">
              <strong>Preregistrations and methods</strong>
              <span>Every experiment&apos;s plan, committed before its runs.</span>
            </Link>
          </li>
          <li>
            <Link href="/frontier">
              <strong>The frontier, measured</strong>
              <span>What Meta&apos;s models reach with ProofForge.</span>
            </Link>
          </li>
          <li>
            <Link href="/brand">
              <strong>Brand kit</strong>
              <span>The mark, the palette and the files.</span>
            </Link>
          </li>
        </ul>
      </section>
    </main>
  );
}
