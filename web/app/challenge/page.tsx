import type { Metadata } from "next";
import Link from "next/link";
import { getJson, type TaskSummary } from "@/lib/api";
import { requirementText } from "@/lib/format";
import { githubFile } from "@/lib/flagships";
import { CHALLENGE, TARGET_MS, challengeFacts, recordedLabel } from "@/lib/challenge";
import { ErrorBox, Status } from "@/components/ui";
import { KpiStrip } from "@/components/FrontierViz";
import { ChallengeRunner } from "./ChallengeRunner";
import { RoundTrips } from "./RoundTrips";
import "./challenge.css";

export const dynamic = "force-dynamic";
const description =
  "Challenge a hidden payout variant: ProofForge builds its executable and runs property tests derived from the locked Lean 4 requirements, and returns REFUTED with a concrete witness when a requirement breaks.";

export const metadata: Metadata = {
  title: "Challenge, ProofForge",
  description,
  openGraph: { title: "Challenge, ProofForge", description },
};

const secs = (s: number | null) => (s == null ? "none" : `${s.toFixed(2)} s`);

function Facts() {
  const f = challengeFacts();
  return (
    <KpiStrip
      label="The hidden challenge in figures"
      items={[
        { value: String(f.variants), label: "hidden payout variants", href: "#ch-run" },
        { value: `${f.refuted} of ${f.calls}`, label: "recorded calls of the deployed challenge returned REFUTED with a witness", href: "#ch-record" },
        { value: secs(f.medianSeconds), label: `median round trip of those calls, against the ${TARGET_MS / 1000} s target`, href: "#ch-record" },
        { value: String(f.propertyCases), label: "property cases per check, derived from the locked requirements", href: "#ch-how" },
        { value: `${f.referencesAccepted} of ${f.references}`, label: "reference fixes accepted by the judge, executables passing", href: "#ch-validation" },
      ]}
    />
  );
}

function Validation() {
  const d = CHALLENGE;
  const f = challengeFacts();
  return (
    <section aria-labelledby="ch-validation" className="ch-section">
      <h2 id="ch-validation">How each hidden variant was validated</h2>
      <p className="ch-section-lead">
        Before a variant is served, its metadata, lock and hygiene checks pass, both reference fixes are accepted by the judge with their
        executables passing the property tests, and the buggy start is refuted by the executable check: {f.referencesAccepted} of {f.references}{" "}
        reference fixes accepted, {f.startsRefuted} of {f.variants} buggy starts refuted. The check is never given the issue report; the page opens it only on request, after a check of that variant.
      </p>
      <div className="table-scroll">
        <table className="ch-vtable">
          <caption className="small muted">Validation record per hidden variant, from hidden/&lt;variant&gt;/validation.json</caption>
          <thead>
            <tr>
              <th scope="col">Variant</th>
              <th scope="col">Metadata, lock, hygiene</th>
              <th scope="col">Reference fixes, judge time</th>
              <th scope="col">Buggy start</th>
            </tr>
          </thead>
          <tbody>
            {d.variants.map((v) => (
              <tr key={v.id}>
                <th scope="row">
                  <a href={githubFile(v.validation.source)} className="mono">
                    {v.id}
                  </a>
                </th>
                <td data-label="Metadata, lock, hygiene">
                  {v.validation.checks.filter((c) => c.passed).length} of {v.validation.checks.length} passed
                </td>
                <td data-label="Reference fixes, judge time">
                  {v.validation.references.map((r) => (
                    <span key={r.file} className="ch-ref">
                      <code>{r.file}</code> <Status value={r.judge} /> in {(r.judgeMs / 1000).toFixed(1)} s, executable <Status value={r.binary} />
                    </span>
                  ))}
                </td>
                <td data-label="Buggy start">
                  judge <Status value={v.validation.start.judge} />, executable <Status value={v.validation.start.binary} />
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </section>
  );
}

function Record() {
  const d = CHALLENGE;
  const f = challengeFacts();
  return (
    <section aria-labelledby="ch-record" className="ch-section">
      <h2 id="ch-record">Every recorded call of the deployed challenge</h2>
      <p className="ch-section-lead">
        The reliability runs called the deployed endpoint once per session with <code>{d.reliability.variant}</code>: {f.refuted} of {f.calls} calls
        returned REFUTED with a witness, with round trips from {secs(f.minSeconds)} to {secs(f.maxSeconds)}, median {secs(f.medianSeconds)}. The
        whole axis below is 0.5 s, one fortieth of the {TARGET_MS / 1000} s target. Point at a dot to read it.
      </p>
      <RoundTrips runs={d.reliability.runs} />
      <details className="wins-details strip-more">
        <summary>Every call as text</summary>
        <ul className="ch-calls">
          {d.reliability.runs.map((r) => (
            <li key={r.source}>
              <a href={githubFile(r.source)}>{r.source}</a>, recorded {r.recordedAt} against {r.api}:{" "}
              {r.calls.map((c) => `session ${c.session} ${c.seconds.toFixed(2)} s ${c.refuted ? "REFUTED" : "not refuted"}`).join(", ")}.
            </li>
          ))}
        </ul>
        <p>
          A call counts as refuted when it answered {d.reliability.refutedMeans}, as <a href={githubFile(d.reliability.runner)}>{d.reliability.runner}</a>{" "}
          records it; the round trip is measured by that script around the request. Runs:{" "}
          {d.reliability.runs.map((r) => recordedLabel(r.recordedAt)).join(" and ")}.
        </p>
      </details>
    </section>
  );
}

function How() {
  const d = CHALLENGE;
  return (
    <section aria-labelledby="ch-how" className="ch-section">
      <h2 id="ch-how">What the check runs</h2>
      <p className="ch-section-lead">
        <code>POST /api/challenge</code> in <a href={githubFile(d.server.source)}>{d.server.source}</a> takes the variant&apos;s executable, built
        from its Lean source once and cached by source hash, and runs the payout&apos;s fixed example case and {d.server.propertyCases} generated
        property cases against it, then follow-up cases derived from their outputs. An independent model of the component, the task&apos;s <code>oracle.py</code>, checks every output against the locked
        requirements; the first violation is returned as the witness. The check stops at {d.server.deadlineS} s, and a run without a result is
        UNRESOLVED. This page sends <code>repair: false</code>, so it never starts a model session.
      </p>
      <p className="ch-section-lead">
        The full check, <code>bin/proofforge check</code>, goes further with the same witness: it states the negation of the locked requirement on
        that input as a Lean theorem and checks it with six kernels, <code>leanchecker</code> and the axiom audit (
        <a href={githubFile("docs/COUNTEREXAMPLES.md")}>docs/COUNTEREXAMPLES.md</a>). Every step is described in{" "}
        <a href={githubFile("docs/ARCHITECTURE.md")}>docs/ARCHITECTURE.md</a>. Facts on this page come from{" "}
        <a href={githubFile(d.generator)}>{d.generator}</a>. <Link href="/results">E1 and E2 results</Link>
      </p>
    </section>
  );
}

export default async function ChallengePage() {
  let variants: string[];
  let tasks: TaskSummary[];
  try {
    [variants, tasks] = await Promise.all([getJson<string[]>("/api/challenge/variants"), getJson<TaskSummary[]>("/api/tasks")]);
  } catch (e) {
    return (
      <main id="main" className="page ch-page">
        <h1>Challenge a hidden variant</h1>
        <ErrorBox title="Could not load challenge variants." message={(e as Error).message} />
        <Facts />
        <Record />
        <Validation />
        <How />
      </main>
    );
  }
  const flagship = tasks.find((t) => t.id === "payout-flagship");
  const texts = Object.fromEntries((flagship?.requirements ?? []).map((r) => [r.id, requirementText(r.text, r.id)]));
  return (
    <main id="main" className="page ch-page">
      <h1>Challenge a hidden variant</h1>
      <p className="lead">
        Each variant is a buggy payout component whose bug is not described to the check. ProofForge builds its executable and runs the
        requirement-derived property tests against it. A violation comes with a concrete witness: the input and the output that breaks a locked
        requirement. The target is a witness within 20 seconds. After a check, the variant's issue report opens on request, to compare with the witness.
      </p>
      <Facts />
      <section aria-labelledby="ch-run" className="ch-section">
        <h2 id="ch-run">Pick a variant and run the check</h2>
        <ChallengeRunner variants={variants} requirementTexts={texts} meta={CHALLENGE.variants} propertyCases={CHALLENGE.server.propertyCases} />
      </section>
      <Record />
      <Validation />
      <How />
    </main>
  );
}
