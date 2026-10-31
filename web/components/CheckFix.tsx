"use client";

import { useEffect, useRef, useState } from "react";
import { API_BASE, apiUrl } from "@/lib/api";
import {
  FIX_TARGETS,
  checkPath,
  statusDifferences,
  summarizePassport,
  type CheckSummary,
  type FixCandidate,
  type PassportLike,
  type RecordedCheck,
} from "@/lib/checkfix";
import { githubFile } from "@/lib/flagships";
import { Status } from "./ui";

/** The API's request-wide deadline is 240 s (PF_VERIFY_DEADLINE_S); the page waits a little longer. */
const CLIENT_TIMEOUT_MS = 300_000;

type Phase =
  | { kind: "idle" }
  | { kind: "checking"; started: number }
  | { kind: "live"; result: CheckSummary; seconds: number }
  | { kind: "recorded"; reason: string };

const authorText: Record<FixCandidate["author"], string> = {
  upstream: "upstream code, ported to Lean",
  port: "vulnerable code, ported to Lean",
  muse: "written by Muse",
  reference: "build-team port of the shipped fix",
};

export function CheckFix() {
  const [targetKey, setTargetKey] = useState(FIX_TARGETS[0]!.key);
  const target = FIX_TARGETS.find((t) => t.key === targetKey)!;
  const [candidateKey, setCandidateKey] = useState(target.candidates[0]!.key);
  const candidate = target.candidates.find((c) => c.key === candidateKey) ?? target.candidates[0]!;
  const [recorded, setRecorded] = useState<RecordedCheck | null>(null);
  const [phase, setPhase] = useState<Phase>({ kind: "idle" });
  const [now, setNow] = useState(0);
  const abort = useRef<AbortController | null>(null);

  // The recorded result of the selected file: its requirements are listed before any check runs.
  useEffect(() => {
    let live = true;
    setRecorded(null);
    fetch(checkPath(target.task, candidate.key, "json"))
      .then((r) => (r.ok ? (r.json() as Promise<RecordedCheck>) : null))
      .then((r) => live && setRecorded(r))
      .catch(() => live && setRecorded(null));
    return () => {
      live = false;
    };
  }, [target.task, candidate.key]);

  useEffect(() => {
    if (phase.kind !== "checking") return;
    const t = setInterval(() => setNow(Date.now()), 500);
    return () => clearInterval(t);
  }, [phase.kind]);

  useEffect(() => () => abort.current?.abort(), []);

  const select = (t: string, c?: string) => {
    abort.current?.abort();
    abort.current = null;
    setPhase({ kind: "idle" });
    const next = FIX_TARGETS.find((x) => x.key === t)!;
    setTargetKey(t);
    setCandidateKey(c ?? next.candidates[0]!.key);
  };

  const run = async () => {
    abort.current?.abort();
    const ctl = new AbortController();
    abort.current = ctl;
    const started = Date.now();
    setNow(started);
    setPhase({ kind: "checking", started });
    const timer = setTimeout(() => ctl.abort(new DOMException("timeout", "TimeoutError")), CLIENT_TIMEOUT_MS);
    try {
      const src = await fetch(checkPath(target.task, candidate.key, "lean"), { signal: ctl.signal });
      if (!src.ok) throw new Error(`the candidate file could not be loaded (${src.status})`);
      const source = await src.text();
      let res: Response;
      try {
        res = await fetch(apiUrl("/api/verify"), {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ task: target.task, source, counterexample: true }),
          signal: ctl.signal,
          cache: "no-store",
        });
      } catch (e) {
        if (ctl.signal.aborted) throw e;
        throw new Error(`the API at ${API_BASE} could not be reached`);
      }
      if (!res.ok) {
        let detail = res.statusText;
        try {
          const body = (await res.json()) as { detail?: unknown };
          if (typeof body.detail === "string") detail = body.detail;
        } catch {
          // keep the status text
        }
        throw new Error(
          res.status === 503 ? "the API is busy with other checks (503)" : res.status === 429 ? "the daily check quota for this address is used up (429)" : `the API answered ${res.status} ${detail}`,
        );
      }
      const p = (await res.json()) as PassportLike;
      setPhase({ kind: "live", result: summarizePassport(p), seconds: Math.round((Date.now() - started) / 1000) });
    } catch (e) {
      if (abort.current !== ctl) return; // superseded by another selection or check
      const timedOut = ctl.signal.aborted && (ctl.signal.reason as DOMException | undefined)?.name === "TimeoutError";
      const userStop = ctl.signal.aborted && !timedOut;
      setPhase({
        kind: "recorded",
        reason: timedOut
          ? `the API did not answer within ${CLIENT_TIMEOUT_MS / 60000} minutes`
          : userStop
            ? "you asked for the recorded result"
            : (e as Error).message,
      });
    } finally {
      clearTimeout(timer);
    }
  };

  const showRecorded = () => {
    abort.current?.abort();
  };

  const live = phase.kind === "live" ? phase.result : null;
  const shown: CheckSummary | null = live ?? (phase.kind === "recorded" ? recorded : null);
  const elapsed = phase.kind === "checking" ? Math.max(0, Math.round((now - phase.started) / 1000)) : null;
  const diffs = live && recorded ? statusDifferences(live, recorded) : [];
  const cexMissing = live && live.status === "REFUTED" && live.counterexamples === null;

  return (
    <div className="cf">
      <div className="cf-pick card">
        <div className="cf-targets" role="group" aria-label="Real failure">
          {FIX_TARGETS.map((t) => (
            <button key={t.key} type="button" className="cf-target" aria-pressed={t.key === targetKey} onClick={() => select(t.key)}>
              {t.incident}
            </button>
          ))}
        </div>
        <fieldset className="cf-candidates">
          <legend className="sr-only">Version of the code to check</legend>
          {target.candidates.map((c) => (
            <label key={c.key} className="cf-candidate" data-checked={c.key === candidate.key}>
              <input type="radio" name="cf-candidate" value={c.key} checked={c.key === candidate.key} onChange={() => select(target.key, c.key)} />
              <span className="cf-candidate-text">
                <strong>{c.label}</strong>
                <span className="cf-candidate-who">{authorText[c.author]}</span>
                <span className="cf-candidate-detail">{c.detail}</span>
              </span>
            </label>
          ))}
        </fieldset>
        <div className="cf-actions">
          <button type="button" className="btn btn-primary" onClick={run} disabled={phase.kind === "checking"}>
            {phase.kind === "checking" ? `Checking, ${elapsed} s` : "Check this file now"}
          </button>
          {phase.kind === "checking" ? (
            <button type="button" className="btn" onClick={showRecorded}>
              Show the recorded result instead
            </button>
          ) : null}
          <a className="small" href={checkPath(target.task, candidate.key, "lean")} target="_blank" rel="noreferrer">
            Lean source
          </a>
        </div>
        <p className="small muted cf-how">
          The file goes to <code>POST /api/verify</code> on the ProofForge API with task <code>{target.task}</code>. The judge builds it against the
          locked specification in a fresh sandbox, runs Comparator with six kernels, leanchecker and the axiom audit, tests the rebuilt executable on
          generated cases, and turns each refuted case into a Lean theorem checked by the same kernels. The page waits up to five minutes.
        </p>
      </div>

      <div className="cf-result card" aria-live="polite">
        <ResultHead phase={phase} live={live} recorded={recorded} elapsed={elapsed} />
        {cexMissing ? (
          <p className="small muted">
            This API did not run the counterexample stage.{" "}
            {recorded?.counterexamples?.length ? "The counterexamples below come from the committed Passport of the same file." : null}
          </p>
        ) : null}
        {live && recorded ? (
          <p className="small muted">
            {diffs.length === 0
              ? `Every requirement has the same status as in the committed Passport of this file (${recorded.passportSha256.slice(0, 12)}).`
              : `Differs from the committed Passport of this file (${recorded.passportSha256.slice(0, 12)}) on ${diffs.join(", ")}.`}
          </p>
        ) : null}
        <Requirements rows={(shown ?? recorded)?.requirements ?? []} checking={phase.kind === "checking"} pending={!shown} />
        {shown?.counterexamples?.length ? (
          <Counterexamples items={shown.counterexamples} />
        ) : cexMissing && recorded?.counterexamples?.length ? (
          <Counterexamples items={recorded.counterexamples} />
        ) : null}
        {shown && shown.status !== "VERIFIED" && shown.reasons.length && !shown.requirements.some((r) => r.status === "REFUTED") ? (
          <p className="small muted">Judge: {shown.reasons.slice(0, 2).join("; ")}</p>
        ) : null}
      </div>
    </div>
  );
}

function ResultHead({ phase, live, recorded, elapsed }: { phase: Phase; live: CheckSummary | null; recorded: RecordedCheck | null; elapsed: number | null }) {
  if (phase.kind === "checking")
    return (
      <p className="cf-status">
        <Status value="CHECKING">Checking</Status> <span>Waiting for the judge, {elapsed} s. Each requirement gets VERIFIED, REFUTED or UNRESOLVED.</span>
      </p>
    );
  if (live)
    return (
      <p className="cf-status">
        <Status value={live.status} />{" "}
        <span>
          Live check, {phase.kind === "live" ? `${phase.seconds} s` : ""}. Passport{" "}
          <a className="hash" href={`/passport/${live.passportSha256}`}>
            {live.passportSha256.slice(0, 16)}
          </a>
          {live.propertyCases ? `, ${live.propertyCases.toLocaleString("en-US")} property cases` : ""}
          {live.kernels ? `, ${live.kernels} kernels` : ""}.
        </span>
      </p>
    );
  if (phase.kind === "recorded")
    return recorded ? (
      <p className="cf-status">
        <Status value={recorded.status} />{" "}
        <span>
          Recorded result, because {phase.reason}: the committed Passport{" "}
          <a className="hash" href={githubFile(recorded.passportPath)}>
            {recorded.passportSha256.slice(0, 16)}
          </a>{" "}
          checked this exact file (sha256 <span className="hash">{recorded.sourceSha256.slice(0, 12)}</span>) on {recorded.generated?.slice(0, 10)}.
        </span>
      </p>
    ) : (
      <p className="cf-status">No result: {phase.reason}, and the recorded result could not be loaded.</p>
    );
  return (
    <p className="cf-idle muted">
      Not checked yet. These are the locked requirements of <span className="mono">{recorded?.task ?? "the task"}</span>.
    </p>
  );
}

function Requirements({ rows, checking, pending }: { rows: CheckSummary["requirements"]; checking: boolean; pending: boolean }) {
  if (!rows.length) return null;
  return (
    <ul className="cf-reqs">
      {rows.map((r) => (
        <li key={r.id} className="cf-req">
          <div className="cf-req-line">
            <span className="req-id">{r.id}</span>
            {pending ? checking ? <Status value="CHECKING">checking</Status> : null : <Status value={r.status} />}
          </div>
          {r.text ? <p className="cf-req-text">{withCode(r.text)}</p> : null}
          {!pending && r.witness ? <p className="cf-witness">Failing case: {r.witness}</p> : null}
        </li>
      ))}
    </ul>
  );
}

function Counterexamples({ items }: { items: NonNullable<CheckSummary["counterexamples"]> }) {
  return (
    <div className="cf-cex">
      <p className="small">
        <strong>Counterexamples.</strong> Each is a Lean theorem stating that the requirement is false for this code, built from the failing case.
      </p>
      <ul>
        {items.map((c) => (
          <li key={c.requirement}>
            <span className="req-id">{c.requirement}</span>{" "}
            {c.kernelChecked ? (
              <>
                accepted by {c.kernels} of 6 kernels and leanchecker: <code>{c.statement}</code>
              </>
            ) : (
              <span className="muted">not kernel-checked: {c.reason}</span>
            )}
          </li>
        ))}
      </ul>
    </div>
  );
}

/** Requirement doc strings mark Lean expressions with backticks. */
function withCode(text: string) {
  return text.split(/`([^`]+)`/).map((part, i) => (i % 2 ? <code key={i}>{part}</code> : part));
}
