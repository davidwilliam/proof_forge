"use client";

import Link from "next/link";
import { useCallback, useEffect, useLayoutEffect, useMemo, useReducer, useRef, useState } from "react";
import { getJson, postJson, type Job, type Passport } from "@/lib/api";
import { claimWord, initialState, reduce, type ForgeState, type StreamEvent } from "@/lib/events";
import { formatDuration, formatInt, formatUsd, modelInfo, shortHash } from "@/lib/format";
import { openJobStream, type ConnectionState } from "@/lib/stream";
import { Pipeline } from "@/components/Pipeline";
import { Status, ErrorBox } from "@/components/ui";
import { StreamView } from "./StreamView";

export interface ReqView {
  id: string;
  theorem: string;
  statement: string | null;
  text: string;
  predicate: string | null;
  statementSha: string;
}

interface TaskView {
  id: string;
  issue: string;
  family: string;
  namespace: string;
  definitions: string[];
  manifestSha: string;
}

const SPEEDS = [5, 10, 20, 40, 80];

type Action = { type: "event"; e: StreamEvent } | { type: "reset" };

export function ForgeSession(props: {
  task: TaskView;
  requirements: ReqView[];
  recordings: string[];
  defaultRecording: string;
  initialJob: string | null;
}) {
  const { task, requirements, recordings } = props;
  const reqRefs = useMemo(() => requirements.map((r) => ({ id: r.id, theorem: r.theorem })), [requirements]);
  const [state, dispatch] = useReducer(
    (s: ForgeState, a: Action) => (a.type === "reset" ? initialState(reqRefs) : reduce(s, a.e)),
    reqRefs,
    initialState,
  );
  const [jobId, setJobId] = useState<string | null>(props.initialJob);
  const [job, setJob] = useState<Job | null>(null);
  const [recording, setRecording] = useState(props.defaultRecording);
  const [speed, setSpeed] = useState(20);
  const [starting, setStarting] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [conn, setConn] = useState<ConnectionState | null>(null);
  const [codeSize, setCodeSize] = useState(16);
  const [expandArgs, setExpandArgs] = useState(false);
  const [minor, setMinor] = useState<boolean | null>(null);
  const [follow, setFollow] = useState(true);
  const [passport, setPassport] = useState<Passport | null>(null);
  const [now, setNow] = useState(() => Date.now() / 1000);
  const scroller = useRef<HTMLDivElement>(null);

  // Saved display preferences.
  useEffect(() => {
    try {
      const v = Number(localStorage.getItem("pf-code-size"));
      if (v >= 12 && v <= 32) setCodeSize(v);
    } catch {
      // storage unavailable
    }
  }, []);
  const changeSize = (d: number) => {
    setCodeSize((v) => {
      const n = Math.min(32, Math.max(12, v + d));
      try {
        localStorage.setItem("pf-code-size", String(n));
      } catch {
        // storage unavailable
      }
      return n;
    });
  };

  // Stream the current job's events.
  useEffect(() => {
    if (!jobId) return;
    dispatch({ type: "reset" });
    setPassport(null);
    setError(null);
    getJson<Job>(`/api/jobs/${encodeURIComponent(jobId)}`)
      .then(setJob)
      .catch((e: Error) => setError(`Job ${jobId}: ${e.message}`));
    return openJobStream(jobId, { onEvent: (e) => dispatch({ type: "event", e }), onConnection: setConn });
  }, [jobId]);

  // Load the Passport once the fresh check has produced one (for provenance and cost).
  const passportSha = state.passport?.sha;
  useEffect(() => {
    if (!passportSha) return;
    getJson<Passport>(`/api/passports/${passportSha}`)
      .then(setPassport)
      .catch(() => setPassport(null));
  }, [passportSha]);

  // Clock for the elapsed time while a job runs.
  useEffect(() => {
    if (!jobId || state.terminal) return;
    const t = setInterval(() => setNow(Date.now() / 1000), 1000);
    return () => clearInterval(t);
  }, [jobId, state.terminal]);

  // Follow the end of the stream unless the viewer scrolled up.
  useLayoutEffect(() => {
    const el = scroller.current;
    if (el && follow) el.scrollTop = el.scrollHeight;
  }, [state.items.length, follow]);
  const onScroll = useCallback(() => {
    const el = scroller.current;
    if (!el) return;
    const atEnd = el.scrollHeight - el.scrollTop - el.clientHeight < 120;
    setFollow(atEnd);
  }, []);

  const start = async () => {
    setStarting(true);
    setError(null);
    try {
      // Replay mode only: the server re-emits a recorded session and freshly checks its artifact.
      const j = await postJson<Job>("/api/jobs", { task: task.id, mode: "replay", recording, speed });
      setJob(j);
      setJobId(j.id);
      setFollow(true);
      const u = new URL(window.location.href);
      u.searchParams.set("job", j.id);
      window.history.replaceState(null, "", u.toString());
    } catch (e) {
      setError((e as Error).message);
    } finally {
      setStarting(false);
    }
  };

  const running = !!jobId && !state.terminal;
  const segment = state.segment ?? (jobId ? "Connecting" : "No session running");
  const segKind = !jobId ? "idle" : /fresh check/i.test(segment) ? "check" : /^live$/i.test(segment) ? "live" : "recorded";
  const showMinor = minor ?? !state.hasToolEvents;
  const wallEnd = state.terminal ? state.wallEnd : now;
  const budget = passport?.provenance?.budget;
  const elapsedRecorded =
    budget?.elapsed_s ?? passport?.provenance?.elapsed_s ?? (state.recordedStart != null && state.recordedEnd != null ? state.recordedEnd - state.recordedStart : null);

  return (
    <main className="forge" style={{ ["--code-size" as string]: `${codeSize}px`, ["--text-size" as string]: `${codeSize + 1}px` }}>
      <div className="segment-bar">
        <span className="segment-label" data-segment={segKind} aria-live="polite">
          {segment}
        </span>
        {state.jobState ? (
          <span>
            Job state <Status value={state.jobState} />
          </span>
        ) : null}
        {conn && running ? <span className="muted small">Stream {conn}</span> : null}
        <span className="spacer" />
        <div className="controls">
          <label>
            Recording
            <select value={recording} onChange={(e) => setRecording(e.target.value)} disabled={running || starting}>
              {recordings.map((r) => (
                <option key={r} value={r}>
                  {r}
                </option>
              ))}
            </select>
          </label>
          <label>
            Speed
            <select value={speed} onChange={(e) => setSpeed(Number(e.target.value))} disabled={running || starting}>
              {SPEEDS.map((s) => (
                <option key={s} value={s}>
                  {s}x
                </option>
              ))}
            </select>
          </label>
          <button className="primary" onClick={start} disabled={running || starting || !recording}>
            {starting ? "Starting" : running ? "Replaying" : "Start replay"}
          </button>
        </div>
      </div>

      <div className="task-header">
        <div>
          <h1>
            Task {task.id}: repair <code>{task.definitions.map((d) => `${task.namespace}.${d}`).join(", ")}</code>
          </h1>
          <p>{task.issue}</p>
        </div>
        <Pipeline />
      </div>

      <aside className="col col-left" aria-label="Locked requirements">
        <h2>Locked requirements</h2>
        <p className="small muted">
          Owner-reviewed and hash-locked. Manifest <span className="hash">{shortHash(task.manifestSha, 16)}</span>
        </p>
        {requirements.map((r) => (
          <div className="req" key={r.id}>
            <div className="req-id">{r.id}</div>
            <p style={{ margin: "2px 0 4px" }}>{r.text}</p>
            <pre>
              <code>
                theorem {r.theorem.split(".").pop()} : {r.statement}
              </code>
            </pre>
            {r.predicate ? (
              <details>
                <summary className="small">Definition of {r.statement?.split(" ")[0]}</summary>
                <pre>
                  <code>{r.predicate}</code>
                </pre>
              </details>
            ) : null}
            <div className="small muted">
              Statement sha256 <span className="hash">{shortHash(r.statementSha)}</span>
            </div>
          </div>
        ))}
      </aside>

      <section className="col stream" ref={scroller} onScroll={onScroll} aria-label="Agent stream">
        <div className="stream-tools controls small">
          <strong>Agent stream</strong>
          <span className="spacer" />
          <label>
            Code size
            <button onClick={() => changeSize(-1)} aria-label="Smaller code">
              A-
            </button>
            <span className="mono">{codeSize}px</span>
            <button onClick={() => changeSize(1)} aria-label="Larger code">
              A+
            </button>
          </label>
          <label>
            <input type="checkbox" checked={expandArgs} onChange={(e) => setExpandArgs(e.target.checked)} /> Expand tool arguments
          </label>
          <label>
            <input type="checkbox" checked={showMinor} onChange={(e) => setMinor(e.target.checked)} /> File writes and snippet checks
          </label>
          <label>
            <input type="checkbox" checked={follow} onChange={(e) => setFollow(e.target.checked)} /> Follow
          </label>
        </div>
        <div className="stream-body">
          {error ? <ErrorBox title="Request failed" message={error} /> : null}
          {!jobId ? (
            <div className="notice" style={{ marginTop: 12 }}>
              <p>
                Pick a recording and a replay speed, then start. The server re-emits the recorded session and then runs a fresh check of the
                stored artifact; requirement statuses come only from that check.
              </p>
            </div>
          ) : null}
          <StreamView state={state} jobId={jobId} expandArgs={expandArgs} showMinor={showMinor} />
        </div>
      </section>

      <aside className="col col-right" aria-label="Claim status">
        <h2>Claim status</h2>
        <ul className="claims">
          {state.order.map((id) => {
            const c = state.claims[id]!;
            const word = claimWord(c);
            let note = "";
            if (c.final) note = "from the Passport";
            else if (c.testViolations) note = `${c.testViolations} test violations at version ${c.testVersion}`;
            else if (c.testVersion != null) note = `tests pass at version ${c.testVersion}`;
            return (
              <li key={id}>
                <span className="req-id">{id}</span>
                <Status value={c.final ?? (c.session === "proved" ? "PROVED" : c.session === "working" ? "IN PROGRESS" : "pending")}>{word}</Status>
                {note ? <span className="note">{note}</span> : null}
              </li>
            );
          })}
        </ul>
        <p className="small muted" style={{ marginTop: 8 }}>
          VERIFIED, REFUTED and UNRESOLVED are assigned only by the final Passport. Proved in session means the agent&apos;s own check found
          no sorry.
        </p>

        {state.passport ? (
          <div className="passport-callout">
            <div>
              Component <Status value={state.passport.status} />
            </div>
            <Link href={`/passport/${state.passport.sha}`}>Open Passport {shortHash(state.passport.sha)}</Link>
          </div>
        ) : null}

        <h2 style={{ marginTop: 16 }}>Session</h2>
        <dl className="metric-grid">
          <dt>Job</dt>
          <dd className="mono">{jobId ?? "none"}</dd>
          <dt>Recording</dt>
          <dd className="mono">{state.recording ?? job?.recording ?? "none"}</dd>
          {state.models.map((m) => {
            const info = modelInfo(m);
            return (
              <FragmentPair key={m} k={info.name} v={info.role === "prover" ? "repairer and prover" : info.role} />
            );
          })}
          <dt>Model turns</dt>
          <dd>{formatInt(state.counts.turns)}</dd>
          <dt>Tool calls</dt>
          <dd>{state.hasToolEvents ? formatInt(state.counts.tools) : "not recorded"}</dd>
          <dt>Versions</dt>
          <dd>{formatInt(state.counts.versions)}</dd>
          <dt>Snippets clean</dt>
          <dd>
            {formatInt(state.counts.snippetsOk)} of {formatInt(state.counts.snippets)}
          </dd>
          <dt>Planner lemmas</dt>
          <dd>
            {formatInt(state.counts.plannedLemmas)} in {formatInt(state.counts.plans)} plans
          </dd>
          <dt>Tokens in</dt>
          <dd>
            {formatInt(state.usage.prompt)} ({formatInt(state.usage.cached)} cached)
          </dd>
          <dt>Tokens out</dt>
          <dd>{formatInt(state.usage.completion)}</dd>
          <dt>Session time</dt>
          <dd>{formatDuration(elapsedRecorded)}</dd>
          <dt>Replay time</dt>
          <dd>{state.wallStart != null && wallEnd != null ? formatDuration(wallEnd - state.wallStart) : "none"}</dd>
          {budget?.usd_list != null ? (
            <>
              <dt>Cost, list</dt>
              <dd>{formatUsd(budget.usd_list)}</dd>
            </>
          ) : null}
          {budget?.usd_actual != null ? (
            <>
              <dt>Cost, billed</dt>
              <dd>{formatUsd(budget.usd_actual)}</dd>
            </>
          ) : null}
          {typeof state.start?.budget_usd === "number" ? (
            <>
              <dt>Budget cap</dt>
              <dd>{formatUsd(state.start.budget_usd)}</dd>
            </>
          ) : null}
        </dl>
        <p className="small muted" style={{ marginTop: 8 }}>
          Token counts are summed from the repairer&apos;s turn events. Cost appears when the session&apos;s provenance records it.
        </p>
      </aside>
    </main>
  );
}

function FragmentPair({ k, v }: { k: string; v: string }) {
  return (
    <>
      <dt>{k}</dt>
      <dd>{v}</dd>
    </>
  );
}

