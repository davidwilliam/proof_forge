"use client";

import Link from "next/link";
import { useCallback, useEffect, useLayoutEffect, useMemo, useReducer, useRef, useState } from "react";
import { getJson, postJson, type Job, type Passport } from "@/lib/api";
import { claimWord, initialState, reduce, type ForgeState, type StreamEvent } from "@/lib/events";
import { buildTimeline, claimMark, stageStates, type SegmentKind } from "@/lib/forge-view";
import { formatDuration, formatInt, formatUsd, modelInfo, shortHash } from "@/lib/format";
import { RECORDING_FACTS, orderRecordings } from "@/lib/recordings";
import { openJobStream, type ConnectionState } from "@/lib/stream";
import { Pipeline } from "@/components/Pipeline";
import { Status, ErrorBox } from "@/components/ui";
import { ActivityTimeline, CountUp, PassportCard, RecordingCard, ReqMarks } from "./forge/ForgeParts";
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
    if (el && follow && jobId) el.scrollTop = el.scrollHeight;
  }, [state.items.length, follow, jobId]);
  const onScroll = useCallback(() => {
    const el = scroller.current;
    if (!el) return;
    const atEnd = el.scrollHeight - el.scrollTop - el.clientHeight < 120;
    setFollow(atEnd);
  }, []);

  /** Start a replay of the chosen recording, or of `pick` when a recording card starts it in one click. */
  const start = async (pick?: string) => {
    const rec = pick ?? recording;
    if (pick) setRecording(pick);
    setStarting(true);
    setError(null);
    try {
      // Replay mode only: the server re-emits a recorded session and freshly checks its artifact.
      const j = await postJson<Job>("/api/jobs", { task: task.id, mode: "replay", recording: rec, speed });
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
  const segKind: SegmentKind = !jobId ? "idle" : /fresh check/i.test(segment) ? "check" : /^live$/i.test(segment) ? "live" : "recorded";
  const showMinor = minor ?? !state.hasToolEvents;
  const wallEnd = state.terminal ? state.wallEnd : now;
  const budget = passport?.provenance?.budget;
  const elapsedRecorded =
    budget?.elapsed_s ?? passport?.provenance?.elapsed_s ?? (state.recordedStart != null && state.recordedEnd != null ? state.recordedEnd - state.recordedStart : null);

  const activeRecording = state.recording ?? job?.recording ?? (jobId ? null : recording);
  const facts = activeRecording ? RECORDING_FACTS[activeRecording] ?? null : null;
  const stages = stageStates(state, !!jobId, segKind);
  const marks = state.order.map((id) => ({ id, mark: claimMark(state.claims[id]!), word: claimWord(state.claims[id]!) }));
  const provedCount = state.order.filter((id) => state.claims[id]!.session === "proved").length;
  const timeline = useMemo(() => buildTimeline(state, facts?.elapsedS ?? null), [state, facts?.elapsedS]);
  const replayedShare = timeline && facts ? Math.min(1, timeline.now / facts.elapsedS) : null;
  const ordered = orderRecordings(recordings, props.defaultRecording);

  return (
    <main
      id="main"
      className="forge fs"
      data-running={running ? "" : undefined}
      style={{ ["--code-size" as string]: `${codeSize}px`, ["--text-size" as string]: `${codeSize + 1}px` }}
    >
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
          <button className="primary" onClick={() => start()} disabled={running || starting || !recording}>
            {starting ? "Starting" : running ? "Replaying" : "Start replay"}
          </button>
        </div>
      </div>

      <div className="task-header fs-head">
        <h1>
          Task {task.id}: repair <code>{task.definitions.map((d) => `${task.namespace}.${d}`).join(", ")}</code>
        </h1>
        <p>{task.issue}</p>
      </div>

      <Pipeline
        className={`fs-rail${state.passport ? ` fs-v-${state.passport.status.toLowerCase()}` : ""}`}
        stages={[
          {
            state: stages[0],
            detail: (
              <>
                <ReqMarks marks={marks.map((m) => ({ ...m, mark: "locked", word: "locked" }))} label={`${requirements.length} requirements locked`} />
                <span className="fs-rail-fact">
                  {requirements.length} requirements, manifest <span className="hash">{shortHash(task.manifestSha, 12)}</span>
                </span>
              </>
            ),
          },
          {
            state: stages[1],
            detail: (
              <>
                <ReqMarks
                  marks={marks.map((m) => ({ ...m, mark: state.claims[m.id]!.session }))}
                  label={`${provedCount} of ${requirements.length} requirements proved in session`}
                />
                <span className="fs-rail-fact">
                  {!jobId && facts ? (
                    <>
                      {modelInfo(facts.model).name}: {formatInt(facts.turns)} turns, {formatInt(facts.versions)} versions recorded
                    </>
                  ) : jobId ? (
                    <>
                      {provedCount} of {requirements.length} proved in session, {formatInt(state.counts.versions)} versions
                    </>
                  ) : (
                    "Pick a recording to replay"
                  )}
                </span>
                {replayedShare != null && jobId ? (
                  <span className="fs-progress" role="progressbar" aria-label="Recorded session replayed" aria-valuemin={0} aria-valuemax={100} aria-valuenow={Math.round(replayedShare * 100)}>
                    <span style={{ width: `${(replayedShare * 100).toFixed(1)}%` }} />
                  </span>
                ) : null}
              </>
            ),
          },
          {
            state: stages[2],
            detail: (
              <span className="fs-rail-fact">
                {stages[2] === "active"
                  ? "Running on the stored artifact"
                  : stages[2] === "done" && passport
                    ? passport.checks.comparator_kernels.length
                      ? `${passport.checks.comparator_kernels.length} kernels accepted, ${formatInt(passport.checks.property_tests.cases)} property cases`
                      : `${formatInt(passport.checks.property_tests.cases)} property cases, ${formatInt(Object.values(passport.checks.property_tests.violations ?? {}).reduce((a, b) => a + b, 0))} violations; proof check not accepted`
                    : stages[2] === "done"
                      ? "Check complete"
                      : "Runs when the recorded session ends"}
              </span>
            ),
          },
          {
            state: stages[3],
            detail: state.passport ? (
              <>
                <ReqMarks marks={marks.map((m) => ({ ...m, mark: state.claims[m.id]!.final ?? "pending" }))} label={`Passport verdicts: ${state.passport.status}`} />
                <span className="fs-rail-fact">
                  <Status value={state.passport.status} /> <Link href={`/passport/${state.passport.sha}`}>Passport {shortHash(state.passport.sha, 8)}</Link>
                </span>
              </>
            ) : (
              <>
                <ReqMarks marks={marks.map((m) => ({ ...m, mark: "pending" }))} label="No Passport yet" />
                <span className="fs-rail-fact">Assigned by the fresh check</span>
              </>
            ),
          },
        ]}
      />

      <aside className="col col-left" aria-label="Locked requirements">
        <h2>Locked requirements</h2>
        <p className="small muted">
          Owner-reviewed and hash-locked. Manifest <span className="hash">{shortHash(task.manifestSha, 16)}</span>
        </p>
        <p className="small muted fs-honesty">
          VERIFIED, REFUTED and UNRESOLVED are assigned only by the final Passport. Proved in session means the agent&apos;s own check found
          no sorry.
        </p>
        <ol className="fs-reqs" aria-label="Claim status">
          {requirements.map((r) => {
            const c = state.claims[r.id]!;
            const word = claimWord(c);
            let note = "";
            if (c.final) note = "from the Passport";
            else if (c.testViolations) note = `${c.testViolations} test violations at version ${c.testVersion}`;
            else if (c.testVersion != null) note = `tests pass at version ${c.testVersion}`;
            const mark = claimMark(c);
            return (
              <li className="fs-req" key={r.id} data-mark={mark}>
                <div className="fs-req-head">
                  <span className="fs-sq" data-mark={mark} key={mark} aria-hidden="true" />
                  <span className="req-id">{r.id}</span>
                </div>
                <p className="fs-req-text">{r.text}</p>
                <p className="fs-req-status">
                  {c.final ? (
                    <Status value={c.final}>{word}</Status>
                  ) : (
                    <span className="status fs-chip" data-mark={c.session}>
                      {word}
                    </span>
                  )}
                  {note ? <span className="fs-req-note">{note}</span> : null}
                </p>
                <details className="fs-req-more">
                  <summary>Theorem, definition and statement hash</summary>
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
                </details>
              </li>
            );
          })}
        </ol>
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
            <div className="fs-start">
              <h2>Watch a Muse model repair the payout code under ProofForge</h2>
              <p className="fs-start-lead">
                Pick a recording and a replay speed, then start. The server re-emits the recorded session and then runs a fresh check of the
                stored artifact; requirement statuses come only from that check.
              </p>
              <ul className="fs-recs" aria-label="Recorded sessions">
                {ordered.map((r) => (
                  <RecordingCard
                    key={r}
                    id={r}
                    facts={RECORDING_FACTS[r] ?? null}
                    requirements={requirements}
                    selected={r === recording}
                    speed={speed}
                    disabled={starting}
                    onReplay={() => start(r)}
                  />
                ))}
              </ul>
            </div>
          ) : null}
          <StreamView state={state} jobId={jobId} expandArgs={expandArgs} showMinor={showMinor} />
        </div>
      </section>

      <aside className="col col-right" aria-label="Session">
        {state.passport ? <PassportCard summary={state.passport} passport={passport} /> : null}

        <h2>Session</h2>
        <ul className="fs-kpis" aria-label="Session counters">
          <li>
            <span className="fs-kpi-v">
              <CountUp value={state.counts.turns} />
            </span>
            <span className="fs-kpi-l">model turns</span>
          </li>
          <li>
            <span className="fs-kpi-v">{state.hasToolEvents ? <CountUp value={state.counts.tools} /> : <span className="fs-kpi-none">not recorded</span>}</span>
            <span className="fs-kpi-l">tool calls</span>
          </li>
          <li>
            <span className="fs-kpi-v">
              <CountUp value={state.counts.versions} />
            </span>
            <span className="fs-kpi-l">versions</span>
          </li>
          <li>
            <span className="fs-kpi-v">
              <CountUp value={provedCount} />
              <span className="fs-kpi-of"> of {requirements.length}</span>
            </span>
            <span className="fs-kpi-l">proved in session</span>
          </li>
        </ul>

        <ActivityTimeline timeline={timeline} hasTools={state.hasToolEvents} recorded={facts != null} />

        <dl className="metric-grid fs-metrics">
          <dt>Job</dt>
          <dd className="mono">{jobId ?? "none"}</dd>
          <dt>Recording</dt>
          <dd className="mono">{state.recording ?? job?.recording ?? "none"}</dd>
          {state.models.map((m) => {
            const info = modelInfo(m);
            return <FragmentPair key={m} k={info.name} v={info.role === "prover" ? "repairer and prover" : info.role} />;
          })}
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
            <CountUp value={state.usage.prompt} /> (<CountUp value={state.usage.cached} /> cached)
          </dd>
          <dt>Tokens out</dt>
          <dd>
            <CountUp value={state.usage.completion} />
          </dd>
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
