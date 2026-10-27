"use client";

import Link from "next/link";
import { memo, useState } from "react";
import { getJson } from "@/lib/api";
import { toolArgs, type ForgeState, type RawEvent, type StreamItem } from "@/lib/events";
import { dialogLabel, formatMs, maybeJson, modelInfo, prettyJson, shortHash } from "@/lib/format";
import { Code, Status } from "@/components/ui";

const MINOR = new Set(["write", "snippet"]);

export function StreamView({ state, jobId, expandArgs, showMinor }: { state: ForgeState; jobId: string | null; expandArgs: boolean; showMinor: boolean }) {
  const defaultModel = typeof state.start?.model === "string" ? state.start.model : null;
  return (
    <div>
      {state.items.map((it) =>
        !showMinor && MINOR.has(it.kind) ? null : (
          <Item key={it.id} it={it} jobId={jobId} expandArgs={expandArgs} hasTools={state.hasToolEvents} defaultModel={defaultModel} />
        ),
      )}
    </div>
  );
}

const s = (v: unknown) => (typeof v === "string" ? v : v == null ? "" : String(v));
const n = (v: unknown) => (typeof v === "number" ? v : null);

const Item = memo(function Item({
  it,
  jobId,
  expandArgs,
  hasTools,
  defaultModel,
}: {
  it: StreamItem;
  jobId: string | null;
  expandArgs: boolean;
  hasTools: boolean;
  defaultModel: string | null;
}) {
  const e = it.ev;
  switch (it.kind) {
    case "job":
      return <JobLine e={e} />;
    case "start":
      return (
        <div className="ev-milestone">
          Session started: {modelInfo(s(e.model)).name} as repairer and prover
          {e.planner && e.planner !== "none" ? `, ${modelInfo(s(e.planner)).name} as lemma planner` : ", no planner"}
          {e.mode ? `, ${s(e.mode)} mode` : ""}
          {e.effort ? `, ${s(e.effort)} effort` : ""}.
        </div>
      );
    case "tests":
      return <TestsLine e={e} />;
    case "phase":
      return (
        <div className="ev-milestone">
          Phase {s(e.phase)}: {e.ok ? "complete, the rebuilt binary passes the requirement tests" : "not complete"}
          {e.skipped ? ` (${s(e.skipped)})` : ""}.
        </div>
      );
    case "write":
      return <WriteLine e={e} jobId={jobId} />;
    case "turn":
      return <Turn e={e} hasTools={hasTools} defaultModel={defaultModel} />;
    case "tool":
      return <Tool e={e} expandArgs={expandArgs} />;
    case "snippet":
      return (
        <div className="ev-compact">
          Snippet check against version {s(e.version)}: {e.ok ? "compiles cleanly" : "has errors or warnings"} ({formatMs(n(e.ms))})
        </div>
      );
    case "check":
      return <CheckLine e={e} />;
    case "judge":
      return (
        <div className="ev-milestone">
          Judge on version {s(e.version)} (Comparator and leanchecker): <Status value={e.accepted ? "ACCEPTED" : "REJECTED"} /> in {formatMs(n(e.ms))}. This is the
          in-session result; the Passport check below runs fresh.
        </div>
      );
    case "plan":
      return <Plan e={e} />;
    case "obligation":
      return (
        <div className="ev-compact">
          Obligation <code>{s(e.theorem)}</code> ({s(e.label)}): {e.ok ? "own proof complete" : "not finished within its turn budget"}
        </div>
      );
    case "resolve":
      return (
        <div className="ev-compact">
          Resolve <code>{s(e.name)}</code> at depth {s(e.depth)}: <Status value={e.ok ? "PROVED" : "SORRY"}>{e.ok ? "proved" : "still open"}</Status>
        </div>
      );
    case "budget_stop":
      return <div className="error-box">Budget stop: {s(e.reason)} cap reached. The last candidate is checked as is.</div>;
    case "passport":
      return <PassportLine e={e} />;
    case "api_error":
      return (
        <div className="ev-compact line-error">
          Model API error {s(e.status)}: {s(e.body).slice(0, 200)}
        </div>
      );
    case "attempt":
      return (
        <div className="ev-compact">
          Attempt {s(e.turn)} on version {s(e.version)}: {e.accepted ? "accepted" : "not accepted"}
        </div>
      );
    default:
      return (
        <details className="ev-compact">
          <summary>Event {it.kind}</summary>
          <Code text={prettyJson(e)} />
        </details>
      );
  }
});

function JobLine({ e }: { e: RawEvent }) {
  const st = s(e.state);
  return (
    <div className="ev-job">
      Job <Status value={st} />
      {e.label ? `: ${s(e.label)}` : ""}
      {e.recording ? `, recording ${s(e.recording)}` : ""}
      {e.reason ? `, ${s(e.reason)}` : ""}
    </div>
  );
}

function TestsLine({ e }: { e: RawEvent }) {
  const v = (e.violations && typeof e.violations === "object" ? e.violations : {}) as Record<string, number>;
  const entries = Object.entries(v).filter(([, c]) => c > 0);
  return (
    <div className="ev-milestone">
      Requirement property tests on the binary built from version {s(e.version)}: <Status value={s(e.status)} />
      {entries.length ? (
        <span>
          {" "}
          with violations of{" "}
          {entries.map(([k, c], i) => (
            <span key={k}>
              {i ? ", " : ""}
              <span className="mono">{k}</span> ({c} cases)
            </span>
          ))}
        </span>
      ) : null}
    </div>
  );
}

function WriteLine({ e, jobId }: { e: RawEvent; jobId: string | null }) {
  const [src, setSrc] = useState<string | null>(null);
  const [err, setErr] = useState<string | null>(null);
  const v = n(e.version);
  const label = `Version ${s(e.version)} written, ${s(e.bytes)} bytes${e.why ? ` (${s(e.why)})` : ""}`;
  if (!jobId || v == null) return <div className="ev-compact">{label}</div>;
  return (
    <details
      className="ev-compact"
      onToggle={(ev) => {
        if ((ev.target as HTMLDetailsElement).open && src == null)
          getJson<{ source: string }>(`/api/jobs/${jobId}/candidate/${v}`)
            .then((r) => setSrc(r.source))
            .catch((x: Error) => setErr(x.message));
      }}
    >
      <summary>{label}</summary>
      {err ? <span className="line-error">{err}</span> : src == null ? "Loading" : <Code text={src} />}
    </details>
  );
}

function Turn({ e, hasTools, defaultModel }: { e: RawEvent; hasTools: boolean; defaultModel: string | null }) {
  const label = s(e.label);
  const info = modelInfo(s(e.model) || defaultModel, label);
  const tools = Array.isArray(e.tools) ? (e.tools as string[]) : [];
  const text = s(e.text).trim();
  return (
    <div className="ev ev-turn">
      <h3>
        <span className="who">
          {info.name}, {info.role}
        </span>{" "}
        <span className="what">
          {dialogLabel(label)}, turn {n(e.turn) != null ? n(e.turn)! + 1 : ""}
        </span>
      </h3>
      {text ? <p className="ev-text">{text}</p> : null}
      {!hasTools && tools.length ? (
        <p className="small muted" style={{ margin: 0 }}>
          Tool calls: <span className="mono">{tools.join(", ")}</span>
        </p>
      ) : null}
      {hasTools && !tools.length ? <p className="small muted">No tool call in this turn.</p> : null}
    </div>
  );
}

const CODE_KEYS = new Set(["content", "code", "text"]);

function Tool({ e, expandArgs }: { e: RawEvent; expandArgs: boolean }) {
  const name = s(e.name);
  const args = toolArgs(e);
  const result = s(e.result);
  const hasArgs = args != null && (typeof args === "string" ? args.length > 0 : Object.keys(args).length > 0);
  const failed = /error|REVERTED|NOT ACCEPTED|REFUTED/.test(result.slice(0, 400)) && !/^snippet compiles/.test(result);
  return (
    <div className="ev-tool">
      <div className="ev-tool-head">
        {name}
        {args && typeof args === "object" && typeof args.name === "string" ? ` ${args.name}` : ""}
        {args && typeof args === "object" && typeof args.path === "string" ? ` ${args.path}` : ""}
        <span className="muted">
          {" "}
          {formatMs(n(e.ms))}
          {e.version != null ? `, file at version ${s(e.version)}` : ""}
        </span>
      </div>
      {hasArgs ? (
        <details key={`a${expandArgs}`} open={expandArgs}>
          <summary className="small">Arguments</summary>
          {typeof args === "string" ? (
            <Code text={args} />
          ) : (
            Object.entries(args!).map(([k, v]) =>
              CODE_KEYS.has(k) || (typeof v === "string" && v.includes("\n")) ? (
                <div key={k}>
                  <span className="small muted mono">{k}</span>
                  <Code text={s(v)} />
                </div>
              ) : (
                <div key={k} className="small mono">
                  {k}: {typeof v === "string" ? v : prettyJson(v)}
                </div>
              ),
            )
          )}
        </details>
      ) : null}
      <details open>
        <summary className="small">{failed ? "Result with errors" : "Result"}</summary>
        <Code text={maybeJson(result)} wrap />
      </details>
    </div>
  );
}

function CheckLine({ e }: { e: RawEvent }) {
  const status = (e.status && typeof e.status === "object" ? e.status : {}) as Record<string, string>;
  const scan = Array.isArray(e.scan) ? (e.scan as string[]) : [];
  return (
    <div className="ev-milestone">
      <div>
        Full check of version {s(e.version)}: {e.errors ? <Status value="ERROR">does not compile</Status> : "compiles"} ({formatMs(n(e.ms))})
      </div>
      {Object.keys(status).length ? (
        <table className="small" style={{ marginTop: 6 }}>
          <tbody>
            {Object.entries(status).map(([k, v]) => (
              <tr key={k}>
                <td className="mono">{k}</td>
                <td>
                  <Status value={v} />
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      ) : null}
      {scan.length ? <Code text={scan.join("\n")} wrap /> : null}
    </div>
  );
}

function Plan({ e }: { e: RawEvent }) {
  const info = modelInfo(s(e.model));
  const lemmas = Array.isArray(e.lemmas) ? (e.lemmas as string[]) : [];
  const prose = s(e.prose).trim();
  const code = s(e.code).trim();
  return (
    <div className="ev ev-turn ev-plan">
      <h3>
        <span className="who">
          {info.name}, {info.role}
        </span>{" "}
        <span className="what">
          plan for <code>{s(e.theorem)}</code>, attempt {n(e.attempt) != null ? n(e.attempt)! + 1 : ""}
        </span>
      </h3>
      {prose ? <p className="ev-text">{prose}</p> : null}
      <p style={{ margin: "4px 0" }}>{lemmas.length} helper lemmas, installed as open targets for the prover:</p>
      <ol className="mono small" style={{ margin: "0 0 6px 1.4em", padding: 0 }}>
        {lemmas.map((l) => (
          <li key={l}>{l}</li>
        ))}
      </ol>
      {code ? <Code text={code} /> : null}
    </div>
  );
}

function PassportLine({ e }: { e: RawEvent }) {
  const reqs = (e.requirements && typeof e.requirements === "object" ? e.requirements : {}) as Record<string, string>;
  const sha = s(e.passport_sha256);
  return (
    <div className="ev-milestone" style={{ borderColor: "var(--fg)" }}>
      <div style={{ fontWeight: 650 }}>
        Passport from the fresh check: component <Status value={s(e.status)} />
      </div>
      <table className="small" style={{ margin: "6px 0" }}>
        <tbody>
          {Object.entries(reqs).map(([k, v]) => (
            <tr key={k}>
              <td className="mono">{k}</td>
              <td>
                <Status value={v} />
              </td>
            </tr>
          ))}
        </tbody>
      </table>
      {sha ? <Link href={`/passport/${sha}`}>Open Passport {shortHash(sha)}</Link> : null}
    </div>
  );
}
