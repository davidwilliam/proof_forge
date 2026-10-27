// Maps the job event stream (GET /api/jobs/{id}/events) to forge session UI state.
// Pure and framework free so it can be tested against recorded events.jsonl files.
//
// Claim statuses: during the session a requirement is pending, being worked on, or
// proved in session (from obligation, resolve and check events). VERIFIED, REFUTED and
// UNRESOLVED are taken only from the final passport event.

export interface RawEvent {
  kind: string;
  t?: number;
  recorded_t?: number;
  [k: string]: unknown;
}

export interface StreamEvent {
  id: number;
  data: RawEvent;
}

export const KNOWN_KINDS = [
  "job",
  "start",
  "tests",
  "phase",
  "write",
  "turn",
  "tool",
  "snippet",
  "check",
  "judge",
  "plan",
  "obligation",
  "resolve",
  "budget_stop",
  "passport",
  "api_error",
  "attempt",
] as const;

export type KnownKind = (typeof KNOWN_KINDS)[number];

export const TERMINAL_STATES = new Set(["COMPLETE", "PARTIAL", "FAILED", "TIMEOUT", "BUDGET_STOP"]);

export type SessionClaim = "pending" | "working" | "proved";
export type FinalStatus = "VERIFIED" | "REFUTED" | "UNRESOLVED";
const FINAL: ReadonlySet<string> = new Set(["VERIFIED", "REFUTED", "UNRESOLVED"]);

export interface Claim {
  id: string;
  theorem: string;
  session: SessionClaim;
  final: FinalStatus | null;
  /** Property-test violations attributed to this requirement in the latest in-session test run. */
  testViolations: number | null;
  testVersion: number | null;
}

export interface StreamItem {
  id: number;
  kind: string;
  ev: RawEvent;
}

export interface Usage {
  prompt: number;
  cached: number;
  completion: number;
}

export interface ForgeState {
  items: StreamItem[];
  lastId: number;
  jobState: string | null;
  segment: string | null;
  recording: string | null;
  failure: string | null;
  terminal: boolean;
  start: RawEvent | null;
  claims: Record<string, Claim>;
  order: string[];
  theoremToReq: Record<string, string>;
  activeLabel: string | null;
  counts: {
    turns: number;
    tools: number;
    versions: number;
    snippets: number;
    snippetsOk: number;
    plans: number;
    plannedLemmas: number;
    lemmasResolved: number;
  };
  usage: Usage;
  models: string[];
  recordedStart: number | null;
  recordedEnd: number | null;
  wallStart: number | null;
  wallEnd: number | null;
  judgeAccepted: boolean | null;
  passport: { sha: string; status: string; requirements: Record<string, string> } | null;
  hasToolEvents: boolean;
  budgetStop: string | null;
  unknownKinds: string[];
}

export interface RequirementRef {
  id: string;
  theorem: string;
}

function shortName(theorem: string): string {
  const i = theorem.lastIndexOf(".");
  return i >= 0 ? theorem.slice(i + 1) : theorem;
}

export function initialState(requirements: RequirementRef[]): ForgeState {
  const claims: Record<string, Claim> = {};
  const theoremToReq: Record<string, string> = {};
  for (const r of requirements) {
    claims[r.id] = { id: r.id, theorem: r.theorem, session: "pending", final: null, testViolations: null, testVersion: null };
    theoremToReq[shortName(r.theorem)] = r.id;
  }
  return {
    items: [],
    lastId: -1,
    jobState: null,
    segment: null,
    recording: null,
    failure: null,
    terminal: false,
    start: null,
    claims,
    order: requirements.map((r) => r.id),
    theoremToReq,
    activeLabel: null,
    counts: { turns: 0, tools: 0, versions: 0, snippets: 0, snippetsOk: 0, plans: 0, plannedLemmas: 0, lemmasResolved: 0 },
    usage: { prompt: 0, cached: 0, completion: 0 },
    models: [],
    recordedStart: null,
    recordedEnd: null,
    wallStart: null,
    wallEnd: null,
    judgeAccepted: null,
    passport: null,
    hasToolEvents: false,
    budgetStop: null,
    unknownKinds: [],
  };
}

const num = (v: unknown): number | null => (typeof v === "number" && Number.isFinite(v) ? v : null);
const str = (v: unknown): string | null => (typeof v === "string" ? v : null);
const rec = (v: unknown): Record<string, unknown> | null =>
  v && typeof v === "object" && !Array.isArray(v) ? (v as Record<string, unknown>) : null;

function setClaim(claims: Record<string, Claim>, id: string | undefined, patch: Partial<Claim>): Record<string, Claim> {
  if (!id || !claims[id]) return claims;
  return { ...claims, [id]: { ...claims[id]!, ...patch } };
}

function reqFor(state: ForgeState, theorem: unknown): string | undefined {
  const t = str(theorem);
  return t ? state.theoremToReq[shortName(t)] : undefined;
}

/** Revert claims that were being worked on (but not proved) to pending, except `keep`. */
function settleWorking(claims: Record<string, Claim>, keep?: string): Record<string, Claim> {
  let out = claims;
  for (const [id, c] of Object.entries(claims)) {
    if (c.session === "working" && id !== keep) out = setClaim(out, id, { session: "pending" });
  }
  return out;
}

export function reduce(state: ForgeState, event: StreamEvent): ForgeState {
  if (event.id <= state.lastId) return state; // duplicate after a reconnect
  const e = event.data;
  if (!e || typeof e.kind !== "string") return { ...state, lastId: event.id };
  const s: ForgeState = { ...state, lastId: event.id, items: [...state.items, { id: event.id, kind: e.kind, ev: e }] };

  const t = num(e.t);
  if (t != null) {
    s.wallStart = s.wallStart ?? t;
    s.wallEnd = t;
  }
  if (e.kind !== "job" && e.kind !== "passport") {
    const rt = num(e.recorded_t) ?? t;
    if (rt != null) {
      s.recordedStart = s.recordedStart ?? rt;
      s.recordedEnd = rt;
    }
  }

  switch (e.kind) {
    case "job": {
      const st = str(e.state);
      if (st) s.jobState = st;
      const label = str(e.label);
      if (label) s.segment = label;
      const recording = str(e.recording);
      if (recording) s.recording = recording;
      if (st === "FAILED") s.failure = str(e.reason) ?? "job failed";
      if (st && TERMINAL_STATES.has(st)) {
        s.terminal = true;
        s.activeLabel = null;
        s.claims = settleWorking(s.claims);
      }
      break;
    }
    case "start": {
      s.start = e;
      const m = str(e.model);
      if (m && !s.models.includes(m)) s.models = [...s.models, m];
      const p = str(e.planner);
      if (p && p !== "none" && !s.models.includes(p)) s.models = [...s.models, p];
      break;
    }
    case "tests": {
      const v = rec(e.violations) ?? {};
      const version = num(e.version);
      let claims = s.claims;
      for (const id of s.order) claims = setClaim(claims, id, { testViolations: num(v[id]) ?? 0, testVersion: version });
      s.claims = claims;
      break;
    }
    case "write": {
      const v = num(e.version);
      if (v != null) s.counts = { ...s.counts, versions: Math.max(s.counts.versions, v) };
      break;
    }
    case "turn": {
      s.counts = { ...s.counts, turns: s.counts.turns + 1 };
      const u = rec(e.usage);
      if (u) {
        const cached = num(rec(u.prompt_tokens_details)?.cached_tokens) ?? 0;
        s.usage = {
          prompt: s.usage.prompt + (num(u.prompt_tokens) ?? 0),
          cached: s.usage.cached + cached,
          completion: s.usage.completion + (num(u.completion_tokens) ?? 0),
        };
      }
      const m = str(e.model) ?? str(s.start?.model);
      if (m && !s.models.includes(m)) s.models = [...s.models, m];
      const label = str(e.label);
      s.activeLabel = label;
      const target = label && label.includes(":") ? label.slice(label.indexOf(":") + 1) : null;
      const rid = target ? s.theoremToReq[target] : undefined;
      if (rid) {
        // A dialog on a requirement theorem: it is now being worked on.
        let claims = settleWorking(s.claims, rid);
        if (claims[rid]?.session !== "proved") claims = setClaim(claims, rid, { session: "working" });
        s.claims = claims;
      }
      break;
    }
    case "tool":
      s.hasToolEvents = true;
      s.counts = { ...s.counts, tools: s.counts.tools + 1 };
      break;
    case "snippet":
      s.counts = { ...s.counts, snippets: s.counts.snippets + 1, snippetsOk: s.counts.snippetsOk + (e.ok === true ? 1 : 0) };
      break;
    case "check": {
      const status = rec(e.status) ?? {};
      let claims = s.claims;
      for (const [th, v] of Object.entries(status)) {
        const rid = s.theoremToReq[shortName(th)];
        if (!rid) continue;
        claims = setClaim(claims, rid, { session: v === "PROVED" ? "proved" : claims[rid]?.session === "working" ? "working" : "pending" });
      }
      s.claims = claims;
      break;
    }
    case "judge":
      s.judgeAccepted = e.accepted === true;
      break;
    case "plan": {
      const lemmas = Array.isArray(e.lemmas) ? e.lemmas.length : 0;
      s.counts = { ...s.counts, plans: s.counts.plans + 1, plannedLemmas: s.counts.plannedLemmas + lemmas };
      const m = str(e.model);
      if (m && !s.models.includes(m)) s.models = [...s.models, m];
      const rid = reqFor(s, e.theorem);
      if (rid && s.claims[rid]?.session !== "proved") s.claims = setClaim(s.claims, rid, { session: "working" });
      break;
    }
    case "obligation": {
      const rid = reqFor(s, e.theorem);
      if (rid && e.ok === true) s.claims = setClaim(s.claims, rid, { session: "proved" });
      break;
    }
    case "resolve": {
      const rid = reqFor(s, e.name);
      if (rid) {
        s.claims = setClaim(s.claims, rid, { session: e.ok === true ? "proved" : "pending" });
      } else if (e.ok === true) {
        s.counts = { ...s.counts, lemmasResolved: s.counts.lemmasResolved + 1 };
      }
      break;
    }
    case "budget_stop":
      s.budgetStop = str(e.reason) ?? "budget exhausted";
      break;
    case "passport": {
      const reqs = rec(e.requirements) ?? {};
      const sha = str(e.passport_sha256) ?? "";
      s.passport = {
        sha,
        status: str(e.status) ?? "UNRESOLVED",
        requirements: Object.fromEntries(Object.entries(reqs).map(([k, v]) => [k, String(v)])),
      };
      let claims = s.claims;
      for (const [id, v] of Object.entries(reqs)) {
        if (typeof v === "string" && FINAL.has(v)) claims = setClaim(claims, id, { final: v as FinalStatus });
      }
      s.claims = claims;
      const label = str(e.label);
      if (label) s.segment = label;
      break;
    }
    case "phase":
    case "api_error":
    case "attempt":
      break;
    default:
      if (!s.unknownKinds.includes(e.kind)) s.unknownKinds = [...s.unknownKinds, e.kind];
  }
  return s;
}

export function reduceAll(state: ForgeState, events: StreamEvent[]): ForgeState {
  return events.reduce(reduce, state);
}

/** Parse one SSE message (data line and lastEventId) into a stream event, or null. */
export function parseSseMessage(data: string, lastEventId: string | null | undefined): StreamEvent | null {
  const id = Number.parseInt(lastEventId ?? "", 10);
  if (!Number.isFinite(id) || id < 0) return null;
  try {
    const parsed = JSON.parse(data) as unknown;
    if (!parsed || typeof parsed !== "object" || typeof (parsed as RawEvent).kind !== "string") return null;
    return { id, data: parsed as RawEvent };
  } catch {
    return null;
  }
}

/** Parse an events.jsonl file into stream events numbered from 0, as the server does. */
export function parseJsonl(text: string): StreamEvent[] {
  return text
    .split("\n")
    .filter((l) => l.trim())
    .map((l, i) => ({ id: i, data: JSON.parse(l) as RawEvent }));
}

/** The status word to show for a claim: the passport status if present, else the session state. */
export function claimWord(c: Claim): string {
  if (c.final) return c.final;
  if (c.session === "proved") return "proved in session";
  if (c.session === "working") return "in progress";
  return "pending";
}

/** Tool arguments may arrive as an object or, in some recordings, as a Python-style repr string. */
export function toolArgs(ev: RawEvent): Record<string, unknown> | string | null {
  const a = ev.args;
  if (a == null) return null;
  if (typeof a === "object" && !Array.isArray(a)) return a as Record<string, unknown>;
  return String(a);
}
