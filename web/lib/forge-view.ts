// Derived views of the forge session state for the progress visuals: the stage of each of the four
// steps, and the recorded timeline binned for the activity chart. Pure and framework free.

import type { Claim, ForgeState } from "./events";

export type StageState = "idle" | "active" | "done";
export type SegmentKind = "idle" | "recorded" | "check" | "live";

/** Lock, Repair, Check and Passport: which step the session is in. */
export function stageStates(state: ForgeState, hasJob: boolean, seg: SegmentKind): [StageState, StageState, StageState, StageState] {
  if (!hasJob) return ["done", "idle", "idle", "idle"];
  const passport = !!state.passport;
  const inCheck = seg === "check" || passport;
  const repair: StageState = inCheck || state.terminal ? "done" : "active";
  const check: StageState = passport ? "done" : inCheck ? (state.terminal ? "done" : "active") : "idle";
  return ["done", repair, check, passport ? "done" : "idle"];
}

/** The status a requirement mark shows: the Passport verdict once there is one, else the session state. */
export function claimMark(c: Claim): string {
  return c.final ?? c.session;
}

export interface TimelineBin {
  /** Seconds from the start of the recording. */
  from: number;
  to: number;
  turns: number;
  tools: number;
  versions: number;
  /** Requirement ids first proved in session within this bin. */
  proved: string[];
}

export interface Timeline {
  /** Recorded seconds the axis spans. */
  span: number;
  /** Recorded seconds replayed so far. */
  now: number;
  bins: TimelineBin[];
  /** The largest stacked bin total, for the y scale. */
  max: number;
}

/**
 * Bin the recorded events by recorded time. The axis spans `spanHint` seconds (the recording's
 * length when known) or the replayed part when longer, so the bars fill in as the replay runs.
 */
export function buildTimeline(state: ForgeState, spanHint: number | null, count = 40): Timeline | null {
  // Replayed events carry their recorded time; events the server adds afterwards (job, passport,
  // summary) carry only wall time and stay off the recorded axis. A live session has wall time only.
  const timed = state.items.filter((it) => it.ev.kind !== "job" && it.ev.kind !== "passport" && it.ev.kind !== "summary");
  const replayed = timed.some((it) => typeof it.ev.recorded_t === "number");
  const timeOf = (it: (typeof timed)[number]): number | null => {
    const v = replayed ? it.ev.recorded_t : it.ev.t;
    return typeof v === "number" && Number.isFinite(v) ? v : null;
  };
  const points = timed.map((it) => ({ it, rt: timeOf(it) })).filter((p): p is { it: (typeof timed)[number]; rt: number } => p.rt != null);
  if (!points.length) return null;
  const start = points[0]!.rt;
  const now = Math.max(0, points[points.length - 1]!.rt - start);
  const span = Math.max(now, spanHint ?? 0, 1);
  const width = span / count;
  const bins: TimelineBin[] = Array.from({ length: count }, (_, i) => ({ from: i * width, to: (i + 1) * width, turns: 0, tools: 0, versions: 0, proved: [] }));
  const provedSeen = new Set<string>();
  const short = (t: unknown) => (typeof t === "string" ? t.slice(t.lastIndexOf(".") + 1) : "");
  for (const { it, rt } of points) {
    const e = it.ev;
    const b = bins[Math.min(count - 1, Math.max(0, Math.floor((rt - start) / width)))]!;
    if (e.kind === "turn") b.turns += 1;
    else if (e.kind === "tool") b.tools += 1;
    else if (e.kind === "write") b.versions += 1;
    // First proof in session of a requirement theorem, as the reducer counts it.
    const proved: string[] = [];
    if ((e.kind === "obligation" || e.kind === "resolve") && e.ok === true) {
      const rid = state.theoremToReq[short(e.kind === "obligation" ? e.theorem : e.name)];
      if (rid) proved.push(rid);
    } else if (e.kind === "check" && e.status && typeof e.status === "object") {
      for (const [th, v] of Object.entries(e.status as Record<string, unknown>)) {
        const rid = state.theoremToReq[short(th)];
        if (rid && v === "PROVED") proved.push(rid);
      }
    }
    for (const rid of proved) {
      if (provedSeen.has(rid) || state.claims[rid]?.session !== "proved") continue;
      provedSeen.add(rid);
      b.proved.push(rid);
    }
  }
  const max = Math.max(1, ...bins.map((b) => b.turns + b.tools + b.versions));
  return { span, now, bins, max };
}
