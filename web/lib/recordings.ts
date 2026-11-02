// What each recorded session under recordings/ contains, for the forge session's start screen.
// Every figure is taken from recordings/<id>/summary.json and recordings/<id>/events.jsonl and
// pinned to those files by tests/forge-view.test.ts. These are in-session facts: the Passport
// verdicts come only from the fresh check a replay runs on the stored artifact.

export interface RecordingFacts {
  id: string;
  task: string;
  arm: string;
  /** Repairer and prover model id (the start event). */
  model: string;
  /** Lemma planner model id, or null when the session ran without one. */
  planner: string | null;
  /** Model turns (turn events). */
  turns: number;
  /** Tool calls (tool events), or null for the earlier format that did not record them. */
  toolCalls: number | null;
  /** Candidate versions written. */
  versions: number;
  /** Recorded session time in seconds (summary.json). */
  elapsedS: number;
  /** The in-session judge (Comparator and leanchecker) accepted the last version. */
  acceptedInSession: boolean;
  /** Required theorems the session's own last check found proved, and the ones it left open. */
  proved: number;
  theorems: number;
  open: string[];
  /** Model spend at list price and as billed, when the session recorded it. */
  usdList: number | null;
  usdBilled: number | null;
  /** Repository path of the evidence this session produced, when there is one. */
  evidence: string | null;
}

export const RECORDING_FACTS: Record<string, RecordingFacts> = {
  "flagship-a2-run7": {
    id: "flagship-a2-run7",
    task: "payout-flagship",
    arm: "A2",
    model: "muse-spark-1.3-contributor",
    planner: "muse-wonder-1.0",
    turns: 88,
    toolCalls: null,
    versions: 54,
    elapsedS: 1213,
    acceptedInSession: true,
    proved: 8,
    theorems: 8,
    open: [],
    usdList: null,
    usdBilled: null,
    evidence: "formal/evidence/muse-repair-002",
  },
  "flagship-a2-20261027": {
    id: "flagship-a2-20261027",
    task: "payout-flagship",
    arm: "A2",
    model: "muse-spark-1.3-contributor",
    planner: "muse-wonder-1.0",
    turns: 147,
    toolCalls: 147,
    versions: 74,
    elapsedS: 3234.9,
    acceptedInSession: false,
    proved: 7,
    theorems: 8,
    open: ["req_conservation"],
    usdList: 2.3785,
    usdBilled: 0.589,
    evidence: null,
  },
};

/** Recordings in display order: the default one first, then the rest as the API lists them. */
export function orderRecordings(recordings: string[], first: string): string[] {
  return recordings.includes(first) ? [first, ...recordings.filter((r) => r !== first)] : recordings;
}
