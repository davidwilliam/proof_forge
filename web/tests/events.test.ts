import { describe, expect, it } from "vitest";
import fs from "node:fs";
import path from "node:path";
import {
  KNOWN_KINDS,
  claimWord,
  initialState,
  parseJsonl,
  parseSseMessage,
  reduce,
  reduceAll,
  toolArgs,
  type RawEvent,
  type StreamEvent,
} from "@/lib/events";

const ROOT = path.resolve(import.meta.dirname, "../..");
const RECORDINGS = path.join(ROOT, "recordings");

// The flagship requirements, in the order GET /api/tasks/payout-flagship lists them.
const REQS = [
  ["REQ-VALID-SUCCEEDS", "Payout.req_valid_succeeds"],
  ["REQ-INVALID-NOOP", "Payout.req_invalid_noop"],
  ["REQ-AUTHORIZATION", "Payout.req_authorization"],
  ["REQ-EFFECTS", "Payout.req_effects"],
  ["REQ-IDEMPOTENCY", "Payout.req_idempotency"],
  ["REQ-NONNEGATIVE", "Payout.req_nonnegative"],
  ["REQ-FAIR-SHARES", "Payout.req_fair_shares"],
  ["REQ-CONSERVATION", "Payout.req_conservation"],
].map(([id, theorem]) => ({ id: id!, theorem: theorem! }));

const recordings = fs.existsSync(RECORDINGS)
  ? fs.readdirSync(RECORDINGS).filter((d) => fs.existsSync(path.join(RECORDINGS, d, "events.jsonl")))
  : [];

function load(name: string): StreamEvent[] {
  return parseJsonl(fs.readFileSync(path.join(RECORDINGS, name, "events.jsonl"), "utf8"));
}

/** Wrap recorded agent events the way server/app.py run_replay and verify_job do. */
function asReplayJob(recording: string, events: StreamEvent[], passport: RawEvent): StreamEvent[] {
  const now = 2_000_000_000;
  const out: RawEvent[] = [
    { kind: "job", state: "CREATED", t: now },
    { kind: "job", state: "DIAGNOSING", label: "Recorded run", recording, t: now },
    ...events.map((e, i) => ({ ...e.data, recorded_t: e.data.t, t: now + 1 + i * 0.1 })),
    { kind: "job", state: "CHECKING", label: "Fresh check of stored artifact", t: now + 100 },
    { ...passport, label: "Fresh check of stored artifact", t: now + 120 },
    { kind: "job", state: passport.status === "VERIFIED" ? "COMPLETE" : "PARTIAL", t: now + 120 },
  ];
  return out.map((data, id) => ({ id, data }));
}

const verifiedPassport: RawEvent = {
  kind: "passport",
  passport_sha256: "ae0c49785e0f60fdc8251348463e5d79453003d00551f5ec42bc9919f7c873be",
  status: "VERIFIED",
  requirements: Object.fromEntries(REQS.map((r) => [r.id, "VERIFIED"])),
};

describe("recorded events.jsonl fixtures", () => {
  it("finds the recordings", () => {
    expect(recordings).toContain("flagship-a2-run7");
  });

  for (const name of recordings) {
    describe(name, () => {
      const events = load(name);

      it("contains only event kinds the reducer handles", () => {
        const kinds = new Set(events.map((e) => e.data.kind));
        for (const k of kinds) expect(KNOWN_KINDS as readonly string[]).toContain(k);
        const s = reduceAll(initialState(REQS), events);
        expect(s.unknownKinds).toEqual([]);
      });

      it("keeps every event in the stream, in order, and counts each kind", () => {
        const s = reduceAll(initialState(REQS), events);
        expect(s.items.length).toBe(events.length);
        expect(s.items.map((i) => i.id)).toEqual(events.map((e) => e.id));
        const count = (k: string) => events.filter((e) => e.data.kind === k).length;
        expect(s.counts.turns).toBe(count("turn"));
        expect(s.counts.tools).toBe(count("tool"));
        expect(s.counts.snippets).toBe(count("snippet"));
        expect(s.counts.plans).toBe(count("plan"));
        expect(s.hasToolEvents).toBe(count("tool") > 0);
        const maxVersion = Math.max(0, ...events.filter((e) => e.data.kind === "write").map((e) => Number(e.data.version)));
        expect(s.counts.versions).toBe(maxVersion);
      });

      it("never assigns a final status without a passport event", () => {
        let s = initialState(REQS);
        for (const e of events) {
          s = reduce(s, e);
          for (const c of Object.values(s.claims)) expect(c.final).toBeNull();
        }
        expect(s.passport).toBeNull();
      });

      it("sums token usage from turn events", () => {
        const s = reduceAll(initialState(REQS), events);
        const expected = events
          .filter((e) => e.data.kind === "turn")
          .reduce((a, e) => a + Number((e.data.usage as { completion_tokens?: number } | undefined)?.completion_tokens ?? 0), 0);
        expect(s.usage.completion).toBe(expected);
      });

      it("marks requirements proved in session only after obligation, resolve or check evidence", () => {
        let s = initialState(REQS);
        for (const e of events) {
          const before = s;
          s = reduce(s, e);
          for (const id of s.order) {
            if (before.claims[id]!.session !== "proved" && s.claims[id]!.session === "proved") {
              expect(["obligation", "resolve", "check"]).toContain(e.data.kind);
            }
          }
        }
      });

      it("records in-session test violations from tests events", () => {
        const tests = events.filter((e) => e.data.kind === "tests");
        if (!tests.length) return;
        const first = reduceAll(initialState(REQS), events.slice(0, events.indexOf(tests[0]!) + 1));
        const v = tests[0]!.data.violations as Record<string, number>;
        for (const id of first.order) expect(first.claims[id]!.testViolations).toBe(v[id] ?? 0);
      });

      it("renders tool events with arguments and results", () => {
        for (const e of events.filter((x) => x.data.kind === "tool")) {
          expect(typeof e.data.name).toBe("string");
          expect(toolArgs(e.data)).not.toBeUndefined();
          expect(typeof e.data.result).toBe("string");
        }
      });

      it("maps the full replay job (job, passport and terminal events) to final statuses", () => {
        const job = asReplayJob(name, events, verifiedPassport);
        let s = initialState(REQS);
        const segments: (string | null)[] = [];
        for (const e of job) {
          s = reduce(s, e);
          segments.push(s.segment);
        }
        expect(segments[1]).toBe("Recorded run");
        expect(segments).toContain("Fresh check of stored artifact");
        expect(s.jobState).toBe("COMPLETE");
        expect(s.terminal).toBe(true);
        expect(s.recording).toBe(name);
        expect(s.passport?.status).toBe("VERIFIED");
        for (const c of Object.values(s.claims)) {
          expect(c.final).toBe("VERIFIED");
          expect(claimWord(c)).toBe("VERIFIED");
          expect(c.session).not.toBe("working");
        }
        // Recorded time comes from recorded_t, not from the replay clock.
        const rts = events.map((e) => e.data.t).filter((t): t is number => typeof t === "number");
        expect(s.recordedStart).toBe(rts[0]);
        expect(s.recordedEnd).toBe(rts[rts.length - 1]);
      });
    });
  }
});

describe("flagship-a2-run7 specifics", () => {
  const events = recordings.includes("flagship-a2-run7") ? load("flagship-a2-run7") : [];

  it("ends with every requirement proved in session and the judge accepting", () => {
    const s = reduceAll(initialState(REQS), events);
    for (const c of Object.values(s.claims)) expect(c.session).toBe("proved");
    expect(s.judgeAccepted).toBe(true);
    expect(s.counts.plans).toBe(2);
    expect(s.counts.versions).toBe(54);
  });

  it("shows conservation in progress while the planner decomposes it", () => {
    const planIdx = events.findIndex((e) => e.data.kind === "plan");
    const s = reduceAll(initialState(REQS), events.slice(0, planIdx + 1));
    expect(s.claims["REQ-CONSERVATION"]!.session).toBe("working");
    expect(s.claims["REQ-FAIR-SHARES"]!.session).toBe("proved");
    expect(claimWord(s.claims["REQ-CONSERVATION"]!)).toBe("in progress");
  });

  it("starts with the fair-shares and conservation violations of the buggy build", () => {
    const s = reduceAll(initialState(REQS), events.slice(0, 2));
    expect(s.claims["REQ-FAIR-SHARES"]!.testViolations).toBeGreaterThan(0);
    expect(s.claims["REQ-CONSERVATION"]!.testViolations).toBeGreaterThan(0);
    expect(s.claims["REQ-EFFECTS"]!.testViolations).toBe(0);
  });
});

describe("real job log from runs/jobs (local only)", () => {
  const jobs = path.join(ROOT, "runs", "jobs");
  const dirs = fs.existsSync(jobs) ? fs.readdirSync(jobs).filter((d) => fs.existsSync(path.join(jobs, d, "events.jsonl"))) : [];
  if (dirs.length === 0) it.skip("no job logs in runs/jobs on this machine", () => {});
  for (const d of dirs) {
    it(`job ${d} reduces without unknown kinds`, () => {
      const events = parseJsonl(fs.readFileSync(path.join(jobs, d, "events.jsonl"), "utf8"));
      const s = reduceAll(initialState(REQS), events);
      expect(s.unknownKinds).toEqual([]);
      const pass = events.find((e) => e.data.kind === "passport");
      if (pass) {
        expect(s.passport?.sha).toBe(pass.data.passport_sha256);
        for (const [id, st] of Object.entries(pass.data.requirements as Record<string, string>)) {
          expect(s.claims[id]?.final).toBe(st);
        }
      }
    });
  }
});

describe("stream handling", () => {
  const sample = recordings.includes("flagship-a2-run7") ? load("flagship-a2-run7").slice(0, 40) : [];

  it("drops duplicate and stale ids after a reconnect", () => {
    const once = reduceAll(initialState(REQS), sample);
    const replayed = reduceAll(initialState(REQS), [...sample.slice(0, 25), ...sample.slice(10)]);
    expect(replayed.items.length).toBe(once.items.length);
    expect(replayed).toEqual(once);
  });

  it("parses SSE messages with their ids", () => {
    expect(parseSseMessage('{"kind":"job","state":"CREATED"}', "0")).toEqual({ id: 0, data: { kind: "job", state: "CREATED" } });
    expect(parseSseMessage("not json", "3")).toBeNull();
    expect(parseSseMessage('{"kind":"job"}', "")).toBeNull();
    expect(parseSseMessage('{"state":"x"}', "4")).toBeNull();
  });

  it("handles budget stops, refutations, unresolved claims and failures", () => {
    const ev: RawEvent[] = [
      { kind: "job", state: "DIAGNOSING", label: "Live" },
      { kind: "turn", label: "pass1:req_conservation", turn: 0, model: "muse-spark-1.3", tools: [], text: "" },
      { kind: "budget_stop", reason: "usd" },
      { kind: "job", state: "CHECKING", label: "Live" },
      {
        kind: "passport",
        passport_sha256: "ab",
        status: "REFUTED",
        requirements: { "REQ-CONSERVATION": "REFUTED", "REQ-FAIR-SHARES": "UNRESOLVED", "REQ-EFFECTS": "VERIFIED", "REQ-BOGUS": "VERIFIED" },
      },
      { kind: "job", state: "BUDGET_STOP" },
    ];
    const s = reduceAll(initialState(REQS), ev.map((data, id) => ({ id, data })));
    expect(s.segment).toBe("Live");
    expect(s.budgetStop).toBe("usd");
    expect(s.jobState).toBe("BUDGET_STOP");
    expect(s.claims["REQ-CONSERVATION"]!.final).toBe("REFUTED");
    expect(s.claims["REQ-CONSERVATION"]!.session).toBe("pending");
    expect(s.claims["REQ-FAIR-SHARES"]!.final).toBe("UNRESOLVED");
    expect(s.claims["REQ-EFFECTS"]!.final).toBe("VERIFIED");
    expect(s.claims["REQ-VALID-SUCCEEDS"]!.final).toBeNull();
    expect(Object.keys(s.claims)).not.toContain("REQ-BOGUS");

    const f = reduceAll(initialState(REQS), [{ id: 0, data: { kind: "job", state: "FAILED", reason: "no final candidate" } }]);
    expect(f.failure).toBe("no final candidate");
    expect(f.terminal).toBe(true);
  });

  it("downgrades a claim when a later check reports sorry", () => {
    const ev: RawEvent[] = [
      { kind: "obligation", label: "pass1", theorem: "req_effects", ok: true },
      { kind: "check", version: 3, errors: false, status: { req_effects: "SORRY" } },
    ];
    let s = reduce(initialState(REQS), { id: 0, data: ev[0]! });
    expect(s.claims["REQ-EFFECTS"]!.session).toBe("proved");
    s = reduce(s, { id: 1, data: ev[1]! });
    expect(s.claims["REQ-EFFECTS"]!.session).toBe("pending");
  });

  it("keeps unknown kinds in the stream and reports them", () => {
    const s = reduce(initialState(REQS), { id: 0, data: { kind: "something_new", x: 1 } });
    expect(s.items.length).toBe(1);
    expect(s.unknownKinds).toEqual(["something_new"]);
  });
});

describe("captured SSE transcript of a replay job (tests/fixtures/sse-replay-run7.txt)", () => {
  // Real output of `curl -N /api/jobs/{id}/events` for a run7 replay at speed 80.
  const raw = fs.readFileSync(path.join(import.meta.dirname, "fixtures", "sse-replay-run7.txt"), "utf8");
  const frames = raw.split("\n\n").filter((f) => f.trim());
  const parsed = frames.map((f) => {
    const id = /^id: (.*)$/m.exec(f)?.[1] ?? null;
    const data = /^data: (.*)$/m.exec(f)?.[1] ?? "";
    return parseSseMessage(data, id);
  });

  it("parses every frame with monotonic ids", () => {
    expect(parsed.every((p) => p !== null)).toBe(true);
    expect(parsed.map((p) => p!.id)).toEqual(parsed.map((_, i) => i));
  });

  it("drives the UI state from Recorded run through the fresh check to VERIFIED", () => {
    let s = initialState(REQS);
    const segments = new Set<string | null>();
    for (const e of parsed) {
      s = reduce(s, e!);
      segments.add(s.segment);
      if (s.segment === "Fresh check of stored artifact" && !s.passport) {
        // Before the passport arrives no claim has a final status.
        for (const c of Object.values(s.claims)) expect(c.final).toBeNull();
      }
    }
    expect([...segments]).toEqual([null, "Recorded run", "Fresh check of stored artifact"]);
    expect(s.jobState).toBe("COMPLETE");
    expect(s.terminal).toBe(true);
    expect(s.unknownKinds).toEqual([]);
    expect(s.passport?.status).toBe("VERIFIED");
    for (const c of Object.values(s.claims)) expect(claimWord(c)).toBe("VERIFIED");
    // Replayed events keep their recorded time, so session time is the recorded span.
    expect(s.recordedEnd! - s.recordedStart!).toBeGreaterThan(1000);
    expect(s.wallEnd! - s.wallStart!).toBeLessThan(600);
  });
});
