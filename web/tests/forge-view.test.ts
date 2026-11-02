import { describe, expect, it } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { initialState, parseJsonl, reduceAll, type RawEvent, type StreamEvent } from "@/lib/events";
import { buildTimeline, claimMark, stageStates } from "@/lib/forge-view";
import { RECORDING_FACTS, orderRecordings } from "@/lib/recordings";

const ROOT = path.resolve(import.meta.dirname, "../..");
const RECORDINGS = path.join(ROOT, "recordings");

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

const load = (name: string): StreamEvent[] => parseJsonl(fs.readFileSync(path.join(RECORDINGS, name, "events.jsonl"), "utf8"));
const summary = (name: string) => JSON.parse(fs.readFileSync(path.join(RECORDINGS, name, "summary.json"), "utf8")) as Record<string, unknown>;

/** Wrap recorded events as server/app.py run_replay and verify_job emit them, including the wall-time summary event. */
function asReplay(name: string, passportStatus: string): StreamEvent[] {
  const now = 2_000_000_000;
  const out: RawEvent[] = [
    { kind: "job", state: "CREATED", t: now },
    { kind: "job", state: "DIAGNOSING", label: "Recorded run", recording: name, t: now },
    ...load(name).map((e, i) => ({ ...e.data, recorded_t: e.data.t, t: now + 1 + i * 0.1 })),
    { kind: "job", state: "CHECKING", label: "Fresh check of stored artifact", t: now + 100 },
    { kind: "summary", t: now + 110 },
    {
      kind: "passport",
      passport_sha256: "f".repeat(64),
      status: passportStatus,
      requirements: Object.fromEntries(REQS.map((r) => [r.id, passportStatus])),
      label: "Fresh check of stored artifact",
      t: now + 120,
    },
    { kind: "job", state: passportStatus === "VERIFIED" ? "COMPLETE" : "PARTIAL", t: now + 120 },
  ];
  return out.map((data, id) => ({ id, data }));
}

describe("recording facts on the start screen", () => {
  for (const [name, f] of Object.entries(RECORDING_FACTS)) {
    describe(name, () => {
      const events = load(name);
      const s = reduceAll(initialState(REQS), events);
      const sum = summary(name);
      const budget = (sum.budget ?? {}) as Record<string, unknown>;
      const finals = sum.final_status as Record<string, string>;

      it("names the models of the start event", () => {
        expect(f.model).toBe(s.start?.model);
        expect(f.planner).toBe(s.start?.planner === "none" ? null : s.start?.planner);
        expect(f.model).toBe(sum.model);
      });

      it("counts turns, tool calls and versions as the events do", () => {
        expect(f.turns).toBe(s.counts.turns);
        expect(f.toolCalls).toBe(s.hasToolEvents ? s.counts.tools : null);
        expect(f.versions).toBe(s.counts.versions);
        expect(f.versions).toBe(sum.versions);
      });

      it("takes the recorded time and spend from summary.json", () => {
        expect(f.elapsedS).toBe(sum.elapsed_s ?? budget.elapsed_s);
        expect(f.usdList).toBe((budget.usd_list as number | undefined) ?? null);
        expect(f.usdBilled).toBe((budget.usd_actual as number | undefined) ?? null);
      });

      it("reports the in-session outcome of the last check and judge", () => {
        expect(f.acceptedInSession).toBe(s.judgeAccepted === true);
        expect(f.acceptedInSession).toBe(sum.accepted ?? sum.accepted_in_session);
        expect(f.theorems).toBe(Object.keys(finals).length);
        expect(f.proved).toBe(Object.values(finals).filter((v) => v === "PROVED").length);
        expect(f.open).toEqual(Object.entries(finals).filter(([, v]) => v !== "PROVED").map(([k]) => k));
        expect(f.proved).toBe(Object.values(s.claims).filter((c) => c.session === "proved").length);
      });

      it("points at evidence that exists", () => {
        if (f.evidence) expect(fs.existsSync(path.join(ROOT, f.evidence))).toBe(true);
      });

      it("is listed in recordings/README.md", () => {
        expect(fs.readFileSync(path.join(RECORDINGS, "README.md"), "utf8")).toContain(`\`${name}\``);
      });
    });
  }

  it("covers every recording the API can list", () => {
    const dirs = fs.readdirSync(RECORDINGS).filter((d) => fs.existsSync(path.join(RECORDINGS, d, "events.jsonl")));
    expect(Object.keys(RECORDING_FACTS).sort()).toEqual(dirs.sort());
  });

  it("puts the default recording first", () => {
    expect(orderRecordings(["a", "b", "c"], "b")).toEqual(["b", "a", "c"]);
    expect(orderRecordings(["a", "b"], "z")).toEqual(["a", "b"]);
  });
});

describe("recorded timeline", () => {
  for (const [name, f] of Object.entries(RECORDING_FACTS)) {
    it(`${name}: bins every turn, tool call and version on the recorded axis`, () => {
      const s = reduceAll(initialState(REQS), asReplay(name, "VERIFIED"));
      const tl = buildTimeline(s, f.elapsedS)!;
      const sum = (k: "turns" | "tools" | "versions") => tl.bins.reduce((a, b) => a + b[k], 0);
      expect(sum("turns")).toBe(f.turns);
      expect(sum("tools")).toBe(f.toolCalls ?? 0);
      expect(sum("versions")).toBe(load(name).filter((e) => e.data.kind === "write").length);
      // The summary and passport events carry wall time only; they must not stretch the axis.
      expect(tl.span).toBeCloseTo(Math.max(f.elapsedS, tl.now), 6);
      expect(tl.now).toBeLessThan(f.elapsedS + 1);
      const marks = tl.bins.flatMap((b) => b.proved);
      expect(marks.length).toBe(f.proved);
      expect(new Set(marks).size).toBe(marks.length);
      expect(tl.max).toBe(Math.max(...tl.bins.map((b) => b.turns + b.tools + b.versions)));
    });
  }

  it("grows with the replay: early events fill only the first bins", () => {
    const all = asReplay("flagship-a2-run7", "VERIFIED");
    const s = reduceAll(initialState(REQS), all.slice(0, 40));
    const tl = buildTimeline(s, RECORDING_FACTS["flagship-a2-run7"]!.elapsedS)!;
    expect(tl.span).toBe(1213);
    expect(tl.now).toBeLessThan(tl.span);
    const filled = tl.bins.map((b, i) => (b.turns + b.tools + b.versions > 0 ? i : -1)).filter((i) => i >= 0);
    const last = filled[filled.length - 1]!;
    expect(tl.bins[last]!.from).toBeLessThanOrEqual(tl.now);
  });

  it("has nothing to show before the first recorded event", () => {
    expect(buildTimeline(initialState(REQS), 100)).toBeNull();
  });
});

describe("stages and marks", () => {
  it("moves Lock, Repair, Check and Passport along with the job", () => {
    const all = asReplay("flagship-a2-run7", "VERIFIED");
    const idle = initialState(REQS);
    expect(stageStates(idle, false, "idle")).toEqual(["done", "idle", "idle", "idle"]);
    const mid = reduceAll(idle, all.slice(0, 50));
    expect(stageStates(mid, true, "recorded")).toEqual(["done", "active", "idle", "idle"]);
    const checkAt = all.findIndex((e) => e.data.state === "CHECKING");
    const checking = reduceAll(idle, all.slice(0, checkAt + 1));
    expect(stageStates(checking, true, "check")).toEqual(["done", "done", "active", "idle"]);
    const done = reduceAll(idle, all);
    expect(stageStates(done, true, "check")).toEqual(["done", "done", "done", "done"]);
  });

  it("shows the Passport verdict once there is one, the session state before", () => {
    const all = asReplay("flagship-a2-20261027", "UNRESOLVED");
    const before = reduceAll(initialState(REQS), all.slice(0, -2));
    expect(claimMark(before.claims["REQ-CONSERVATION"]!)).not.toBe("proved");
    expect(claimMark(before.claims["REQ-FAIR-SHARES"]!)).toBe("proved");
    const after = reduceAll(initialState(REQS), all);
    for (const c of Object.values(after.claims)) expect(claimMark(c)).toBe("UNRESOLVED");
  });
});
