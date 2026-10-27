import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { openJobStream } from "@/lib/stream";
import type { StreamEvent } from "@/lib/events";

// Minimal stand-in for the browser EventSource.
class FakeEventSource {
  static CONNECTING = 0;
  static OPEN = 1;
  static CLOSED = 2;
  static instances: FakeEventSource[] = [];
  readyState = FakeEventSource.CONNECTING;
  onopen: (() => void) | null = null;
  onmessage: ((m: { data: string; lastEventId: string }) => void) | null = null;
  onerror: (() => void) | null = null;
  constructor(public url: string) {
    FakeEventSource.instances.push(this);
  }
  open() {
    this.readyState = FakeEventSource.OPEN;
    this.onopen?.();
  }
  send(id: number, data: object) {
    this.onmessage?.({ data: JSON.stringify(data), lastEventId: String(id) });
  }
  fail(closed: boolean) {
    if (closed) this.readyState = FakeEventSource.CLOSED;
    this.onerror?.();
  }
  close() {
    this.readyState = FakeEventSource.CLOSED;
  }
}

describe("openJobStream", () => {
  beforeEach(() => {
    FakeEventSource.instances = [];
    vi.stubGlobal("EventSource", FakeEventSource);
    vi.useFakeTimers();
  });
  afterEach(() => {
    vi.useRealTimers();
    vi.unstubAllGlobals();
  });

  it("reconnects after the connection closes and drops repeated events", () => {
    const got: StreamEvent[] = [];
    const states: string[] = [];
    openJobStream("abc", { onEvent: (e) => got.push(e), onConnection: (s) => states.push(s) });
    const first = FakeEventSource.instances[0]!;
    expect(first.url).toMatch(/\/api\/jobs\/abc\/events$/);
    first.open();
    first.send(0, { kind: "job", state: "CREATED" });
    first.send(1, { kind: "job", state: "DIAGNOSING", label: "Recorded run" });
    first.fail(true);
    expect(states).toContain("reconnecting");
    vi.advanceTimersByTime(10000);
    const second = FakeEventSource.instances[1]!;
    expect(second).toBeDefined();
    second.open();
    // A fresh EventSource cannot send Last-Event-ID, so the server repeats from 0.
    second.send(0, { kind: "job", state: "CREATED" });
    second.send(1, { kind: "job", state: "DIAGNOSING", label: "Recorded run" });
    second.send(2, { kind: "turn", label: "implement", turn: 0 });
    expect(got.map((e) => e.id)).toEqual([0, 1, 2]);
  });

  it("closes the stream after a terminal job state so the browser does not reconnect", () => {
    const got: StreamEvent[] = [];
    const states: string[] = [];
    openJobStream("abc", { onEvent: (e) => got.push(e), onConnection: (s) => states.push(s) });
    const es = FakeEventSource.instances[0]!;
    es.open();
    es.send(0, { kind: "job", state: "CHECKING", label: "Fresh check of stored artifact" });
    es.send(1, { kind: "job", state: "COMPLETE" });
    expect(es.readyState).toBe(FakeEventSource.CLOSED);
    expect(states[states.length - 1]).toBe("closed");
    es.fail(true);
    vi.advanceTimersByTime(20000);
    expect(FakeEventSource.instances.length).toBe(1);
  });

  it("lets the browser retry transient errors itself and stops on unsubscribe", () => {
    const stop = openJobStream("abc", { onEvent: () => {} });
    const es = FakeEventSource.instances[0]!;
    es.fail(false);
    vi.advanceTimersByTime(20000);
    expect(FakeEventSource.instances.length).toBe(1);
    stop();
    expect(es.readyState).toBe(FakeEventSource.CLOSED);
  });

  it("ignores malformed messages", () => {
    const got: StreamEvent[] = [];
    openJobStream("abc", { onEvent: (e) => got.push(e) });
    const es = FakeEventSource.instances[0]!;
    es.onmessage?.({ data: "not json", lastEventId: "0" });
    es.onmessage?.({ data: '{"kind":"job"}', lastEventId: "" });
    expect(got).toEqual([]);
  });
});
