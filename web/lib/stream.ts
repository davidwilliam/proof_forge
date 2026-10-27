// Browser EventSource consumer for GET /api/jobs/{id}/events with reconnection.
// EventSource retries on its own and sends Last-Event-ID, which the server resumes from.
// If the connection is closed for good (for example the server restarted), a new
// EventSource is opened with backoff; events it repeats are dropped by id.

import { apiUrl } from "./api";
import { parseSseMessage, TERMINAL_STATES, type StreamEvent } from "./events";

export type ConnectionState = "connecting" | "open" | "reconnecting" | "closed";

export interface JobStreamHandlers {
  onEvent: (e: StreamEvent) => void;
  onConnection?: (s: ConnectionState) => void;
}

export function openJobStream(jobId: string, h: JobStreamHandlers): () => void {
  let es: EventSource | null = null;
  let lastId = -1;
  let stopped = false;
  let attempt = 0;
  let timer: ReturnType<typeof setTimeout> | null = null;

  const connect = () => {
    if (stopped) return;
    h.onConnection?.(attempt === 0 ? "connecting" : "reconnecting");
    es = new EventSource(apiUrl(`/api/jobs/${encodeURIComponent(jobId)}/events`));
    es.onopen = () => {
      attempt = 0;
      h.onConnection?.("open");
    };
    es.onmessage = (m: MessageEvent<string>) => {
      const ev = parseSseMessage(m.data, m.lastEventId);
      if (!ev || ev.id <= lastId) return;
      lastId = ev.id;
      h.onEvent(ev);
      if (ev.data.kind === "job" && TERMINAL_STATES.has(String(ev.data.state))) {
        // The server ends the stream after a terminal state; stop the browser from reconnecting.
        stop();
        h.onConnection?.("closed");
      }
    };
    es.onerror = () => {
      if (stopped) return;
      if (es && es.readyState === EventSource.CLOSED) {
        es = null;
        attempt += 1;
        h.onConnection?.("reconnecting");
        timer = setTimeout(connect, Math.min(10000, 500 * 2 ** Math.min(attempt, 5)));
      } else {
        h.onConnection?.("reconnecting");
      }
    };
  };

  const stop = () => {
    stopped = true;
    if (timer) clearTimeout(timer);
    es?.close();
    es = null;
  };

  connect();
  return stop;
}
