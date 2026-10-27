// Display helpers shared by the pages. Pure functions only.

export function shortHash(h: string | null | undefined, n = 12): string {
  if (!h) return "none";
  const s = h.startsWith("sha256:") ? h.slice(7) : h;
  return s.slice(0, n);
}

/**
 * Plain-language requirement text. The API extracts the predicate docstring; older
 * server builds could return several concatenated docstrings, so keep only the last one
 * and drop the leading "REQ-ID:" prefix when it repeats the id shown next to it.
 */
export function requirementText(text: string | null | undefined, id?: string): string {
  if (!text) return "";
  let t = text;
  const last = t.lastIndexOf("/--");
  if (last >= 0) t = t.slice(last + 3);
  t = t.replace(/-\/\s*$/, "").trim();
  if (id && t.startsWith(`${id}:`)) t = t.slice(id.length + 1).trim();
  return t.charAt(0).toUpperCase() + t.slice(1);
}

/** The Lean definition of the predicate a requirement applies, extracted from Spec.lean. */
export function predicateSource(spec: string | undefined, statement: string | null | undefined): string | null {
  if (!spec || !statement) return null;
  const pred = statement.trim().split(/\s+/)[0];
  if (!pred) return null;
  const lines = spec.split("\n");
  const start = lines.findIndex((l) => new RegExp(`^def ${pred.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`).test(l));
  if (start < 0) return null;
  const out: string[] = [];
  for (let i = start; i < lines.length; i++) {
    const l = lines[i] ?? "";
    if (i > start && (l.trim() === "" || /^(\/--|\/-!|def |theorem |end |structure |abbrev )/.test(l))) break;
    out.push(l);
  }
  return out.join("\n");
}

export interface ModelInfo {
  name: string;
  role: string;
}

/** Human name and role of a Meta model id as used by the agents. */
export function modelInfo(id: string | null | undefined, label?: string | null): ModelInfo {
  const raw = id || "";
  const m = /^muse-(spark|wonder)-([\d.]+)/.exec(raw);
  const family = m?.[1] === "wonder" ? "Muse Wonder" : m?.[1] === "spark" ? "Muse Spark" : raw || "Model";
  const name = m ? `${family} ${m[2]}` : family;
  let role = "agent";
  if (m?.[1] === "wonder") role = "lemma planner";
  else if (m?.[1] === "spark") role = label === "implement" ? "repairer" : "prover";
  return { name, role };
}

/** Readable description of a dialog label such as "pass1:req_fair_shares" or "d1:plan0_x". */
export function dialogLabel(label: string | null | undefined): string {
  if (!label) return "";
  if (label === "implement") return "Phase 1: fix the implementation until the tests pass";
  if (label === "free") return "Free session";
  const [stage, target] = label.split(":", 2);
  if (!target) return label;
  if (stage === "pass1") return `First pass: prove ${target}`;
  const d = /^d(\d+)$/.exec(stage ?? "");
  if (d) return Number(d[1]) === 0 ? `Resolve ${target} with planner support` : `Prove planner lemma ${target} (depth ${d[1]})`;
  return `${stage}: ${target}`;
}

export function dialogTarget(label: string | null | undefined): string | null {
  if (!label) return null;
  const i = label.indexOf(":");
  return i >= 0 ? label.slice(i + 1) : null;
}

export function formatDuration(seconds: number | null | undefined): string {
  if (seconds == null || !Number.isFinite(seconds)) return "none";
  const s = Math.max(0, Math.round(seconds));
  const h = Math.floor(s / 3600);
  const m = Math.floor((s % 3600) / 60);
  const r = s % 60;
  if (h) return `${h} h ${m} min ${r} s`;
  if (m) return `${m} min ${r} s`;
  return `${r} s`;
}

export function formatMs(ms: number | null | undefined): string {
  if (ms == null || !Number.isFinite(ms)) return "";
  if (ms < 1000) return `${Math.round(ms)} ms`;
  return `${(ms / 1000).toFixed(1)} s`;
}

export function formatInt(n: number | null | undefined): string {
  if (n == null || !Number.isFinite(n)) return "none";
  return Math.round(n).toLocaleString("en-US");
}

export function formatUsd(n: number | null | undefined): string {
  if (n == null || !Number.isFinite(n)) return "none";
  return `$${n.toFixed(2)}`;
}

export function commandText(cmd: string[] | string | undefined): string {
  if (!cmd) return "";
  if (typeof cmd === "string") return cmd;
  // The judge runs `docker run ... bash -lc "<command>"`; show the inner command first.
  return cmd.map((a) => (/[\s"']/.test(a) ? JSON.stringify(a) : a)).join(" ");
}

export function innerCommand(cmd: string[] | string | undefined): string {
  if (!cmd || typeof cmd === "string") return cmd || "";
  const i = cmd.indexOf("-lc");
  return i >= 0 && cmd[i + 1] ? cmd[i + 1]! : commandText(cmd);
}

export function prettyJson(v: unknown): string {
  try {
    return JSON.stringify(v, null, 2);
  } catch {
    return String(v);
  }
}

/** Pretty-print a string if it holds JSON, otherwise return it unchanged. */
export function maybeJson(s: string): string {
  const t = s.trim();
  if (!(t.startsWith("{") || t.startsWith("["))) return s;
  try {
    return JSON.stringify(JSON.parse(t), null, 2);
  } catch {
    return s;
  }
}
