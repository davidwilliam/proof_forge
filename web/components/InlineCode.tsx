import type { ReactNode } from "react";

/** Text copied from Markdown: code spans in backticks become <code>, links [text](url) keep their text; the rest stays text. */
export function inlineCode(s: string): ReactNode[] {
  return s
    .replace(/\[([^\]]+)\]\([^)]+\)/g, "$1")
    .split(/(`[^`]+`)/)
    .map((p, i) => (p.length > 1 && p.startsWith("`") && p.endsWith("`") ? <code key={i}>{p.slice(1, -1)}</code> : p));
}
