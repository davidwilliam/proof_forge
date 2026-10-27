import type { ReactNode } from "react";

/** A status word with its color. The word is always shown; color is never the only signal. */
export function Status({ value, children }: { value: string | null | undefined; children?: ReactNode }) {
  const v = (value || "pending").toUpperCase();
  let cls = "status-pending";
  if (["VERIFIED", "PASS", "ACCEPTED", "PROVED", "PROVED IN SESSION", "ACCEPT", "COMPLETE", "OK"].includes(v)) cls = "status-verified";
  else if (["REFUTED", "FAILED", "REJECTED", "ERROR", "BUILD_FAILED", "REJECT", "SORRY", "MISSING"].includes(v)) cls = "status-refuted";
  else if (["UNRESOLVED", "PARTIAL", "BUDGET_STOP", "TIMEOUT"].includes(v)) cls = "status-unresolved";
  else if (["TESTED_ONLY"].includes(v)) cls = "status-tested";
  else if (["IN PROGRESS", "CHECKING", "DIAGNOSING", "CREATED"].includes(v)) cls = "status-working";
  return <span className={`status ${cls}`}>{children ?? value ?? "pending"}</span>;
}

/** Preformatted code with compiler errors and goal lines highlighted. */
export function Code({ text, wrap = false, className = "" }: { text: string; wrap?: boolean; className?: string }) {
  const lines = text.replace(/\n+$/, "").split("\n");
  return (
    <pre className={`${wrap ? "wrap" : ""} ${className}`.trim()}>
      <code>
        {lines.map((l, i) => {
          let cls: string | undefined;
          if (/(^|\s|:)error(:|\s)/i.test(l) || /^REVERTED|NOT ACCEPTED/.test(l)) cls = "line-error";
          else if (/^\s*(⊢|case )/.test(l)) cls = "line-goal";
          return (
            <span key={i} className={cls}>
              {l}
              {i < lines.length - 1 ? "\n" : ""}
            </span>
          );
        })}
      </code>
    </pre>
  );
}

export function ErrorBox({ title, message, children }: { title: string; message?: string; children?: ReactNode }) {
  return (
    <div className="error-box" role="alert">
      <strong>{title}</strong>
      {message ? <p style={{ margin: "4px 0 0" }}>{message}</p> : null}
      {children}
    </div>
  );
}

export function Hash({ value, full = false }: { value: string | null | undefined; full?: boolean }) {
  if (!value) return <span className="muted">none</span>;
  const v = value.startsWith("sha256:") ? value.slice(7) : value;
  return (
    <span className="hash" title={v}>
      {full ? v : v.slice(0, 16)}
    </span>
  );
}
