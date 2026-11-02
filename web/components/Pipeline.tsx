import type { ReactNode } from "react";

/** The state of one step and a live detail under its sentence (the forge session uses both). */
export interface PipelineStage {
  state?: "idle" | "active" | "done";
  detail?: ReactNode;
}

const STEPS = [
  ["Lock", <>The owner&apos;s requirements, hashed.</>],
  ["Repair", <>A Muse model fixes the code and proves each one.</>],
  ["Check", <>Fresh Comparator, kernel replay and property tests.</>],
  ["Passport", <>Statuses come only from that check.</>],
] as const;

/** The four steps a repair goes through before it counts. Shared by the home page and the forge session. */
export function Pipeline({ className = "", stages }: { className?: string; stages?: PipelineStage[] }) {
  return (
    <ol className={`pipeline ${className}`.trim()} aria-label="How a repair counts">
      {STEPS.map(([name, text], i) => {
        const st = stages?.[i];
        return (
          <li key={name} data-state={st?.state} aria-current={st?.state === "active" ? "step" : undefined}>
            <strong>{name}</strong>
            {text}
            {st?.detail != null ? <div className="pipeline-detail">{st.detail}</div> : null}
          </li>
        );
      })}
    </ol>
  );
}
