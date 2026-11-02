"use client";

import { useState } from "react";
import type { CellState, E1Grid, E1Run, GridTask } from "@/lib/results-view";

const STATE_TEXT: Record<CellState, string> = {
  done: "completed",
  missed: "not completed",
  outage: "ended by the GPU host's outage, counted as not completed",
  none: "not run",
};

const stopText = (s: string | null) => (s === "usd" ? "stopped at the dollar cap" : s === "wall" ? "stopped at the time cap" : null);

function runText(run: E1Run, price: string): string {
  const parts = [`judge ${run.judge ?? "none"}`, `binary ${run.binary ?? "none"}`];
  const stop = stopText(run.stop);
  if (stop) parts.push(stop);
  if (run.usdList != null) parts.push(`$${run.usdList.toFixed(2)} ${price}`);
  if (run.elapsedS != null) parts.push(`${Math.round(run.elapsedS).toLocaleString("en-US")} s`);
  return parts.join(", ");
}

const markText = { pf: "completed only with ProofForge", alone: "completed only on its own" } as const;

/**
 * One E1 set as a grid: a column per task, a row per arm, grouped by family; a cell is filled when
 * that arm completed the task. Tasks completed only with ProofForge carry a mark under the column.
 * Pointing at or focusing a column shows its runs in the readout below, which has a fixed height.
 */
export function TaskGrid({
  name,
  grid,
  armNames,
  price,
}: {
  name: string;
  grid: E1Grid;
  armNames: Record<string, string>;
  price: string;
}) {
  const all = grid.families.flatMap((f) => f.tasks);
  const first = all.find((t) => t.mark === "pf") ?? all.find((t) => t.mark) ?? all[0]!;
  const [active, setActive] = useState(first.id);
  const cur: GridTask = all.find((t) => t.id === active) ?? first;
  const hasOutage = all.some((t) => grid.arms.some((a) => t.cells[a]!.state === "outage"));
  const hasNone = all.some((t) => grid.arms.some((a) => t.cells[a]!.state === "none"));
  const label = (t: GridTask) =>
    `${t.id}: ${grid.arms.map((a) => `${a} ${STATE_TEXT[t.cells[a]!.state]}`).join(", ")}${t.mark ? `; ${markText[t.mark]}` : ""}`;
  return (
    <figure className="tg" aria-label={`${name}: every task by arm`}>
      <ul className="tg-legend" aria-label="Legend">
        <li>
          <span className="tg-key" data-state="done" aria-hidden="true" />
          Completed
        </li>
        <li>
          <span className="tg-key" data-state="missed" aria-hidden="true" />
          Not completed
        </li>
        {hasOutage ? (
          <li>
            <span className="tg-key" data-state="outage" aria-hidden="true" />
            Ended by the outage
          </li>
        ) : null}
        {hasNone ? (
          <li>
            <span className="tg-key" data-state="none" aria-hidden="true" />
            Not run
          </li>
        ) : null}
        <li>
          <span className="tg-mark" data-mark="pf" aria-hidden="true" />
          Completed only with ProofForge
        </li>
        {grid.aloneOnly ? (
          <li>
            <span className="tg-mark" data-mark="alone" aria-hidden="true" />
            Completed only on its own
          </li>
        ) : null}
      </ul>
      <div className="tg-fams">
        {grid.families.map((f) => (
          <div key={f.family} className="tg-fam">
            <p className="tg-fam-name">{f.family}</p>
            <div className="tg-body">
              <ul className="tg-arms" aria-hidden="true">
                {grid.arms.map((a) => (
                  <li key={a}>{a}</li>
                ))}
              </ul>
              <div className="tg-cols">
                {f.tasks.map((t) => (
                  <button
                    key={t.id}
                    type="button"
                    className="tg-col"
                    data-mark={t.mark ?? undefined}
                    aria-pressed={t.id === cur.id}
                    aria-label={label(t)}
                    onMouseEnter={() => setActive(t.id)}
                    onFocus={() => setActive(t.id)}
                    onClick={() => setActive(t.id)}
                  >
                    {grid.arms.map((a) => (
                      <span key={a} className="tg-cell" data-state={t.cells[a]!.state} />
                    ))}
                    <span className="tg-mark" data-mark={t.mark ?? undefined} />
                  </button>
                ))}
              </div>
              <ul className="tg-counts" aria-label={`${f.family}, completed per arm`}>
                {grid.arms.map((a) => (
                  <li key={a} aria-label={`${a}: ${f.counts[a]!.completed} of ${f.counts[a]!.n}`}>
                    {f.counts[a]!.completed}/{f.counts[a]!.n}
                  </li>
                ))}
              </ul>
            </div>
          </div>
        ))}
      </div>
      <figcaption className="tg-readout" aria-live="polite">
        <p className="tg-readout-head">
          <code>{cur.id}</code>
          <span className="muted">{cur.family}</span>
          {cur.mark ? <strong className="tg-readout-mark">{markText[cur.mark]}</strong> : null}
        </p>
        <ul>
          {grid.arms.map((a) => {
            const c = cur.cells[a]!;
            return (
              <li key={a}>
                <span className="tg-key" data-state={c.state} aria-hidden="true" />
                <span className="tg-readout-arm">
                  {a} {armNames[a] ?? ""}
                </span>{" "}
                {STATE_TEXT[c.state]}
                {c.run ? <span className="muted">: {runText(c.run, price)}</span> : null}
              </li>
            );
          })}
        </ul>
      </figcaption>
    </figure>
  );
}
