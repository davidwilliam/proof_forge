"use client";

import { useState } from "react";
import type { DotGroup, MatrixRow } from "@/lib/home-view";

const COLS = [
  { key: "alone", label: "Muse alone" },
  { key: "proofforge", label: "Muse with ProofForge" },
  { key: "spec", label: "From the specification alone" },
] as const;

type Pick = { row: number; col: (typeof COLS)[number]["key"]; group: string };

function Dots({ g }: { g: DotGroup }) {
  return (
    <span className="cm-dots" aria-hidden="true">
      {Array.from({ length: g.runs }, (_, i) => (
        <span key={i} className={i < g.verified ? "cm-d cm-d-on" : "cm-d"} />
      ))}
    </span>
  );
}

/** Requirements of the vulnerable code: filled when refuted with a kernel-checked counterexample, outlined when refuted by the rebuilt executable only. */
function CexMarks({ r, total }: { r: MatrixRow["refutations"][number]; total: number }) {
  return (
    <span className="cm-cex" role="img" aria-label={`${r.label}: ${r.refuted} of ${total} requirements refuted, ${r.kernelChecked} of them with a kernel-checked counterexample`}>
      <span className="cm-cex-marks" aria-hidden="true">
        {Array.from({ length: total }, (_, i) => (
          <span key={i} className="cm-q" data-s={i < r.kernelChecked ? "kernel" : i < r.refuted ? "refuted" : "none"} />
        ))}
      </span>
      <span className="cm-cex-text">
        <strong>
          {r.kernelChecked} of {r.refuted}
        </strong>{" "}
        {r.label}
      </span>
    </span>
  );
}

/**
 * The six real failures: per failure, one group of dots per set of runs (filled when verified) for Muse
 * alone, Muse with ProofForge and implementation from the specification, and the vulnerable code's
 * refuted requirements. Pointing at a group or focusing it shows its runs in the readout below, whose
 * height is fixed.
 */
export function CompareMatrix({ rows, initial }: { rows: MatrixRow[]; initial: Pick }) {
  const [pick, setPick] = useState<Pick>(initial);
  const row = rows[pick.row]!;
  const g = row[pick.col].find((x) => x.key === pick.group) ?? row[pick.col][0]!;
  const colLabel = COLS.find((c) => c.key === pick.col)!.label;
  return (
    <div className="cm">
      <div className="cm-legend" aria-hidden="true">
        <span>
          <span className="cm-d cm-d-on" /> run verified
        </span>
        <span>
          <span className="cm-d" /> run not verified
        </span>
        <span>
          <span className="cm-q" data-s="kernel" /> requirement refuted, kernel-checked counterexample
        </span>
        <span>
          <span className="cm-q" data-s="refuted" /> refuted by the rebuilt executable
        </span>
      </div>
      <div className="cm-grid" role="table" aria-label="Muse alone and Muse with ProofForge on six real failures">
        <div className="cm-head" role="row">
          <span role="columnheader">Failure</span>
          {COLS.map((c) => (
            <span key={c.key} role="columnheader">
              {c.label}
            </span>
          ))}
          <span role="columnheader">Vulnerable code, counterexamples</span>
        </div>
        {rows.map((r, ri) => (
          <div key={r.key} className="cm-row" role="row" data-lead={r.proofforge.some((x) => x.lead) || undefined}>
            <span className="cm-name" role="rowheader">
              {r.href ? (
                <a href={r.href}>
                  {r.incident}, {r.year}
                </a>
              ) : (
                <strong>
                  {r.incident}, {r.year}
                </strong>
              )}
              <span className="cm-sub">{r.loss}</span>
            </span>
            {COLS.map((c) => (
              <span key={c.key} className="cm-cell" role="cell" data-label={c.label}>
                {r[c.key].map((x) => {
                  const on = pick.row === ri && pick.col === c.key && g.key === x.key;
                  return (
                    <button
                      key={x.key}
                      type="button"
                      className="cm-g"
                      data-lead={x.lead || undefined}
                      aria-pressed={on}
                      aria-label={`${r.incident}, ${c.label}, ${x.label}: ${x.verified} of ${x.runs} ${x.runs === 1 ? "run" : "runs"} verified`}
                      onMouseEnter={() => setPick({ row: ri, col: c.key, group: x.key })}
                      onFocus={() => setPick({ row: ri, col: c.key, group: x.key })}
                      onClick={() => setPick({ row: ri, col: c.key, group: x.key })}
                    >
                      <Dots g={x} />
                      <span className="cm-g-text">
                        <strong>
                          {x.verified} of {x.runs}
                        </strong>{" "}
                        {x.label}
                      </span>
                    </button>
                  );
                })}
              </span>
            ))}
            <span className="cm-cell" role="cell" data-label="Vulnerable code, counterexamples">
              {r.refutations.map((x) => (
                <CexMarks key={x.label} r={x} total={r.requirements} />
              ))}
            </span>
          </div>
        ))}
      </div>
      <p className="cm-readout" aria-live="polite">
        <strong>
          {row.incident}, {colLabel}, {g.label}: {g.verified} of {g.runs}
        </strong>
        <span>{g.detail}</span>
      </p>
    </div>
  );
}
