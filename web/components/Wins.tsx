import type { ReactNode } from "react";
import { githubFile } from "@/lib/flagships";
import {
  DIMENSIONS,
  modelName,
  pValue,
  seconds,
  usd,
  type Comparison,
  type Headline,
  type Outcome,
} from "@/lib/wins";

/** The headline wins as cards: figure and sentence, then the significance and limits, then the links. */
export function WinsHeadline({ items, headingLevel = 3 }: { items: Headline[]; headingLevel?: 2 | 3 }) {
  const H = headingLevel === 2 ? "h2" : "h3";
  return (
    <ul className="wins-headline" aria-label="Headline wins">
      {items.map((h) => (
        <li key={h.key} className="card win-card">
          <H className="win-figure">
            {h.figure} <span className="win-figure-alt">{h.figureAlt}</span>
          </H>
          <p className="win-text">{h.text}</p>
          <p className="win-note">{h.note}</p>
          <p className="win-links">
            {h.links.map((l) => (
              <a key={l.path} href={githubFile(l.path)}>
                {l.label}
              </a>
            ))}
          </p>
        </li>
      ))}
    </ul>
  );
}

const LETTER: Record<Outcome, string> = { win: "W", tie: "T", loss: "L", "n/a": "-" };

function OutcomeChips({ c }: { c: Comparison }) {
  return (
    <span className="wo-chips">
      {DIMENSIONS.map((d) => {
        const o = c.classification[d.key];
        return (
          <span key={d.key} className="wo-chip" data-outcome={o} title={`${d.label}: ${o}`}>
            <span aria-hidden="true">{LETTER[o]}</span>
            <span className="sr-only">
              {d.label}: {o}.
            </span>
          </span>
        );
      })}
    </span>
  );
}

const pair = (a: ReactNode, b: ReactNode) => (
  <>
    <span className="wt-v">{a}</span> <span className="wt-sep">/</span> <span className="wt-v">{b}</span>
  </>
);

function Row({ c }: { c: Comparison }) {
  const al = c.alone;
  const pf = c.proofforge;
  return (
    <tr>
      <td className="wt-id">
        <code>{c.id}</code>
        <span className="ledger-sub">
          {modelName(c.model)}, {al.arm} against {pf.arm}
          {c.flags.length ? `; ${c.flags.join("; ")}` : ""}
        </span>
      </td>
      <td data-label="Verified, alone / ProofForge">{pair(`${al.verified} of ${al.runs}`, `${pf.verified} of ${pf.runs}`)}</td>
      <td data-label="List $ per verified run">{pair(usd(al.usdPerVerified), usd(pf.usdPerVerified))}</td>
      <td data-label="Wall time">{pair(seconds(c.time.alone), seconds(c.time.proofforge))}</td>
      <td data-label="Requirements proved, mean">
        {pair(`${al.reqMean}`, `${pf.reqMean}`)} of {Math.max(al.reqTotal, pf.reqTotal)}
      </td>
      <td data-label="Cap stops">{pair(al.capStops, pf.capStops)}</td>
      <td data-label="Test">
        {c.test ? (
          <>
            p = {pValue(c.test.p)}
            <span className="ledger-sub">{c.test.preregistered ? "preregistered" : "not preregistered"}</span>
          </>
        ) : (
          <span className="muted">none</span>
        )}
      </td>
      <td data-label="V C T R S">
        <OutcomeChips c={c} />
      </td>
    </tr>
  );
}

/** Every comparison of a set, ties and losses included, in the ledger's order. */
export function ComparisonTable({ rows, caption }: { rows: Comparison[]; caption: string }) {
  return (
    <div className="ledger-wrap">
      <table className="ledger wins-table">
        <caption>{caption}</caption>
        <thead>
          <tr>
            <th scope="col">Comparison</th>
            <th scope="col">Verified, alone / ProofForge</th>
            <th scope="col">List $ per verified run</th>
            <th scope="col">Wall time</th>
            <th scope="col">Requirements proved, mean</th>
            <th scope="col">Cap stops</th>
            <th scope="col">Test</th>
            <th scope="col">
              <span aria-hidden="true" className="wo-head">
                {DIMENSIONS.map((d) => (
                  <span key={d.key}>{d.letter}</span>
                ))}
              </span>
              <span className="sr-only">For ProofForge, by dimension</span>
            </th>
          </tr>
        </thead>
        <tbody>
          {rows.map((c) => (
            <Row key={c.id} c={c} />
          ))}
        </tbody>
      </table>
    </div>
  );
}
