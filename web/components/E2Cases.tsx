"use client";

import { useState } from "react";
import { getJson } from "@/lib/api";
import { shortHash } from "@/lib/format";
import { isE2, type E2Row } from "@/lib/results";
import { Status } from "./ui";

const PAGE = 50;

/**
 * Every case of one E2 result set. The rows are fetched from GET /api/results when the list is
 * opened and shown 50 at a time, so the results page does not ship them as HTML.
 */
export function E2Cases({ name, count }: { name: string; count: number }) {
  const [rows, setRows] = useState<E2Row[] | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [page, setPage] = useState(0);
  const [loading, setLoading] = useState(false);

  const load = async () => {
    if (rows || loading) return;
    setLoading(true);
    try {
      const data = await getJson<Record<string, unknown>>("/api/results");
      const set = data[name];
      if (!isE2(set)) throw new Error(`the API has no case list for ${name}`);
      setRows(set.rows);
    } catch (e) {
      setError((e as Error).message);
    } finally {
      setLoading(false);
    }
  };

  const pages = rows ? Math.max(1, Math.ceil(rows.length / PAGE)) : 0;
  const shown = rows ? rows.slice(page * PAGE, page * PAGE + PAGE) : [];

  return (
    <details style={{ marginTop: 12 }} onToggle={(e) => (e.currentTarget as HTMLDetailsElement).open && load()}>
      <summary>All {count} cases</summary>
      {error ? <p className="small muted">Could not load the cases: {error}</p> : null}
      {loading ? <p className="small muted">Loading the cases.</p> : null}
      {rows ? (
        <>
          <div className="table-scroll">
            <table className="small">
              <thead>
                <tr>
                  <th>Task</th>
                  <th>Case</th>
                  <th>Label</th>
                  <th>Ordinary</th>
                  <th>Rebuild and tests</th>
                  <th>ProofForge</th>
                  <th>ProofForge reason</th>
                </tr>
              </thead>
              <tbody>
                {shown.map((r, i) => (
                  <tr key={page * PAGE + i}>
                    <td className="mono">{r.task}</td>
                    <td>
                      <span className="mono">{r.case}</span>
                      {r.note ? <div className="muted">{r.note}</div> : null}
                      {r.sha256 ? <div className="muted hash">{shortHash(r.sha256)}</div> : null}
                    </td>
                    <td>{r.label}</td>
                    <td>
                      <Status value={r.ordinary.accepted === (r.label === "good") ? "PASS" : "REFUTED"}>{r.ordinary.accepted ? "accept" : "reject"}</Status>
                    </td>
                    <td>{r.proofforge.binary === undefined ? "not recorded" : r.proofforge.binary === "PASS" ? "accept" : "reject"}</td>
                    <td>
                      <Status value={r.proofforge.accepted === (r.label === "good") ? "PASS" : "REFUTED"}>{r.proofforge.accepted ? "accept" : "reject"}</Status>
                    </td>
                    <td className="mono">{r.proofforge.reason || "none"}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          <div className="row small" style={{ marginTop: 8, gap: 10, flexWrap: "wrap" }}>
            <button type="button" onClick={() => setPage((p) => Math.max(0, p - 1))} disabled={page === 0}>
              Previous
            </button>
            <span>
              Cases {page * PAGE + 1} to {Math.min(rows.length, (page + 1) * PAGE)} of {rows.length}
            </span>
            <button type="button" onClick={() => setPage((p) => Math.min(pages - 1, p + 1))} disabled={page >= pages - 1}>
              Next
            </button>
          </div>
          <p className="small muted">Green marks a correct decision; red marks a wrong one (a bad case accepted or a good case rejected).</p>
        </>
      ) : null}
    </details>
  );
}
