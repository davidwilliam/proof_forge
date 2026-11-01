"use client";

import { useId, useState } from "react";
import { Ticked } from "./Ticked";

export interface WinRow {
  key: string;
  group: 1 | 2 | 3;
  id: string;
  kind: string;
  kindLabel: string;
  model: string;
  winKind: string | null;
  detail: string;
  links: { label: string; href: string }[];
}

export interface WinGroup {
  group: 1 | 2 | 3;
  title: string;
  text: string;
}

/** Every win of the ledger by group, filtered by group, source and model. Without JavaScript every win is shown. */
export function WinsExplorer({ rows, groups }: { rows: WinRow[]; groups: WinGroup[] }) {
  const [group, setGroup] = useState("all");
  const [kind, setKind] = useState("all");
  const [model, setModel] = useState("all");
  const uid = useId();
  const kinds = [...new Map(rows.map((r) => [r.kind, r.kindLabel])).entries()];
  const models = [...new Set(rows.map((r) => r.model))];
  const shown = rows.filter((r) => (group === "all" || String(r.group) === group) && (kind === "all" || r.kind === kind) && (model === "all" || r.model === model));
  return (
    <div className="wins-explorer">
      <div className="wins-filters" role="group" aria-label="Filter the wins">
        <label htmlFor={`${uid}-g`}>
          <span>Group</span>
          <select id={`${uid}-g`} value={group} onChange={(e) => setGroup(e.target.value)}>
            <option value="all">All groups</option>
            {groups.map((g) => (
              <option key={g.group} value={String(g.group)}>
                ({g.group}) {g.title}
              </option>
            ))}
          </select>
        </label>
        <label htmlFor={`${uid}-k`}>
          <span>Source</span>
          <select id={`${uid}-k`} value={kind} onChange={(e) => setKind(e.target.value)}>
            <option value="all">All sources</option>
            {kinds.map(([k, label]) => (
              <option key={k} value={k}>
                {label}
              </option>
            ))}
          </select>
        </label>
        <label htmlFor={`${uid}-m`}>
          <span>Model</span>
          <select id={`${uid}-m`} value={model} onChange={(e) => setModel(e.target.value)}>
            <option value="all">All models</option>
            {models.map((m) => (
              <option key={m} value={m}>
                {m}
              </option>
            ))}
          </select>
        </label>
        <p className="wins-count" aria-live="polite">
          {shown.length} of {rows.length} wins shown
        </p>
      </div>
      {groups.map((g) => {
        const items = shown.filter((r) => r.group === g.group);
        const total = rows.filter((r) => r.group === g.group).length;
        if (group !== "all" && String(g.group) !== group) return null;
        return (
          <section key={g.group} className="wins-group" id={`group-${g.group}`} aria-labelledby={`${uid}-h${g.group}`}>
            <h2 id={`${uid}-h${g.group}`}>
              Wins ({g.group}): {g.title.charAt(0).toLowerCase() + g.title.slice(1)}
            </h2>
            <p className="wins-group-lead">
              {total} in the ledger{items.length !== total ? `, ${items.length} with these filters` : ""}. {g.text}
            </p>
            {items.length ? (
              <ol className="win-list">
                {items.map((r) => (
                  <li key={r.key} className="win-item" data-kind={r.kind}>
                    <p className="win-item-head">
                      <code>{r.id}</code>
                      <span className="win-item-meta">
                        {r.model}, {r.kindLabel}
                        {r.winKind ? `, ${r.winKind}` : ""}
                      </span>
                    </p>
                    <p className="win-item-detail">
                      <Ticked text={r.detail} />
                    </p>
                    <p className="win-links">
                      {r.links.map((l) => (
                        <a key={l.href} href={l.href}>
                          {l.label}
                        </a>
                      ))}
                    </p>
                  </li>
                ))}
              </ol>
            ) : (
              <p className="muted">No win in this group matches these filters.</p>
            )}
          </section>
        );
      })}
    </div>
  );
}
