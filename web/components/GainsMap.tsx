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

function Readout({ r }: { r: WinRow }) {
  return (
    <div className="gm-readout" aria-live="polite">
      <p className="win-item-head">
        <span className="gm-swatch" data-kind={r.kind} aria-hidden="true" />
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
    </div>
  );
}

/** Every win of the ledger as one tile, by group, coloured by source; pointing at a tile shows its ledger sentence. Every sentence is also listed as text. */
export function GainsMap({ rows, groups }: { rows: WinRow[]; groups: WinGroup[] }) {
  const [group, setGroup] = useState("all");
  const [kind, setKind] = useState("all");
  const [model, setModel] = useState("all");
  const [active, setActive] = useState(rows[0]!.key);
  const [pinned, setPinned] = useState<string | null>(null);
  const uid = useId();
  const kinds = [...new Map(rows.map((r) => [r.kind, r.kindLabel])).entries()];
  const models = [...new Set(rows.map((r) => r.model))];
  const match = (r: WinRow) => (group === "all" || String(r.group) === group) && (kind === "all" || r.kind === kind) && (model === "all" || r.model === model);
  const shown = rows.filter(match);
  const current = rows.find((r) => r.key === (pinned ?? active)) ?? rows[0]!;
  return (
    <div className="wins-explorer gm">
      <div className="wins-filters" role="group" aria-label="Filter the gains">
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
          {shown.length} of {rows.length} gains shown. Point at a tile to read it; select it to keep it.
        </p>
      </div>
      <ul className="gm-legend" aria-label="Sources">
        {kinds.map(([k, label]) => (
          <li key={k}>
            <span className="gm-swatch" data-kind={k} aria-hidden="true" />
            {label}, {rows.filter((r) => r.kind === k).length}
          </li>
        ))}
      </ul>
      <Readout r={current} />
      <div className="gm-groups">
        {groups.map((g) => {
          const items = rows.filter((r) => r.group === g.group);
          const n = items.filter(match).length;
          return (
            <section key={g.group} className="gm-group" id={`group-${g.group}`} aria-labelledby={`${uid}-h${g.group}`}>
              <h3 id={`${uid}-h${g.group}`}>
                <span className="gm-count">{items.length}</span> {g.title}
              </h3>
              <p className="gm-text">
                {n !== items.length ? `${n} with these filters. ` : ""}
                {g.text}
              </p>
              <div className="gm-tiles" role="list">
                {items.map((r) => {
                  const on = match(r);
                  return (
                    <button
                      key={r.key}
                      type="button"
                      role="listitem"
                      className="gm-tile"
                      data-kind={r.kind}
                      data-dim={on ? undefined : ""}
                      aria-pressed={pinned === r.key}
                      aria-label={`${r.id}, ${r.kindLabel}`}
                      tabIndex={on ? 0 : -1}
                      onMouseEnter={() => setActive(r.key)}
                      onFocus={() => setActive(r.key)}
                      onClick={() => setPinned(pinned === r.key ? null : r.key)}
                    />
                  );
                })}
              </div>
            </section>
          );
        })}
      </div>
      <details className="wins-details gm-text-list">
        <summary>Every gain as text, {shown.length} with these filters</summary>
        {groups.map((g) => {
          const items = shown.filter((r) => r.group === g.group);
          if (!items.length) return null;
          return (
            <div key={g.group} className="wins-group">
              <h3>
                Gains ({g.group}): {g.title.charAt(0).toLowerCase() + g.title.slice(1)}
              </h3>
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
            </div>
          );
        })}
      </details>
    </div>
  );
}
