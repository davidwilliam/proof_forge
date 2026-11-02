"use client";

import { useEffect, useState, type ReactNode } from "react";

/**
 * The incidents as tabs over one panel each. Every panel is rendered on the server; the ones not
 * selected are hidden until picked. A link to #case-<key> selects that case.
 */
export function CaseViewer({ keys, tabs, panels }: { keys: string[]; tabs: ReactNode[]; panels: ReactNode[] }) {
  const [active, setActive] = useState(0);

  useEffect(() => {
    const fromHash = (scroll: boolean) => {
      const m = /^#case-(.+)$/.exec(window.location.hash);
      const i = m ? keys.indexOf(m[1]!) : -1;
      if (i < 0) return;
      setActive(i);
      if (scroll) requestAnimationFrame(() => document.getElementById(`case-tab-${keys[i]}`)?.closest(".cv")?.scrollIntoView({ block: "start" }));
    };
    fromHash(true);
    const on = () => fromHash(true);
    window.addEventListener("hashchange", on);
    return () => window.removeEventListener("hashchange", on);
  }, [keys]);

  const onKey = (e: React.KeyboardEvent) => {
    const d = e.key === "ArrowRight" ? 1 : e.key === "ArrowLeft" ? -1 : 0;
    if (!d) return;
    e.preventDefault();
    const n = (active + d + keys.length) % keys.length;
    setActive(n);
    document.getElementById(`case-tab-${keys[n]}`)?.focus();
  };

  return (
    <div className="cv">
      <div className="cv-tabs" role="tablist" aria-label="Incidents" onKeyDown={onKey}>
        {tabs.map((t, i) => (
          <button
            key={keys[i]}
            id={`case-tab-${keys[i]}`}
            type="button"
            role="tab"
            className="cv-tab"
            aria-selected={i === active}
            aria-controls={`case-${keys[i]}`}
            tabIndex={i === active ? 0 : -1}
            onClick={() => setActive(i)}
          >
            {t}
          </button>
        ))}
      </div>
      {panels.map((p, i) => (
        <div key={keys[i]} id={`case-${keys[i]}`} className="cv-panel" role="tabpanel" aria-labelledby={`case-tab-${keys[i]}`} hidden={i !== active}>
          {p}
        </div>
      ))}
    </div>
  );
}
