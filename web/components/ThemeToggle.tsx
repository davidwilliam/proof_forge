"use client";

import { useEffect, useState } from "react";

type Theme = "system" | "light" | "dark";

export function ThemeToggle() {
  const [theme, setTheme] = useState<Theme>("system");

  useEffect(() => {
    try {
      const t = localStorage.getItem("pf-theme");
      if (t === "light" || t === "dark") setTheme(t);
    } catch {
      // storage unavailable
    }
  }, []);

  const apply = (t: Theme) => {
    setTheme(t);
    const root = document.documentElement;
    if (t === "system") root.removeAttribute("data-theme");
    else root.setAttribute("data-theme", t);
    try {
      if (t === "system") localStorage.removeItem("pf-theme");
      else localStorage.setItem("pf-theme", t);
    } catch {
      // storage unavailable
    }
  };

  return (
    <label className="row small muted theme-toggle">
      <span>Theme</span>
      <select value={theme} onChange={(e) => apply(e.target.value as Theme)} aria-label="Color theme">
        <option value="system">System</option>
        <option value="light">Light</option>
        <option value="dark">Dark</option>
      </select>
    </label>
  );
}
