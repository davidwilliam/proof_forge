"use client";

import Link from "next/link";
import { usePathname } from "next/navigation";
import { useCallback, useEffect, useId, useRef, useState, type KeyboardEvent } from "react";
import { ThemeToggle } from "./ThemeToggle";
import "./site-header.css";

const LINKS = [
  { href: "/", label: "Overview" },
  { href: "/frontier", label: "Frontier" },
  { href: "/forge", label: "Forge session" },
  { href: "/challenge", label: "Challenge" },
  { href: "/app", label: "Balancer replay" },
  { href: "/results", label: "Results" },
];

interface Resource {
  href: string;
  label: string;
  text: string;
  /** A full page load: static files, and the home page with ?splash, whose head script decides before first paint. */
  plain?: boolean;
}

const RESOURCES: { group: string; items: Resource[] }[] = [
  {
    group: "Check and reuse",
    items: [
      { href: "/verify", label: "Verify a Passport yourself", text: "The commands that rerun every check and compare each hash and status." },
      { href: "/methods", label: "Preregistrations and methods", text: "Every experiment's plan, committed before its runs, with its result." },
      { href: "/brand", label: "Brand kit", text: "The mark, lockups, palette and type, with downloads." },
      { href: "/?splash", label: "Replay the splash screen", text: "The identity sequence over the home page.", plain: true },
    ],
  },
  {
    group: "For agents",
    items: [
      { href: "/llms.txt", label: "llms.txt", text: "Every claim, figure, Passport hash, source file and command on the site, as plain text.", plain: true },
      { href: "/evidence.json", label: "evidence.json", text: "The same evidence as JSON: incidents, comparisons, Passports and reproduction commands.", plain: true },
    ],
  },
];

const RESOURCE_PATHS = ["/verify", "/methods", "/brand"];

/** The kit's horizontal lockup, primary on light grounds and reversed on dark ones; never recomposed. */
export function Lockup({ className = "" }: { className?: string }) {
  return (
    <span className={`lockup ${className}`.trim()} role="img" aria-label="ProofForge">
      <img className="lockup-primary" src="/brand/proofforge-horizontal-primary.svg" alt="" width={624} height={106} />
      <img className="lockup-reversed" src="/brand/proofforge-horizontal-reversed.svg" alt="" width={624} height={106} />
    </span>
  );
}

/** A disclosure: a button that shows and hides a list of links. Escape closes it and returns focus to the button. */
function ResourcesMenu({ path }: { path: string }) {
  const [open, setOpen] = useState(false);
  const wrap = useRef<HTMLDivElement>(null);
  const button = useRef<HTMLButtonElement>(null);
  const panelId = useId();

  const close = useCallback((refocus: boolean) => {
    setOpen(false);
    if (refocus) button.current?.focus();
  }, []);

  // Close on navigation.
  useEffect(() => setOpen(false), [path]);

  useEffect(() => {
    if (!open) return;
    const onPointer = (e: PointerEvent) => {
      if (wrap.current && !wrap.current.contains(e.target as Node)) close(false);
    };
    const onKey = (e: globalThis.KeyboardEvent) => {
      if (e.key === "Escape") {
        e.preventDefault();
        close(true);
      }
    };
    document.addEventListener("pointerdown", onPointer);
    document.addEventListener("keydown", onKey);
    return () => {
      document.removeEventListener("pointerdown", onPointer);
      document.removeEventListener("keydown", onKey);
    };
  }, [open, close]);

  const links = () => Array.from(wrap.current?.querySelectorAll<HTMLAnchorElement>(".res-panel a") ?? []);

  // Arrow keys move between the links; Tab works as everywhere else.
  const onPanelKey = (e: KeyboardEvent<HTMLDivElement>) => {
    const ls = links();
    const i = ls.indexOf(document.activeElement as HTMLAnchorElement);
    let next = -1;
    if (e.key === "ArrowDown") next = i < 0 ? 0 : (i + 1) % ls.length;
    else if (e.key === "ArrowUp") next = i <= 0 ? ls.length - 1 : i - 1;
    else if (e.key === "Home") next = 0;
    else if (e.key === "End") next = ls.length - 1;
    if (next >= 0) {
      e.preventDefault();
      ls[next]?.focus();
    }
  };

  const onButtonKey = (e: KeyboardEvent<HTMLButtonElement>) => {
    if (e.key === "ArrowDown") {
      e.preventDefault();
      setOpen(true);
      requestAnimationFrame(() => links()[0]?.focus());
    }
  };

  const current = RESOURCE_PATHS.includes(path);
  return (
    <div
      className="res"
      ref={wrap}
      onBlur={(e) => {
        if (open && wrap.current && e.relatedTarget && !wrap.current.contains(e.relatedTarget as Node)) setOpen(false);
      }}
    >
      <button
        ref={button}
        type="button"
        className="res-button"
        aria-expanded={open}
        aria-controls={panelId}
        data-current={current ? "true" : undefined}
        onClick={() => setOpen((o) => !o)}
        onKeyDown={onButtonKey}
      >
        Resources
        <svg className="res-chevron" width="10" height="10" viewBox="0 0 10 10" aria-hidden="true">
          <path d="M1.5 3.5 5 7l3.5-3.5" fill="none" stroke="currentColor" strokeWidth="1.6" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
      </button>
      <div className="res-panel" id={panelId} hidden={!open} onKeyDown={onPanelKey}>
        {RESOURCES.map((g) => (
          <div className="res-group" key={g.group}>
            <p className="res-group-label" id={`${panelId}-${g.group.replace(/\W+/g, "-")}`}>
              {g.group}
            </p>
            <ul aria-labelledby={`${panelId}-${g.group.replace(/\W+/g, "-")}`}>
              {g.items.map((r) => {
                const body = (
                  <>
                    <span className="res-label">{r.label}</span>
                    <span className="res-text">{r.text}</span>
                  </>
                );
                return (
                  <li key={r.href}>
                    {r.plain ? (
                      <a href={r.href} onClick={() => setOpen(false)}>
                        {body}
                      </a>
                    ) : (
                      <Link href={r.href} aria-current={path === r.href ? "page" : undefined} onClick={() => setOpen(false)}>
                        {body}
                      </Link>
                    )}
                  </li>
                );
              })}
            </ul>
          </div>
        ))}
      </div>
    </div>
  );
}

export function SiteHeader() {
  const path = usePathname();
  // The home page opens on the Void hero band, so its header is dark in both themes.
  return (
    <header className="site-header" data-tone={path === "/" ? "dark" : undefined}>
      <Link href="/" className="brand" aria-label="ProofForge, overview">
        <Lockup />
      </Link>
      <nav className="site-nav" aria-label="Main">
        {LINKS.map((l) => (
          <Link key={l.href} href={l.href} aria-current={path === l.href ? "page" : undefined}>
            {l.label}
          </Link>
        ))}
        <ResourcesMenu path={path} />
        <Link href="/about" className="nav-about" aria-current={path === "/about" ? "page" : undefined}>
          About
        </Link>
      </nav>
      <ThemeToggle />
    </header>
  );
}
