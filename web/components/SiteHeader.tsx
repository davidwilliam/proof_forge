"use client";

import Link from "next/link";
import { usePathname } from "next/navigation";
import { ThemeToggle } from "./ThemeToggle";

const LINKS = [
  { href: "/", label: "Overview" },
  { href: "/forge", label: "Forge session" },
  { href: "/challenge", label: "Challenge" },
  { href: "/app", label: "Payouts app" },
  { href: "/results", label: "Results" },
];

export function SiteHeader() {
  const path = usePathname();
  return (
    <header className="site-header">
      <Link href="/" className="brand">
        <svg className="brand-mark" viewBox="0 0 32 32" aria-hidden="true">
          <rect width="32" height="32" rx="8" fill="var(--fg)" />
          <path d="M9 16.5l4.5 4.5L23 11.5" fill="none" stroke="var(--bg)" strokeWidth="3.2" strokeLinecap="round" strokeLinejoin="round" />
        </svg>
        ProofForge
      </Link>
      <nav className="site-nav" aria-label="Main">
        {LINKS.map((l) => (
          <Link key={l.href} href={l.href} aria-current={path === l.href ? "page" : undefined}>
            {l.label}
          </Link>
        ))}
      </nav>
      <span className="spacer" />
      <ThemeToggle />
    </header>
  );
}
