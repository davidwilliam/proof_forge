"use client";

import Link from "next/link";
import { usePathname } from "next/navigation";
import { ThemeToggle } from "./ThemeToggle";

const LINKS = [
  { href: "/", label: "Forge session" },
  { href: "/challenge", label: "Challenge" },
  { href: "/app", label: "Payouts app" },
  { href: "/results", label: "Results" },
];

export function SiteHeader() {
  const path = usePathname();
  return (
    <header className="site-header">
      <Link href="/" className="brand">
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
