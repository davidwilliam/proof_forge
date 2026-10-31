"use client";

import Link from "next/link";
import { usePathname } from "next/navigation";
import { ThemeToggle } from "./ThemeToggle";

const LINKS = [
  { href: "/", label: "Overview" },
  { href: "/forge", label: "Forge session" },
  { href: "/challenge", label: "Challenge" },
  { href: "/app", label: "Balancer replay" },
  { href: "/results", label: "Results" },
];

/** The kit's horizontal lockup, primary on light grounds and reversed on dark ones; never recomposed. */
export function Lockup({ className = "" }: { className?: string }) {
  return (
    <span className={`lockup ${className}`.trim()} role="img" aria-label="ProofForge">
      <img className="lockup-primary" src="/brand/proofforge-horizontal-primary.svg" alt="" width={624} height={106} />
      <img className="lockup-reversed" src="/brand/proofforge-horizontal-reversed.svg" alt="" width={624} height={106} />
    </span>
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
      </nav>
      <span className="spacer" />
      <ThemeToggle />
    </header>
  );
}
