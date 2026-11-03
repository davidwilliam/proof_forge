import type { Metadata, Viewport } from "next";
import type { ReactNode } from "react";
import { Instrument_Serif, Inter, JetBrains_Mono, Space_Grotesk } from "next/font/google";
import "./globals.css";
import { SiteHeader } from "@/components/SiteHeader";
import { Splash } from "@/components/Splash";
import { splashScript } from "@/components/splash-script";

// The identity kit's four families: Instrument Serif for page headlines, Space Grotesk for the
// wordmark, figures and section titles, Inter for interface and body, JetBrains Mono for Lean,
// hashes and Passport readings.
const headline = Instrument_Serif({ subsets: ["latin"], weight: "400", variable: "--font-headline", display: "swap" });
const display = Space_Grotesk({ subsets: ["latin"], weight: ["500", "600", "700"], variable: "--font-display", display: "swap" });
const sans = Inter({ subsets: ["latin"], variable: "--font-sans", display: "swap" });
const mono = JetBrains_Mono({ subsets: ["latin"], weight: ["400", "500"], variable: "--font-mono", display: "swap" });

export const metadata: Metadata = {
  metadataBase: new URL(process.env.NEXT_PUBLIC_SITE_URL || "https://proofforge.dev"),
  title: "ProofForge",
  description:
    "ProofForge turns Meta's Muse models into provers of financial code. Muse Spark, in the ProofForge harness or in Muse Code with ProofForge as its MCP server, repairs code against locked Lean 4 specifications; ProofForge refutes code that breaks one with a kernel-checked counterexample, accepts a fix only when six kernels check its proof, and records each verdict in a hash-bound Passport anyone can re-run.",
  icons: {
    icon: [
      { url: "/favicon.ico", sizes: "16x16 24x24 32x32 48x48 64x64" },
      { url: "/brand/favicon.svg", type: "image/svg+xml" },
    ],
    apple: "/brand/apple-touch-icon.png",
  },
  manifest: "/brand/site.webmanifest",
};

export const viewport: Viewport = { themeColor: "#05070B" };

// Applies the saved theme before first paint to avoid a flash of the wrong theme.
const themeScript = `try{var t=localStorage.getItem("pf-theme");if(t==="light"||t==="dark")document.documentElement.setAttribute("data-theme",t)}catch(e){}`;

export default function RootLayout({ children }: { children: ReactNode }) {
  return (
    <html lang="en" className={`${headline.variable} ${display.variable} ${sans.variable} ${mono.variable}`} suppressHydrationWarning>
      <head>
        <script dangerouslySetInnerHTML={{ __html: themeScript + splashScript }} />
      </head>
      <body>
        <a className="skip-link" href="#main">
          Skip to content
        </a>
        <SiteHeader />
        {children}
        <Splash />
      </body>
    </html>
  );
}
