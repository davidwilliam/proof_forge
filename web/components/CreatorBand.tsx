import Link from "next/link";
import { HACKATHON } from "@/lib/contribution";
import { Email } from "./Email";
import "./creator-band.css";

export const CREATOR = {
  name: "David William Silva",
  github: "https://github.com/davidwilliam",
  githubUser: "davidwilliam",
} as const;

/** The credit line at the end of the home page: who built ProofForge, with what and when. */
export function CreatorBand() {
  return (
    <aside className="creator-band" aria-label="Who built ProofForge">
      <span className="creator-mark" aria-hidden="true">
        <img className="lockup-primary" src="/brand/proofforge-icon-primary.svg" alt="" width={40} height={40} />
        <img className="lockup-reversed" src="/brand/proofforge-icon-reversed.svg" alt="" width={40} height={40} />
      </span>
      <p className="creator-text">
        ProofForge was built by <strong>{CREATOR.name}</strong> with Meta&apos;s Muse models during the {HACKATHON.event}.
      </p>
      <p className="creator-links">
        <a href={CREATOR.github}>GitHub</a>
        <Email />
        <Link href="/about">About ProofForge</Link>
      </p>
    </aside>
  );
}
