import Link from "next/link";
import type { Metadata } from "next";
import { readPropertyTests, readRepairedPassport } from "@/lib/generated";
import { formatInt, shortHash } from "@/lib/format";
import { Status } from "@/components/ui";
import { PayoutForm } from "./PayoutForm";

export const dynamic = "force-dynamic";
export const metadata: Metadata = { title: "Split a payout, ProofForge" };

// The payout demo that /app showed before the Balancer replay; linked from the bottom of /app.

export default function PayoutsPage() {
  const tests = readPropertyTests();
  const passport = readRepairedPassport();
  return (
    <main className="page">
      <h1>Split a payout</h1>
      <p className="lead">
        Enter an amount in dollars and three or more recipients, then run the same request on the buggy build and on the verified repair. Both
        builds are the Lean payout component compiled to the <code>payout-sidecar</code> executable.
      </p>

      <section className="boundary" aria-label="Evidence boundary">
        <div className="card">
          <h2>Lean component: Payout.step</h2>
          <p>
            Status for the repaired build: {passport ? <Status value={passport.status} /> : <Status value="pending">no Passport recorded</Status>}.
            Its requirements are proved in Lean for all inputs and checked by Comparator.
          </p>
          {passport ? (
            <p>
              <Link href={`/passport/${passport.passport_sha256}`}>Open the Passport {shortHash(passport.passport_sha256)}</Link> for{" "}
              <code>{passport.solution_file}</code> (sha256 <span className="hash">{shortHash(passport.solution_sha256, 16)}</span>).
            </p>
          ) : (
            <p className="small muted">
              Run <code>pnpm passport:repaired</code> with the API running to create and record the Passport for the repaired build.
            </p>
          )}
        </div>
        <div className="card">
          <h2>TypeScript glue on this page</h2>
          <p>
            Status: <Status value="TESTED_ONLY" />. Dollar parsing, cent formatting, request building and result summaries are not proved.
          </p>
          {tests ? (
            <p>
              {formatInt(tests.cases)} property-test cases across {tests.properties} properties with {tests.library}
              {tests.failed.length ? (
                <>
                  , <Status value="FAILED">{tests.failed.length} failing</Status>
                </>
              ) : (
                ", all passing"
              )}
              . Last run {tests.generated}.
            </p>
          ) : (
            <p className="small muted">
              No property-test run recorded. Run <code>pnpm test</code> to generate the count.
            </p>
          )}
          <p className="small muted">The JSON wrapper inside the executable (app/Main.lean) is also TESTED_ONLY.</p>
        </div>
      </section>

      <PayoutForm passportSolutionSha={passport?.solution_sha256 ?? null} />
    </main>
  );
}
