import Link from "next/link";
import type { Metadata } from "next";
import { githubFile } from "@/lib/flagships";
import { MEASURED, REQUIREMENTS, TASK, VERSIONS } from "@/lib/swap";
import { shortHash } from "@/lib/format";
import { Status } from "@/components/ui";
import { SwapReplay } from "./SwapReplay";
import "./replay.css";

export const metadata: Metadata = {
  title: "Balancer exploit replay, ProofForge",
  description:
    "Replay the November 2025 Balancer V2 rounding exploit on the deployed swap code, the obvious plus-one hotfix and the repair Muse proved with ProofForge.",
};

export default function BalancerReplayPage() {
  const alone = MEASURED.alone;
  const forge = MEASURED.forge;
  return (
    <main className="page replay">
      <h1>The Balancer V2 rounding exploit, replayed</h1>
      <p className="lead">
        On November 3, 2025, attackers drained Balancer V2 Composable Stable Pools and their forks of more than $120 million (
        <a href="https://www.openzeppelin.com/news/understanding-the-balancer-v2-exploit">OpenZeppelin</a>). A swap for an exact amount out rounded
        that amount down before pricing it, and at balances of a few wei one unit of rounding is a large part of a balance: 17 wei of osETH, worth
        17.988 of the pool&apos;s units, was priced as 17. The obvious fix, adding one unit, stops the drain but overcharges whole amounts and refuses
        valid swaps.
      </p>

      <section aria-labelledby="versions">
        <h2 id="versions">Three versions of the swap code</h2>
        <p className="section-lead">
          Each version is Lean code compiled to the same <code>swap-sidecar</code> executable and checked against the same eight locked requirements
          of <a href={githubFile(`${TASK}/README.md`)}>rw-balancer-upscale</a>. Only the given-out path differs; the lines below are the difference.
        </p>
        <div className="versions">
          {VERSIONS.map((v) => (
            <article key={v.key} className="card version" data-verdict={v.verdict}>
              <h3>
                <span className="swatch" style={{ ["--swatch" as string]: `var(--series-${v.key})` }} aria-hidden="true" />
                {v.name}
              </h3>
              <p className="origin">{v.origin}</p>
              <pre>
                <code>{v.code.join("\n")}</code>
              </pre>
              <p className="finding">
                The check says <Status value={v.verdict} />. {v.finding}
              </p>
              <p className="links">
                <a href={githubFile(v.passport.path)}>Passport {shortHash(v.passport.sha256)}</a>
                {v.counterexamples.map((c) => (
                  <a key={c.path} href={githubFile(c.path)}>
                    {c.label}
                  </a>
                ))}
                <a href={githubFile(v.source)}>source</a>
              </p>
            </article>
          ))}
        </div>
      </section>

      <section aria-labelledby="replay">
        <h2 id="replay">Replay a batch on all three</h2>
        <p className="section-lead">
          Pick a batch and run it. The server runs it through the executable built from each version and reports, after every swap, the amount
          charged and the pool&apos;s value: the invariant of its balances, which for a Composable Stable Pool is the D behind the BPT price. A
          batch with a refused swap reverts as a whole, as Balancer&apos;s <code>batchSwap</code> does.
        </p>
        <SwapReplay />
      </section>

      <section aria-labelledby="measured">
        <h2 id="measured">Muse alone and Muse with ProofForge on this task</h2>
        <div className="measured">
          <div className="card">
            <p>Muse Spark alone verified</p>
            <p className="measured-figure">
              {alone.verified} of {alone.runs} runs
            </p>
            <p className="muted">${alone.usdPerVerified.toFixed(2)} list per verified run</p>
          </div>
          <div className="card">
            <p>Muse with ProofForge and the Muse Wonder planner verified</p>
            <p className="measured-figure">
              {forge.verified} of {forge.runs} runs
            </p>
            <p className="muted">${forge.usdPerVerified.toFixed(2)} list per verified run</p>
          </div>
        </div>
        <p className="measured-note">
          Every run had the same caps: ${MEASURED.capUsd} at list prices and {MEASURED.capHours} hours. The three Muse-alone runs that did not verify
          ended at a cap with code that passes all {MEASURED.failedAloneCases.toLocaleString("en-US")} generated property cases and none of the eight
          requirements proved, so the check reports them <Status value="UNRESOLVED" />, not refuted.{" "}
          <a href={githubFile(MEASURED.source)}>Runs and costs</a>.
        </p>
        <p className="small muted">
          A one-sided Fisher exact test on the verification rate gives p = {MEASURED.fisherP}: the difference in rate is not significant at these
          sample sizes. The difference in cost per verified run is the stronger result.
        </p>
      </section>

      <section aria-labelledby="proves">
        <h2 id="proves">What the Muse repair proves</h2>
        <p className="section-lead">
          For any pool math that meets the contract stated in the specification. The constant-product math is proved to meet it; StableMath is not,
          so the StableMath replays above are tested, not proved.
        </p>
        <ol className="reqs">
          {REQUIREMENTS.map((r) => (
            <li key={r.id}>
              <code>{r.id}</code>
              <span>{r.text}</span>
            </li>
          ))}
        </ol>
      </section>

      <p className="replay-foot">
        The earlier demo, splitting a payout on a buggy and a repaired build, is at <Link href="/app/payout">/app/payout</Link>.
      </p>
    </main>
  );
}
