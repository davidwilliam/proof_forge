"use client";

import { useEffect, useRef, useState } from "react";
import { postJson, type ChallengeResult } from "@/lib/api";
import { formatMs, prettyJson, shortHash } from "@/lib/format";
import { Code, ErrorBox, Status } from "@/components/ui";

const TARGET_MS = 20000;

export function ChallengeRunner({ variants, requirementTexts }: { variants: string[]; requirementTexts: Record<string, string> }) {
  const [variant, setVariant] = useState(variants[0] ?? "");
  const [busy, setBusy] = useState(false);
  const [result, setResult] = useState<ChallengeResult | null>(null);
  const [roundTrip, setRoundTrip] = useState<number | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [tick, setTick] = useState(0);
  const t0 = useRef(0);

  useEffect(() => {
    if (!busy) return;
    const t = setInterval(() => setTick(performance.now() - t0.current), 100);
    return () => clearInterval(t);
  }, [busy]);

  const run = async () => {
    setBusy(true);
    setError(null);
    setResult(null);
    setRoundTrip(null);
    t0.current = performance.now();
    setTick(0);
    try {
      // repair stays false: this page only runs the binary check, never a model session.
      const r = await postJson<ChallengeResult>("/api/challenge", { variant, repair: false });
      setRoundTrip(performance.now() - t0.current);
      setResult(r);
    } catch (e) {
      setError((e as Error).message);
    } finally {
      setBusy(false);
    }
  };

  if (!variants.length) return <div className="notice">No hidden variants are available on this server.</div>;

  const w = result?.witness ?? null;
  const elapsed = result?.elapsed_ms ?? null;
  const within = elapsed != null ? elapsed <= TARGET_MS : null;
  const violations = Object.entries(result?.violations ?? {}).filter(([, n]) => n > 0);

  return (
    <div className="stack">
      <div className="panel row">
        <label className="row">
          Variant
          <select value={variant} onChange={(e) => setVariant(e.target.value)} disabled={busy}>
            {variants.map((v) => (
              <option key={v} value={v}>
                {v}
              </option>
            ))}
          </select>
        </label>
        <button className="primary" onClick={run} disabled={busy || !variant}>
          {busy ? "Checking" : "Run check"}
        </button>
        {busy ? <span className="mono">{(tick / 1000).toFixed(1)} s of 20 s target</span> : null}
      </div>

      {error ? <ErrorBox title="Challenge failed" message={error} /> : null}

      {result ? (
        <>
          <div className="card">
            <p style={{ fontSize: "1.2rem", margin: 0 }}>
              {result.label}: variant <span className="mono">{result.variant}</span> is <Status value={result.status} />
            </p>
            <dl className="kv" style={{ marginTop: 8 }}>
              <dt>Check time</dt>
              <dd>
                {formatMs(elapsed)} against the 20 s target:{" "}
                {within ? <Status value="PASS">within target</Status> : <Status value="UNRESOLVED">over target</Status>}
              </dd>
              {roundTrip != null ? (
                <>
                  <dt>Round trip</dt>
                  <dd>{formatMs(roundTrip)} including the request</dd>
                </>
              ) : null}
              <dt>Executable sha256</dt>
              <dd className="hash">{shortHash(result.executable_sha256, 16)}</dd>
              <dt>Violations</dt>
              <dd>{violations.length ? violations.map(([k, n]) => `${k} in ${n} cases`).join(", ") : "none found"}</dd>
            </dl>
          </div>

          {w ? (
            <div className="card">
              <h2>
                Violated requirement <span className="mono">{w.requirement}</span>
              </h2>
              <p>{requirementTexts[w.requirement] || "No requirement text available."}</p>
              <p>
                Witness: <strong>{w.message}</strong>
              </p>
              <div className="split-results">
                <div>
                  <h3>Input</h3>
                  <Code text={prettyJson(w.input)} />
                </div>
                <div>
                  <h3>Output of the variant&apos;s executable</h3>
                  <Code text={prettyJson(w.output)} />
                </div>
              </div>
            </div>
          ) : (
            <div className="notice">
              No witness was found in this run, so the variant is UNRESOLVED: the tests did not refute it, and nothing has been proved about it.
            </div>
          )}
        </>
      ) : null}
    </div>
  );
}
