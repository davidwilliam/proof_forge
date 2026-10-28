"use client";

import { useState } from "react";
import { postJson, type PayoutResponse } from "@/lib/api";
import { buildPayoutInput, formatCents, parseAccountId, parseDollars, summarizeResult, type PayoutInput, type PayoutSummary } from "@/lib/money";
import { formatMs, shortHash } from "@/lib/format";
import { ErrorBox, Status } from "@/components/ui";

type Build = "buggy" | "repaired";

interface RunResult {
  input: PayoutInput;
  response: PayoutResponse;
  summary: PayoutSummary | null;
  error: string | null;
}

export function PayoutForm({ passportSolutionSha }: { passportSolutionSha: string | null }) {
  const [amount, setAmount] = useState("1.00");
  const [balance, setBalance] = useState("10.00");
  const [recipients, setRecipients] = useState(["2", "3", "4"]);
  const [busy, setBusy] = useState<Build | null>(null);
  const [runs, setRuns] = useState<Partial<Record<Build, RunResult>>>({});
  const [error, setError] = useState<string | null>(null);
  const [txId, setTxId] = useState(7);

  const amountCheck = parseDollars(amount);
  const balanceCheck = parseDollars(balance);
  const built = buildPayoutInput({ amount, sourceBalance: balance, sourceId: "1", recipientIds: recipients, txId });

  const run = async (build: Build) => {
    if (!built.ok) return;
    setBusy(build);
    setError(null);
    try {
      const response = await postJson<PayoutResponse>("/api/payout", { build, state: built.value.state, request: built.value.request });
      const s = summarizeResult(built.value, response.result);
      setRuns((r) => ({ ...r, [build]: { input: built.value, response, summary: s.ok ? s.value : null, error: s.ok ? null : s.error } }));
      setTxId((t) => t + 1);
    } catch (e) {
      setError(`${build} build: ${(e as Error).message}`);
    } finally {
      setBusy(null);
    }
  };

  return (
    <section>
      <h2>Payout request</h2>
      <div className="form-grid">
        <label htmlFor="amount">Amount (dollars)</label>
        <div>
          <input
            id="amount"
            inputMode="decimal"
            value={amount}
            onChange={(e) => setAmount(e.target.value)}
            aria-invalid={!amountCheck.ok}
            aria-describedby="amount-msg"
            style={{ width: "100%" }}
          />
          <div id="amount-msg" className="small" style={{ color: amountCheck.ok ? "var(--muted)" : "var(--bad)" }}>
            {amountCheck.ok ? `${amountCheck.value} cents` : amountCheck.error}
          </div>
        </div>
        <label htmlFor="balance">Source balance (dollars)</label>
        <div>
          <input
            id="balance"
            inputMode="decimal"
            value={balance}
            onChange={(e) => setBalance(e.target.value)}
            aria-invalid={!balanceCheck.ok}
            aria-describedby="balance-msg"
            style={{ width: "100%" }}
          />
          <div id="balance-msg" className="small" style={{ color: balanceCheck.ok ? "var(--muted)" : "var(--bad)" }}>
            {balanceCheck.ok ? `${balanceCheck.value} cents in source account 1` : balanceCheck.error}
          </div>
        </div>
        <span>Recipients (account ids)</span>
        <div className="stack">
          {recipients.map((r, i) => {
            const ok = parseAccountId(r).ok;
            return (
              <div className="row" key={i}>
                <input
                  aria-label={`Recipient ${i + 1} account id`}
                  value={r}
                  inputMode="numeric"
                  onChange={(e) => setRecipients((xs) => xs.map((x, j) => (j === i ? e.target.value : x)))}
                  aria-invalid={!ok}
                  style={{ width: 110 }}
                />
                <button onClick={() => setRecipients((xs) => xs.filter((_, j) => j !== i))} disabled={recipients.length <= 3} aria-label={`Remove recipient ${i + 1}`}>
                  Remove
                </button>
              </div>
            );
          })}
          <button
            onClick={() =>
              setRecipients((xs) => {
                const used = new Set(xs.map(Number));
                let next = 2;
                while (used.has(next)) next++;
                return [...xs, String(next)];
              })
            }
            disabled={recipients.length >= 12}
          >
            Add recipient
          </button>
        </div>
      </div>
      {!built.ok ? (
        <p style={{ color: "var(--bad)" }} role="status">
          {built.error}
        </p>
      ) : null}
      <div className="row" style={{ margin: "16px 0" }}>
        <button onClick={() => run("buggy")} disabled={!built.ok || busy !== null}>
          {busy === "buggy" ? "Running on buggy build" : "Run on buggy build"}
        </button>
        <button className="primary" onClick={() => run("repaired")} disabled={!built.ok || busy !== null}>
          {busy === "repaired" ? "Running on repaired build" : "Run on repaired build"}
        </button>
        <span className="small muted">The first run of each build compiles it, which can take a minute.</span>
      </div>
      {error ? <ErrorBox title="Payout request failed" message={error} /> : null}

      <div className="split-results">
        {(["buggy", "repaired"] as const).map((b) => (
          <ResultCard key={b} build={b} run={runs[b]} passportSolutionSha={b === "repaired" ? passportSolutionSha : null} />
        ))}
      </div>
    </section>
  );
}

function ResultCard({ build, run, passportSolutionSha }: { build: Build; run: RunResult | undefined; passportSolutionSha: string | null }) {
  const title = build === "buggy" ? "Buggy build" : "Repaired build";
  if (!run) {
    return (
      <div className="card">
        <h3>{title}</h3>
        <p className="muted">Not run yet.</p>
      </div>
    );
  }
  const { summary, response, input } = run;
  const match = passportSolutionSha ? passportSolutionSha === response.solution_sha256 : null;
  return (
    <div className="card">
      <h3>{title}</h3>
      {run.error || !summary ? (
        <p style={{ color: "var(--bad)" }}>{run.error ?? "No result"}</p>
      ) : (
        <>
          <p>
            Outcome <Status value={summary.outcome === "ok" ? "OK" : "REJECTED"}>{summary.outcome}</Status> for {formatCents(input.request.amount)} dollars (
            {input.request.amount} cents)
          </p>
          <div className="table-scroll">
            <table>
              <thead>
                <tr>
                  <th>Recipient</th>
                  <th className="num">Received (cents)</th>
                  <th className="num">Dollars</th>
                </tr>
              </thead>
              <tbody>
                {summary.shares.map((s) => (
                  <tr key={s.account}>
                    <td className="mono">account {s.account}</td>
                    <td className="num mono">{s.cents}</td>
                    <td className="num mono">{formatCents(s.cents)}</td>
                  </tr>
                ))}
                <tr>
                  <th>Total received</th>
                  <th className="num mono">{summary.distributed}</th>
                  <th className="num mono">{formatCents(summary.distributed)}</th>
                </tr>
              </tbody>
            </table>
          </div>
          <p className="big-total" style={{ marginTop: 10 }}>
            {summary.shares.map((s) => s.cents).join(" + ")} = {summary.distributed}
          </p>
          {summary.outcome === "ok" ? (
            summary.discrepancy === 0 ? (
              <p>
                <Status value="OK">conserved</Status> Every cent of the {input.request.amount} is accounted for; the source was debited {summary.sourceDebit}.
              </p>
            ) : (
              <p>
                <Status value="REFUTED">{summary.discrepancy > 0 ? `${summary.discrepancy} cents lost` : `${-summary.discrepancy} cents created`}</Status> The
                source was debited {summary.sourceDebit} cents but recipients received {summary.distributed}.
              </p>
            )
          ) : (
            <p className="muted">The component rejected the request and left the state unchanged.</p>
          )}
        </>
      )}
      <dl className="kv small" style={{ marginTop: 8 }}>
        <dt>Solution sha256</dt>
        <dd className="hash">{shortHash(response.solution_sha256, 16)}</dd>
        <dt>Executable sha256</dt>
        <dd className="hash">{shortHash(response.executable_sha256, 16)}</dd>
        <dt>Run time</dt>
        <dd>{formatMs(response.elapsed_ms)}</dd>
        {match != null ? (
          <>
            <dt>Passport match</dt>
            <dd>{match ? "solution hash matches the Passport" : "solution hash differs from the recorded Passport"}</dd>
          </>
        ) : null}
      </dl>
    </div>
  );
}
