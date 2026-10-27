// TypeScript glue between the payouts form and the Lean payout sidecar.
// This code is TESTED_ONLY (property tests in tests/money.property.test.ts); it is not
// covered by the Lean proofs, which apply only to Payout.step.

import type { PayoutRequestBody, PayoutState } from "./api";

export type Parsed<T> = { ok: true; value: T } | { ok: false; error: string };

/** Largest cent amount accepted: JSON numbers must stay exact integers in JavaScript. */
export const MAX_CENTS = Number.MAX_SAFE_INTEGER;

const DOLLARS = /^(0|[1-9][0-9]*)(?:\.([0-9]{1,2}))?$/;

/**
 * Parse a decimal dollar string to integer cents.
 * Accepted: digits with an optional fraction of one or two digits, for example "1", "1.5",
 * "1.00", "0.07". Surrounding whitespace is ignored. Rejected: empty input, signs
 * (including negatives), more than two decimals, leading zeros such as "01", a bare
 * point (".5", "1."), separators, exponents, and values above MAX_CENTS.
 */
export function parseDollars(input: string): Parsed<number> {
  if (typeof input !== "string") return { ok: false, error: "Enter an amount." };
  const s = input.trim();
  if (s === "") return { ok: false, error: "Enter an amount." };
  if (s.startsWith("-")) return { ok: false, error: "Negative amounts are not allowed." };
  const m = DOLLARS.exec(s);
  if (!m) {
    if (/^[0-9]*\.[0-9]{3,}$/.test(s)) return { ok: false, error: "Use at most two decimal places." };
    return { ok: false, error: "Enter a dollar amount such as 1.00." };
  }
  const whole = BigInt(m[1]!);
  const frac = BigInt((m[2] ?? "").padEnd(2, "0") || "0");
  const cents = whole * 100n + frac;
  if (cents > BigInt(MAX_CENTS)) return { ok: false, error: "Amount is too large." };
  return { ok: true, value: Number(cents) };
}

/** Format integer cents as a dollar string with exactly two decimals, for example 34 -> "0.34". */
export function formatCents(cents: number): string {
  if (!Number.isSafeInteger(cents)) throw new RangeError(`not a safe integer: ${cents}`);
  const neg = cents < 0;
  const abs = BigInt(Math.abs(cents));
  const whole = abs / 100n;
  const frac = (abs % 100n).toString().padStart(2, "0");
  return `${neg ? "-" : ""}${whole.toString()}.${frac}`;
}

/** Parse a positive integer account id (no sign, no leading zeros). */
export function parseAccountId(input: string): Parsed<number> {
  const s = input.trim();
  if (!/^[1-9][0-9]*$/.test(s)) return { ok: false, error: "Account ids are positive integers." };
  const n = Number(s);
  if (!Number.isSafeInteger(n)) return { ok: false, error: "Account id is too large." };
  return { ok: true, value: n };
}

export interface PayoutForm {
  amount: string;
  sourceBalance: string;
  sourceId: string;
  recipientIds: string[];
  txId: number;
}

export interface PayoutInput {
  state: PayoutState;
  request: PayoutRequestBody;
}

/**
 * Build the sidecar input from the form. The source pays, recipients start at zero, the
 * source authorizes itself, and no transactions have been applied yet. Validation here is
 * input hygiene only: business rules (for example amount above balance) are decided by
 * Payout.step, which rejects invalid payouts.
 */
export function buildPayoutInput(form: PayoutForm): Parsed<PayoutInput> {
  const amount = parseDollars(form.amount);
  if (!amount.ok) return { ok: false, error: `Amount: ${amount.error}` };
  const balance = parseDollars(form.sourceBalance);
  if (!balance.ok) return { ok: false, error: `Source balance: ${balance.error}` };
  const source = parseAccountId(form.sourceId);
  if (!source.ok) return { ok: false, error: `Source account: ${source.error}` };
  if (form.recipientIds.length < 3) return { ok: false, error: "Add at least three recipients." };
  const recipients: number[] = [];
  for (const [i, raw] of form.recipientIds.entries()) {
    const r = parseAccountId(raw);
    if (!r.ok) return { ok: false, error: `Recipient ${i + 1}: ${r.error}` };
    if (r.value === source.value) return { ok: false, error: `Recipient ${i + 1} is the source account.` };
    if (recipients.includes(r.value)) return { ok: false, error: `Recipient ${i + 1} is listed twice.` };
    recipients.push(r.value);
  }
  if (!Number.isSafeInteger(form.txId) || form.txId < 0) return { ok: false, error: "Invalid transaction id." };
  return {
    ok: true,
    value: {
      state: {
        balances: [[source.value, balance.value], ...recipients.map((r): [number, number] => [r, 0])],
        auth: [[source.value, source.value]],
        applied: [],
      },
      request: { txId: form.txId, requester: source.value, source: source.value, recipients, amount: amount.value },
    },
  };
}

export interface PayoutSummary {
  outcome: string;
  shares: { account: number; cents: number }[];
  distributed: number;
  sourceDebit: number;
  /** amount minus the cents recipients received; nonzero means money was lost or created. */
  discrepancy: number;
}

/** Compare the sidecar's resulting state with the input state. */
export function summarizeResult(input: PayoutInput, result: { outcome?: string; state?: PayoutState }): Parsed<PayoutSummary> {
  if (!result.outcome || !result.state || !Array.isArray(result.state.balances)) {
    return { ok: false, error: "The sidecar returned no state." };
  }
  const before = new Map(input.state.balances);
  const after = new Map(result.state.balances);
  const shares = input.request.recipients.map((a) => ({ account: a, cents: (after.get(a) ?? 0) - (before.get(a) ?? 0) }));
  const distributed = shares.reduce((acc, s) => acc + s.cents, 0);
  const src = input.request.source;
  const sourceDebit = (before.get(src) ?? 0) - (after.get(src) ?? 0);
  const discrepancy = result.outcome === "ok" ? input.request.amount - distributed : 0;
  return { ok: true, value: { outcome: result.outcome, shares, distributed, sourceDebit, discrepancy } };
}
