// Property tests for the TESTED_ONLY TypeScript glue in lib/money.ts.
// The run writes generated/property-tests.json with the number of cases executed;
// the /app/payout page displays that count.

import { afterAll, describe, expect, it } from "vitest";
import fc from "fast-check";
import fs from "node:fs";
import path from "node:path";
import { MAX_CENTS, buildPayoutInput, formatCents, parseAccountId, parseDollars, summarizeResult } from "@/lib/money";

const OUT = path.resolve(import.meta.dirname, "../generated/property-tests.json");
const results: { name: string; cases: number; passed: boolean }[] = [];

/** Run one property, counting every case the predicate is evaluated on. */
function property<Ts extends [unknown, ...unknown[]]>(
  name: string,
  runs: number,
  arbs: { [K in keyof Ts]: fc.Arbitrary<Ts[K]> },
  pred: (...args: Ts) => boolean | void,
) {
  it(name, () => {
    const entry = { name, cases: 0, passed: false };
    results.push(entry);
    const p = fc.property(...(arbs as unknown as [fc.Arbitrary<unknown>]), ((...args: Ts) => {
      entry.cases += 1;
      return pred(...args);
    }) as unknown as (a: unknown) => boolean | void);
    fc.assert(p, { numRuns: runs, seed: 20261027 });
    entry.passed = true;
  });
}

const cents = fc.integer({ min: 0, max: MAX_CENTS });
const smallCents = fc.integer({ min: 0, max: 10_000_000 });
const digits = (min: number, max: number) => fc.string({ unit: fc.constantFrom(..."0123456789"), minLength: min, maxLength: max });
const wholePart = fc.oneof(fc.constant("0"), fc.tuple(fc.constantFrom(..."123456789"), digits(0, 12)).map(([a, b]) => a + b));

describe("parseDollars and formatCents", () => {
  property("format then parse is the identity on cents", 2000, [cents], (c) => {
    const p = parseDollars(formatCents(c));
    return p.ok && p.value === c;
  });

  property("parse matches whole * 100 + fraction for one or two decimals", 2000, [wholePart, digits(0, 2)], (w, f) => {
    const s = f === "" ? w : `${w}.${f}`;
    const p = parseDollars(s);
    const expected = BigInt(w) * 100n + BigInt(f.padEnd(2, "0") || "0");
    if (expected > BigInt(MAX_CENTS)) return !p.ok;
    return p.ok && BigInt(p.value) === expected;
  });

  property("parse then format gives the canonical two-decimal form", 1000, [wholePart, digits(1, 2)], (w, f) => {
    const p = parseDollars(`${w}.${f}`);
    if (!p.ok) return BigInt(w) * 100n > BigInt(MAX_CENTS);
    return formatCents(p.value) === `${w}.${f.padEnd(2, "0")}`;
  });

  property("rejects more than two decimal places", 1000, [wholePart, digits(3, 8)], (w, f) => !parseDollars(`${w}.${f}`).ok);

  property("rejects negative amounts", 1000, [cents], (c) => {
    const p = parseDollars(`-${formatCents(c)}`);
    return !p.ok && /negative/i.test(p.error);
  });

  property(
    "rejects any string containing a character outside digits, point and outer whitespace",
    1500,
    [fc.string({ maxLength: 12 }), fc.string({ minLength: 1, maxLength: 3 }).filter((s) => /[^0-9.\s]/.test(s)), fc.string({ maxLength: 12 })],
    (a, bad, b) => !parseDollars(a + bad + b).ok,
  );

  property("every accepted string is a strict decimal with at most two fraction digits", 1500, [fc.string({ maxLength: 10 })], (s) => {
    const p = parseDollars(s);
    if (!p.ok) return true;
    return /^(0|[1-9][0-9]*)(\.[0-9]{1,2})?$/.test(s.trim()) && Number.isSafeInteger(p.value) && p.value >= 0;
  });

  property("rejects leading zeros and bare points", 500, [digits(1, 6)], (d) => {
    return !parseDollars(`0${d}`).ok && !parseDollars(`.${d.slice(0, 2)}`).ok && !parseDollars(`${d}.`).ok;
  });

  property("parsing preserves order", 1000, [smallCents, smallCents], (a, b) => {
    const pa = parseDollars(formatCents(a));
    const pb = parseDollars(formatCents(b));
    return pa.ok && pb.ok && Math.sign(pa.value - pb.value) === Math.sign(a - b);
  });

  property("formatCents of negatives mirrors positives", 500, [fc.integer({ min: 1, max: MAX_CENTS })], (c) => formatCents(-c) === `-${formatCents(c)}`);

  it("handles fixed examples", () => {
    expect(parseDollars("1.00")).toEqual({ ok: true, value: 100 });
    expect(parseDollars("0.07")).toEqual({ ok: true, value: 7 });
    expect(parseDollars(" 12.5 ")).toEqual({ ok: true, value: 1250 });
    for (const bad of ["", "-1", "1.001", "abc", "1e2", "1,000", "+1", "01", ".5", "1.", "NaN", "Infinity", "0x10"]) {
      expect(parseDollars(bad).ok).toBe(false);
    }
    expect(formatCents(34)).toBe("0.34");
    expect(formatCents(100)).toBe("1.00");
    expect(() => formatCents(0.5)).toThrow();
  });
});

describe("account ids and payout input", () => {
  property("parseAccountId accepts exactly the positive integers", 1000, [fc.integer({ min: -1000, max: 1_000_000 })], (n) => {
    const p = parseAccountId(String(n));
    return n >= 1 ? p.ok && p.value === n : !p.ok;
  });

  const ids = fc.uniqueArray(fc.integer({ min: 2, max: 9999 }), { minLength: 3, maxLength: 8 });

  property("buildPayoutInput maps the form to the sidecar format", 1000, [smallCents, smallCents, ids], (amt, bal, rec) => {
    const r = buildPayoutInput({ amount: formatCents(amt), sourceBalance: formatCents(bal), sourceId: "1", recipientIds: rec.map(String), txId: 7 });
    if (!r.ok) return false;
    const { state, request } = r.value;
    return (
      request.amount === amt &&
      request.source === 1 &&
      request.requester === 1 &&
      JSON.stringify(request.recipients) === JSON.stringify(rec) &&
      state.balances.length === rec.length + 1 &&
      state.balances[0]![0] === 1 &&
      state.balances[0]![1] === bal &&
      state.balances.slice(1).every(([a, b], i) => a === rec[i] && b === 0) &&
      state.applied.length === 0 &&
      JSON.stringify(state.auth) === "[[1,1]]"
    );
  });

  property("buildPayoutInput rejects duplicate recipients, the source as recipient, and fewer than three", 1000, [ids, fc.nat({ max: 7 })], (rec, k) => {
    const i = k % rec.length;
    const dup = [...rec, String(rec[i])];
    const withSource = [...rec.map(String), "1"];
    const short = rec.slice(0, 2).map(String);
    const base = { amount: "1.00", sourceBalance: "10.00", sourceId: "1", txId: 7 };
    return (
      !buildPayoutInput({ ...base, recipientIds: dup.map(String) }).ok &&
      !buildPayoutInput({ ...base, recipientIds: withSource }).ok &&
      !buildPayoutInput({ ...base, recipientIds: short }).ok
    );
  });

  property(
    "summarizeResult reports shares, total and discrepancy for any resulting state",
    1000,
    [smallCents, ids, fc.array(fc.integer({ min: 0, max: 100000 }), { minLength: 8, maxLength: 8 })],
    (amt, rec, got) => {
      const r = buildPayoutInput({ amount: formatCents(amt), sourceBalance: formatCents(amt), sourceId: "1", recipientIds: rec.map(String), txId: 7 });
      if (!r.ok) return false;
      const after: [number, number][] = [[1, 0], ...rec.map((a, i): [number, number] => [a, got[i]!])];
      const s = summarizeResult(r.value, { outcome: "ok", state: { balances: after, auth: [[1, 1]], applied: [7] } });
      if (!s.ok) return false;
      const total = rec.reduce((acc, _, i) => acc + got[i]!, 0);
      return s.value.distributed === total && s.value.discrepancy === amt - total && s.value.sourceDebit === amt && s.value.shares.every((x, i) => x.cents === got[i]);
    },
  );

  it("summarizes the flagship example for both builds", () => {
    const r = buildPayoutInput({ amount: "1.00", sourceBalance: "10.00", sourceId: "1", recipientIds: ["2", "3", "4"], txId: 7 });
    expect(r.ok).toBe(true);
    if (!r.ok) return;
    const buggy = summarizeResult(r.value, { outcome: "ok", state: { balances: [[1, 900], [2, 33], [3, 33], [4, 33]], auth: [[1, 1]], applied: [7] } });
    const fixed = summarizeResult(r.value, { outcome: "ok", state: { balances: [[1, 900], [2, 34], [3, 33], [4, 33]], auth: [[1, 1]], applied: [7] } });
    expect(buggy.ok && buggy.value.discrepancy).toBe(1);
    expect(fixed.ok && fixed.value.discrepancy).toBe(0);
    expect(summarizeResult(r.value, {}).ok).toBe(false);
  });
});

afterAll(() => {
  const cases = results.reduce((a, r) => a + r.cases, 0);
  const out = {
    suite: "tests/money.property.test.ts",
    library: "fast-check",
    properties: results.length,
    cases,
    failed: results.filter((r) => !r.passed).map((r) => r.name),
    generated: new Date().toISOString(),
    detail: results,
  };
  fs.mkdirSync(path.dirname(OUT), { recursive: true });
  fs.writeFileSync(OUT, JSON.stringify(out, null, 2) + "\n");
});
