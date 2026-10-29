// Reads committed result files for the home page figures. Used by scripts/evidence.mjs
// (which writes public/evidence.json and public/llms.txt) and by tests/flagships.test.ts.
//
// Result JSON is written by Python and holds integers far beyond 2^53 (Cetus sqrt prices,
// Euler balances in wei), so it is parsed losslessly: integers outside the safe range become
// bigint. A Passport's sha256 is recomputed exactly as harness/passport.py content_hash does:
// json.dumps(body, sort_keys=True) with Python's default separators and ASCII escaping, over
// the Passport without its passport_sha256 field.

import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";

const here = path.dirname(new URL(import.meta.url).pathname);
/** Repository root (web/scripts/lib -> ../../..). */
export const ROOT = path.resolve(here, "../../..");

/** A number kept with its source text, so it can be written back exactly. */
class Num {
  constructor(raw) {
    this.raw = raw;
  }
}

function parseRaw(text) {
  let i = 0;
  const ws = () => {
    while (i < text.length && " \t\n\r".includes(text[i])) i++;
  };
  const value = () => {
    ws();
    const c = text[i];
    if (c === "{") {
      i++;
      const out = new Map();
      ws();
      if (text[i] === "}") return i++, out;
      for (;;) {
        ws();
        const k = string();
        ws();
        if (text[i++] !== ":") throw new Error(`expected : at ${i}`);
        out.set(k, value());
        ws();
        const d = text[i++];
        if (d === "}") return out;
        if (d !== ",") throw new Error(`expected , or } at ${i}`);
      }
    }
    if (c === "[") {
      i++;
      const out = [];
      ws();
      if (text[i] === "]") return i++, out;
      for (;;) {
        out.push(value());
        ws();
        const d = text[i++];
        if (d === "]") return out;
        if (d !== ",") throw new Error(`expected , or ] at ${i}`);
      }
    }
    if (c === '"') return string();
    if (text.startsWith("true", i)) return (i += 4), true;
    if (text.startsWith("false", i)) return (i += 5), false;
    if (text.startsWith("null", i)) return (i += 4), null;
    const m = /^-?(?:0|[1-9]\d*)(?:\.\d+)?(?:[eE][+-]?\d+)?/.exec(text.slice(i, i + 400));
    if (!m) throw new Error(`unexpected input at ${i}`);
    i += m[0].length;
    return new Num(m[0]);
  };
  const string = () => {
    if (text[i] !== '"') throw new Error(`expected string at ${i}`);
    const start = i;
    i++;
    while (text[i] !== '"') i += text[i] === "\\" ? 2 : 1;
    i++;
    return JSON.parse(text.slice(start, i));
  };
  const v = value();
  ws();
  if (i !== text.length) throw new Error(`trailing input at ${i}`);
  return v;
}

function toPlain(v) {
  if (v instanceof Num) {
    if (/^-?\d+$/.test(v.raw)) {
      const b = BigInt(v.raw);
      return b >= BigInt(Number.MIN_SAFE_INTEGER) && b <= BigInt(Number.MAX_SAFE_INTEGER) ? Number(b) : b;
    }
    return Number(v.raw);
  }
  if (Array.isArray(v)) return v.map(toPlain);
  if (v instanceof Map) return Object.fromEntries([...v].map(([k, x]) => [k, toPlain(x)]));
  return v;
}

function pyString(s) {
  let out = '"';
  for (const ch of s) {
    const cp = ch.codePointAt(0);
    if (ch === '"') out += '\\"';
    else if (ch === "\\") out += "\\\\";
    else if (ch === "\n") out += "\\n";
    else if (ch === "\r") out += "\\r";
    else if (ch === "\t") out += "\\t";
    else if (ch === "\b") out += "\\b";
    else if (ch === "\f") out += "\\f";
    else if (cp >= 0x20 && cp <= 0x7e) out += ch;
    else {
      // Python escapes outside printable ASCII as \uXXXX, astral code points as a surrogate pair.
      for (let k = 0; k < ch.length; k++) out += "\\u" + ch.charCodeAt(k).toString(16).padStart(4, "0");
    }
  }
  return out + '"';
}

/** Python's json.dumps(v, sort_keys=True) over a raw parse tree. */
function pyDumps(v) {
  if (v === null) return "null";
  if (v === true) return "true";
  if (v === false) return "false";
  if (v instanceof Num) return v.raw;
  if (typeof v === "string") return pyString(v);
  if (Array.isArray(v)) return "[" + v.map(pyDumps).join(", ") + "]";
  const keys = [...v.keys()].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
  return "{" + keys.map((k) => `${pyString(k)}: ${pyDumps(v.get(k))}`).join(", ") + "}";
}

const abs = (rel) => path.join(ROOT, rel);

/** Parse a JSON file under the repository root; integers beyond 2^53 become bigint. */
export function readExact(rel) {
  return toPlain(parseRaw(fs.readFileSync(abs(rel), "utf8")));
}

/** sha256 of a file's bytes. */
export function fileSha256(rel) {
  return createHash("sha256").update(fs.readFileSync(abs(rel))).digest("hex");
}

/** The Passport at `rel`, with its content hash recomputed as harness/passport.py does. */
export function readPassport(rel) {
  const tree = parseRaw(fs.readFileSync(abs(rel), "utf8"));
  const stored = tree.get("passport_sha256");
  const body = new Map([...tree].filter(([k]) => k !== "passport_sha256"));
  const recomputed = createHash("sha256").update(pyDumps(body), "utf8").digest("hex");
  const p = toPlain(tree);
  return {
    path: rel,
    sha256: stored,
    recomputedSha256: recomputed,
    status: p.status,
    task: p.task.id,
    requirements: Object.fromEntries(p.requirements.map((r) => [r.id, r.status])),
    propertyCases: p.checks?.property_tests?.cases ?? null,
    kernels: (p.checks?.comparator_kernels ?? []).length,
    executableStatus: p.executable?.status ?? null,
    reproduce: p.reproduce ?? null,
  };
}

/** Budget of an agent run (summary.json): list and charged dollars, seconds, model calls. */
export function readRunSummary(rel) {
  const s = readExact(rel);
  const calls = Object.values(s.budget.by_model ?? {}).reduce((n, m) => n + (m.calls ?? 0), 0);
  return {
    path: rel,
    task: s.task,
    arm: s.arm,
    model: s.model,
    planner: s.planner,
    usdList: s.budget.usd_list,
    usdCharged: s.budget.usd_actual,
    seconds: s.budget.elapsed_s,
    calls,
    acceptedInSession: s.accepted_in_session === true,
  };
}
