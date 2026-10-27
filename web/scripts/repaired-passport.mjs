// Creates a Passport for the repaired build the payout sidecar runs
// (formal/evidence/muse-repair-002/Solution.lean) via POST /api/verify, and records its
// sha256 in generated/repaired-passport.json for the /app page. No model calls are made.
// Usage: node scripts/repaired-passport.mjs   (takes about 30 to 60 s)

import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";

const here = path.dirname(new URL(import.meta.url).pathname);
const api = (process.env.NEXT_PUBLIC_API_BASE || "http://localhost:8765").replace(/\/+$/, "");
const rel = "formal/evidence/muse-repair-002/Solution.lean";
const file = path.resolve(here, "../..", rel);
const source = fs.readFileSync(file, "utf8");
const sha = createHash("sha256").update(fs.readFileSync(file)).digest("hex");

console.log(`POST ${api}/api/verify for ${rel} (sha256 ${sha.slice(0, 16)})`);
const res = await fetch(`${api}/api/verify`, {
  method: "POST",
  headers: { "Content-Type": "application/json" },
  body: JSON.stringify({ task: "payout-flagship", source }),
});
if (!res.ok) {
  console.error(`verify failed: ${res.status} ${await res.text()}`);
  process.exit(1);
}
const p = await res.json();
const out = {
  passport_sha256: p.passport_sha256,
  status: p.status,
  solution_file: rel,
  solution_sha256: sha,
  generated: new Date().toISOString(),
};
const dest = path.resolve(here, "../generated/repaired-passport.json");
fs.mkdirSync(path.dirname(dest), { recursive: true });
fs.writeFileSync(dest, JSON.stringify(out, null, 2) + "\n");
console.log(`Passport ${p.passport_sha256} ${p.status}; wrote ${path.relative(process.cwd(), dest)}`);
