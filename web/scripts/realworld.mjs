// Copies what the home page shows about released real-world bugs from
// results/realworld-1/summary.json into generated/realworld.json. No checks are run.
// Usage: node scripts/realworld.mjs [path/to/summary.json]
//
// Per project it keeps the source repository, the function, the proved reference and, per
// released version, the case counts, violations by requirement and one witness (the first
// one the project's issue tracker documents, otherwise the first one recorded).

import fs from "node:fs";
import path from "node:path";

const here = path.dirname(new URL(import.meta.url).pathname);
const root = path.resolve(here, "../..");
const src = path.resolve(process.argv[2] ?? path.join(root, "results/realworld-1/summary.json"));
const dest = path.resolve(here, "../generated/realworld.json");

if (!fs.existsSync(src)) {
  console.error(`${path.relative(process.cwd(), src)} not found; nothing written`);
  process.exit(1);
}
const summary = JSON.parse(fs.readFileSync(src, "utf8"));

const num = (v) => (typeof v === "number" && Number.isFinite(v) ? v : null);
const str = (v) => (typeof v === "string" && v ? v : null);
const obj = (v) => (v && typeof v === "object" && !Array.isArray(v) ? v : {});

function witness(w) {
  if (!w || typeof w !== "object") return null;
  const out = obj(w.output);
  return {
    requirement: str(w.requirement),
    message: str(w.message),
    documented: w.documented === true,
    input: w.input ?? null,
    output: { shares: Array.isArray(out.shares) ? out.shares : null, failure: str(out.failure) },
    proved_output: Array.isArray(w.proved_output) ? w.proved_output : null,
    lean_goal: str(w.lean_goal),
    confirmed_in_lean: w.confirmed_in_lean === true,
  };
}

function version(key, v) {
  const ws = Array.isArray(v.witnesses) ? v.witnesses : [];
  const pick = ws.find((w) => w && w.documented) ?? ws[0];
  return {
    tag: str(v.tag) ?? key,
    commit: str(v.commit),
    status: str(v.status),
    cases: num(v.cases),
    violating_cases: num(v.violating_cases),
    failures_on_valid_input: num(v.failures_on_valid_input),
    by_requirement: Object.fromEntries(Object.entries(obj(v.by_requirement)).filter(([, n]) => num(n) !== null)),
    witnesses: ws.length,
    witness: witness(pick),
  };
}

const projects = Object.entries(obj(summary.projects)).map(([key, p]) => ({
  key,
  project: str(p.project) ?? key,
  repository: str(p.repository),
  license: str(p.license),
  function: str(p.function),
  references: Array.isArray(p.references) ? p.references.filter((r) => typeof r === "string") : [],
  reference: { candidate: str(obj(p.reference).candidate) },
  versions: Object.entries(obj(p.versions)).map(([k, v]) => version(k, obj(v))),
  lean_confirmation: p.lean_confirmation ? { goals: num(p.lean_confirmation.goals), checked: num(p.lean_confirmation.checked) } : null,
  ports: Object.entries(obj(p.ports)).map(([name, port]) => ({
    name,
    note: str(port.note),
    judge: str(port.judge),
    binary: str(port.binary),
    kernel_refutation_checked: port.kernel_refutation_checked === true,
  })),
}));

const out = {
  source: path.relative(root, src),
  generated: str(summary.generated),
  projects,
};
fs.mkdirSync(path.dirname(dest), { recursive: true });
fs.writeFileSync(dest, JSON.stringify(out, null, 2) + "\n");
const versions = projects.reduce((n, p) => n + p.versions.length, 0);
console.log(`${projects.length} projects, ${versions} versions; wrote ${path.relative(process.cwd(), dest)}`);
