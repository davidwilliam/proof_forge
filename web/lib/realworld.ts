// Released real-world bugs, as written to generated/realworld.json by scripts/realworld.mjs
// from results/realworld-1/summary.json. The file can be missing or hold only some projects;
// normalizeRealworld never throws and drops what it cannot read.

export interface RwWitness {
  requirement: string | null;
  message: string | null;
  documented: boolean;
  input: unknown;
  output: { shares: number[] | null; failure: string | null };
  proved_output: number[] | null;
  lean_goal: string | null;
  confirmed_in_lean: boolean;
}

export interface RwVersion {
  tag: string;
  commit: string | null;
  status: "buggy" | "fixed" | null;
  cases: number | null;
  violating_cases: number | null;
  by_requirement: Record<string, number>;
  witness: RwWitness | null;
}

export interface RwPort {
  name: string;
  binary: string | null;
  kernel_refutation_checked: boolean;
}

export interface RwProject {
  key: string;
  name: string;
  project: string;
  repository: string | null;
  function: string | null;
  references: string[];
  referenceCandidate: string | null;
  versions: RwVersion[];
  leanConfirmation: { goals: number; checked: number } | null;
  ports: RwPort[];
}

export interface Realworld {
  source: string | null;
  generated: string | null;
  projects: RwProject[];
}

/** The projects this evaluation covers, in display order. A project missing from the data is listed as pending. */
export const EXPECTED_PROJECTS = [
  { name: "Spliit", match: /spliit/i },
  { name: "go-money", match: /go-money|gomoney/i },
  { name: "moneyphp", match: /moneyphp/i },
] as const;

const isObj = (v: unknown): v is Record<string, unknown> => !!v && typeof v === "object" && !Array.isArray(v);
const str = (v: unknown) => (typeof v === "string" && v ? v : null);
const num = (v: unknown) => (typeof v === "number" && Number.isFinite(v) ? v : null);
const nums = (v: unknown) => (Array.isArray(v) && v.every((x) => typeof x === "number") ? (v as number[]) : null);

export function displayName(key: string, project: string | null): string {
  const hit = EXPECTED_PROJECTS.find((p) => p.match.test(key) || (project ? p.match.test(project) : false));
  return hit?.name ?? project ?? key;
}

function witness(v: unknown): RwWitness | null {
  if (!isObj(v)) return null;
  const out = isObj(v.output) ? v.output : {};
  return {
    requirement: str(v.requirement),
    message: str(v.message),
    documented: v.documented === true,
    input: v.input ?? null,
    output: { shares: nums(out.shares), failure: str(out.failure) },
    proved_output: nums(v.proved_output),
    lean_goal: str(v.lean_goal),
    confirmed_in_lean: v.confirmed_in_lean === true,
  };
}

function version(v: unknown): RwVersion | null {
  if (!isObj(v)) return null;
  const tag = str(v.tag);
  if (!tag) return null;
  const by = isObj(v.by_requirement) ? v.by_requirement : {};
  const status = v.status === "buggy" || v.status === "fixed" ? v.status : null;
  return {
    tag,
    commit: str(v.commit),
    status,
    cases: num(v.cases),
    violating_cases: num(v.violating_cases),
    by_requirement: Object.fromEntries(Object.entries(by).filter(([, n]) => num(n) !== null)) as Record<string, number>,
    witness: witness(v.witness),
  };
}

function project(v: unknown): RwProject | null {
  if (!isObj(v)) return null;
  const key = str(v.key);
  if (!key) return null;
  const versions = (Array.isArray(v.versions) ? v.versions : []).map(version).filter((x): x is RwVersion => !!x);
  const lc = isObj(v.lean_confirmation) ? v.lean_confirmation : null;
  const goals = lc ? num(lc.goals) : null;
  const checked = lc ? num(lc.checked) : null;
  return {
    key,
    name: displayName(key, str(v.project)),
    project: str(v.project) ?? key,
    repository: str(v.repository),
    function: str(v.function),
    references: (Array.isArray(v.references) ? v.references : []).filter((r): r is string => typeof r === "string"),
    referenceCandidate: isObj(v.reference) ? str(v.reference.candidate) : null,
    versions,
    leanConfirmation: goals !== null && checked !== null ? { goals, checked } : null,
    ports: (Array.isArray(v.ports) ? v.ports : [])
      .filter(isObj)
      .map((p) => ({ name: str(p.name) ?? "port", binary: str(p.binary), kernel_refutation_checked: p.kernel_refutation_checked === true })),
  };
}

export function normalizeRealworld(raw: unknown): Realworld {
  if (!isObj(raw)) return { source: null, generated: null, projects: [] };
  const projects = (Array.isArray(raw.projects) ? raw.projects : []).map(project).filter((p): p is RwProject => !!p && p.versions.length > 0);
  const rank = (p: RwProject) => {
    const i = EXPECTED_PROJECTS.findIndex((e) => e.name === p.name);
    return i < 0 ? EXPECTED_PROJECTS.length : i;
  };
  projects.sort((a, b) => rank(a) - rank(b));
  return { source: str(raw.source), generated: str(raw.generated), projects };
}

/** Expected projects with no data yet. */
export function pendingProjects(rw: Realworld): string[] {
  return EXPECTED_PROJECTS.map((e) => e.name).filter((name) => !rw.projects.some((p) => p.name === name));
}

/** "a, b and c" */
export function listWords(words: string[]): string {
  if (words.length <= 1) return words.join("");
  return `${words.slice(0, -1).join(", ")} and ${words[words.length - 1]}`;
}

/** Plain description of a witness input, for example "-2 split 3 ways" or "5 allocated by ratios 0, 7, 3". */
export function describeInput(input: unknown): string {
  if (!isObj(input)) return JSON.stringify(input);
  const amount = num(input.amount);
  const n = num(input.n);
  const ratios = nums(input.ratios) ?? nums(input.shares) ?? nums(input.weights);
  if (amount !== null && n !== null && Object.keys(input).length === 2) return `${amount} split ${n} ways`;
  if (amount !== null && ratios && Object.keys(input).length === 2) return `${amount} allocated by ratios ${ratios.join(", ")}`;
  return JSON.stringify(input);
}
