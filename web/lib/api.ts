// Typed client for the ProofForge API (server/app.py). Used from server components
// and from the browser; the base URL comes from NEXT_PUBLIC_API_BASE.

export const API_BASE = (process.env.NEXT_PUBLIC_API_BASE || "http://localhost:8765").replace(/\/+$/, "");

export function apiUrl(path: string): string {
  return `${API_BASE}${path.startsWith("/") ? path : `/${path}`}`;
}

export class ApiError extends Error {
  constructor(public status: number, message: string) {
    super(message);
  }
}

async function request<T>(path: string, init?: RequestInit): Promise<T> {
  let res: Response;
  try {
    res = await fetch(apiUrl(path), { cache: "no-store", ...init });
  } catch (e) {
    throw new ApiError(0, `API unreachable at ${API_BASE}: ${(e as Error).message}`);
  }
  if (!res.ok) {
    let detail = res.statusText;
    try {
      const body = (await res.json()) as { detail?: unknown };
      if (body && typeof body.detail === "string") detail = body.detail;
    } catch {
      // keep statusText
    }
    throw new ApiError(res.status, `${res.status} ${detail}`);
  }
  return (await res.json()) as T;
}

export function getJson<T>(path: string): Promise<T> {
  return request<T>(path);
}

export function postJson<T>(path: string, body: unknown): Promise<T> {
  return request<T>(path, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
}

// Response types

export interface Requirement {
  id: string;
  theorem: string;
  statement: string | null;
  text: string | null;
}

export interface TaskSummary {
  id: string;
  family: string;
  split: string;
  namespace: string;
  issue: string;
  definitions: string[];
  requirements: Requirement[];
  manifest_sha256: string;
}

export interface TaskDetail extends TaskSummary {
  files: Record<string, string>;
  locked: Record<string, string>;
  comparator: {
    challenge_module?: string;
    solution_module?: string;
    theorem_names?: string[];
    definition_names?: string[];
    permitted_axioms?: string[];
  };
}

export interface Job {
  id: string;
  task: string;
  mode: string;
  arm: string;
  recording: string | null;
  state: string;
  created: number;
  passport_sha256?: string;
  versions?: number;
}

export interface CheckRecord {
  command?: string[] | string;
  exit_code?: number;
  elapsed_ms?: number;
  stdout_sha256?: string;
  stderr_sha256?: string;
}

export interface Witness {
  requirement: string;
  message: string;
  input: unknown;
  output: unknown;
}

export interface PassportRequirement {
  id: string;
  theorem: string;
  statement: string | null;
  statement_sha256: string;
  text: string | null;
  status: string;
  axioms_used: string[] | null;
  witness: Witness | null;
  binary_violations: number;
}

export interface Budget {
  usd_cap?: number | null;
  wall_cap_s?: number | null;
  stop?: string | null;
  usd_list?: number;
  usd_actual?: number;
  elapsed_s?: number;
  by_model?: Record<string, { calls?: number; prompt?: number; cached?: number; completion?: number; usd_list?: number; usd_actual?: number }>;
}

export interface Provenance {
  model?: string;
  mode?: string;
  effort?: string;
  planner?: string;
  arm?: string;
  accepted?: boolean;
  accepted_in_session?: boolean;
  versions?: number;
  elapsed_s?: number;
  usage?: Record<string, number>;
  budget?: Budget;
  final_status?: Record<string, string>;
  [k: string]: unknown;
}

export interface Passport {
  schema_version: number;
  generated: string;
  task: { id: string; family: string; namespace: string; definitions: string[] };
  status: string;
  proof_check: { accepted: boolean; reasons: string[] };
  requirements: PassportRequirement[];
  locked: { manifest_sha256: string; files: Record<string, string> };
  toolchain: { lean: string; judge_image: string | null };
  solution: { files: Record<string, string>; solution_tree_sha256: string };
  executable: { target: string; sha256: string | null; platform?: string; status: string; wrapper: string };
  checks: {
    tree: { passed: boolean; problems: string[] };
    impl_scan: { passed: boolean; problems: string[] };
    comparator: CheckRecord | null;
    comparator_kernels: string[];
    leanchecker: CheckRecord | null;
    axiom_audit: CheckRecord | null;
    property_tests: {
      cases?: number;
      followup_cases?: number;
      seed?: number;
      violations?: Record<string, number>;
      build?: CheckRecord | null;
    };
  };
  permitted_axioms: string[];
  trust_assumptions: string[];
  scope: string;
  provenance: Provenance | null;
  reproduce: string;
  timings_ms?: Record<string, number | null>;
  passport_sha256: string;
}

/** The candidate source a Passport checked, as stored by the API. */
export interface PassportCandidate {
  filename: string;
  source: string;
  sha256: string;
  reproduce: string;
}

export interface PayoutState {
  balances: [number, number][];
  auth: [number, number][];
  applied: number[];
}

export interface PayoutRequestBody {
  txId: number;
  requester: number;
  source: number;
  recipients: number[];
  amount: number;
}

export interface PayoutResponse {
  build: string;
  solution_sha256: string;
  executable_sha256: string;
  result: { outcome?: string; state?: PayoutState; error?: string };
  elapsed_ms: number;
}

export interface ChallengeResult {
  variant: string;
  status: string;
  violations: Record<string, number>;
  witness: Witness | null;
  executable_sha256: string | null;
  elapsed_ms: number;
  label: string;
  repair_job?: string;
}
