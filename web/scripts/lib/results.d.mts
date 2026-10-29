// Types for results.mjs.

export const ROOT: string;

/** Parsed JSON; integers outside the safe range are bigint. */
export type Exact = null | boolean | number | bigint | string | Exact[] | { [key: string]: Exact };

export function readExact(rel: string): any;
export function fileSha256(rel: string): string;

export interface PassportFacts {
  path: string;
  sha256: string;
  recomputedSha256: string;
  status: string;
  task: string;
  requirements: Record<string, string>;
  propertyCases: number | null;
  kernels: number;
  executableStatus: string | null;
  reproduce: string | null;
}
export function readPassport(rel: string): PassportFacts;

export interface RunSummaryFacts {
  path: string;
  task: string;
  arm: string;
  model: string;
  planner: string;
  usdList: number;
  usdCharged: number;
  seconds: number;
  calls: number;
  acceptedInSession: boolean;
}
export function readRunSummary(rel: string): RunSummaryFacts;
