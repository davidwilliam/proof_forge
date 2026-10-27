// Reads files written by the test run and by scripts/repaired-passport.mjs.
// Server only: uses the filesystem at request time so the page always shows the latest run.

import fs from "node:fs";
import path from "node:path";

export interface PropertyTestReport {
  suite: string;
  library: string;
  properties: number;
  cases: number;
  failed: string[];
  generated: string;
}

export interface RepairedPassportRef {
  passport_sha256: string;
  status: string;
  solution_file: string;
  solution_sha256: string;
  generated: string;
}

function readJson<T>(name: string): T | null {
  try {
    return JSON.parse(fs.readFileSync(path.join(process.cwd(), "generated", name), "utf8")) as T;
  } catch {
    return null;
  }
}

export const readPropertyTests = () => readJson<PropertyTestReport>("property-tests.json");
export const readRepairedPassport = () => readJson<RepairedPassportRef>("repaired-passport.json");
