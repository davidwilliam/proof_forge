// Loads a TypeScript module of web/ that has no runtime imports, with the TypeScript compiler's
// transpiler. Used by scripts/evidence.mjs and scripts/check-fixes.mjs.

import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { pathToFileURL } from "node:url";
import ts from "typescript";
import { ROOT } from "./results.mjs";

export async function loadTs(rel) {
  const src = fs.readFileSync(path.join(ROOT, "web", rel), "utf8");
  const { outputText } = ts.transpileModule(src, {
    compilerOptions: { module: ts.ModuleKind.ESNext, target: ts.ScriptTarget.ES2022 },
    fileName: rel,
  });
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "pf-load-ts-"));
  const file = path.join(tmp, path.basename(rel).replace(/\.ts$/, ".mjs"));
  fs.writeFileSync(file, outputText);
  try {
    return await import(pathToFileURL(file).href);
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
}
