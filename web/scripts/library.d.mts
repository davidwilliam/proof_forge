/** Lean files under lib/<dir>, with their theorem and definition declarations counted (comments excluded). */
export function countDeclarations(dir: string): { files: number; theorems: number; definitions: number };
