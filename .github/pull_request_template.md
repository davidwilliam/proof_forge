## What changes

## Checks

- [ ] Candidate changes: `bin/proofforge check` returns VERIFIED (the `proofforge` workflow posts the verdict).
- [ ] No edits to a task's `spec/`, `app/`, Lake files, `spec/locked.json`, `reference/`, `attacks/` or `witnesses/`.
- [ ] Site or data changes: `pnpm vitest run` and every `node scripts/<name>.mjs --check` in `web/` pass.
