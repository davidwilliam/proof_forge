# Origin and provenance

ProofForge is being built for the Meta Global AI Developer Hackathon, organized by Meta and Cerebral Valley (kickoff 2026-10-26 12:00 ET, submissions due 2026-11-04 21:00 ET).

## Built during the hackathon

Everything in this repository was created on or after 2026-10-26. Implementation started 2026-10-26 with the day-0 tooling checks in `experiments/` and `infra/`.

Development uses AI coding agents under the owner's direction and review.

## Not built during the hackathon (dependencies)

| Dependency | Use |
|---|---|
| Lean 4 v4.35.0 (kernel, compiler, Lake, `lake comparator`, `leanchecker`) | Proof checking, challenge comparison, executable build |
| bubblewrap | Comparator's sandbox |
| elan | Lean toolchain installer |
| Ubuntu 24.04 base image | Judge/dev container |
| Meta Model API (Muse Spark, Muse Wonder) | Repair, proof and planning agents |
| Muse Code 1.4.14 (Meta's coding agent) | Runs ProofForge as an MCP server with the ProofForge skill |
| Baseten Model APIs (Muse Spark Open) | Serving of Meta's open-weight model |
| Modal and vLLM (Muse Glimmer 30B) | Self-hosted serving of Muse Glimmer 30B |
| FastAPI, Starlette, Pydantic, Uvicorn | API server |
| Next.js, React | Web front end |
| fast-check, Vitest | Property tests of the web glue code |

No code from earlier personal projects is included.
