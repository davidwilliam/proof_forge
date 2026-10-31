# Library-based Compound proof on the deployed judge

`Solution.lean` is `tests/fixtures/library/compound_lib.lean`, written by the build team, not by a
model. It imports ProofForgeFin and proves all eight requirements of `rw-compound-comp`, including
REQ-REWARDS-BOUNDED, REQ-ACCOUNT-BOUNDED and REQ-NO-BACKDATED-REWARDS, which no Muse run has proved
(see `results/compound-1`).

It was submitted on 2026-10-30 to `POST /api/verify` on https://proofforge.fly.dev (judge image
`registry.fly.io/proofforge@sha256:51be605b...`, library source tree `f2fbb0d3...`). The returned
Passport, `passport.json`, is VERIFIED with all eight requirements VERIFIED; its
`passport_sha256` (`b654d456e1a5eec1...`) matches its content. The run checked 1,000 property cases,
the API's setting for synchronous checks.

It shows that the deployed judge vendors the library, scans every imported library module, and
checks a library-based proof with the same six kernels, leanchecker and axiom audit as any other
candidate. It is not a model result.

Reproduce from a clone: `bin/proofforge verify results/library-live-1/passport.json --candidate results/library-live-1/Solution.lean`
