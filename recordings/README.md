# Recordings

Recorded repair sessions replayed by the API (`POST /api/jobs` with `mode: "replay"`). A replay re-emits the recorded events with compressed timing and labels them "Recorded run"; the final candidate is then checked fresh ("Fresh check of stored artifact"). Nothing in a replay calls a model.

| Recording | Task | Arm | Model | Result | Events |
|---|---|---|---|---|---|
| `flagship-a2-run7` | payout-flagship | A2 | muse-spark-1.3-contributor, planner muse-wonder-1.0 | accepted after 1213 s, 54 versions (see `formal/evidence/muse-repair-002`) | earlier format: no `tool` events |
| `flagship-a2-20261027` | payout-flagship | A2 | muse-spark-1.3-contributor, planner muse-wonder-1.0 | not accepted: 7 of 8 requirements proved, `req_conservation` unresolved after 3235 s, 74 versions | full `tool` and `plan` events |

Model-written text is stored verbatim except that em dashes are replaced with semicolons.
