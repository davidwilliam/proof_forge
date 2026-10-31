# ProofForge web

Requires Node 20.9 or later and pnpm.

## Run

Start the API from the repository root:

```sh
.venv/bin/uvicorn server.app:app --port 8765
```

Then, in `web/`:

```sh
pnpm install
pnpm test                # property and reducer tests; writes generated/property-tests.json
pnpm passport:repaired   # Passport for the repaired sidecar build; writes generated/repaired-passport.json
pnpm realworld           # real-world bug results from results/realworld-1/summary.json; writes generated/realworld.json
pnpm evidence            # machine-readable summary of the home page; writes public/evidence.json and public/llms.txt
node scripts/check-fixes.mjs  # candidates and recorded Passports for the "Check a fix" panel; writes public/check/
pnpm dev                 # http://localhost:3000
```

Production build:

```sh
pnpm build
pnpm start
```

## Configuration

| Variable | Default | Purpose |
|---|---|---|
| `NEXT_PUBLIC_API_BASE` | `http://localhost:8765` | ProofForge API base URL |
| `NEXT_PUBLIC_DEFAULT_RECORDING` | `flagship-a2-run7` | Accepted recording preselected on the forge session page |

## Pages

| Path | Content |
|---|---|
| `/` | Overview: the Cetus hotfix refuted and fixed, the trust model, Muse alone against Muse with ProofForge, open-weight, planner and library figures (`lib/contribution.ts`, checked by `tests/contribution.test.ts`), the "Check a fix" panel (`lib/checkfix.ts`, `components/CheckFix.tsx`, `public/check/`, checked by `tests/checkfix.test.ts`), the Cetus, Balancer, Euler, Knight Capital and Hundred Finance cases with their Passports and real-code results (`lib/flagships.ts`, checked against `results/` and `realworld/tasks/` by `tests/flagships.test.ts`), the benchmark, headline E1 and E2 figures (`lib/evidence.ts`, checked by `tests/evidence.test.ts`) and released real-world bugs (`generated/realworld.json`) |
| `/opengraph-image`, `/twitter-image` | The card shown for shared links, from the same data modules |
| `/llms.txt`, `/evidence.json` | The same claims, figures, Passport hashes, source paths and reproduction commands for agents (`scripts/evidence.mjs`; `tests/evidence-files.test.ts` fails when they are stale) |
| `/forge` | Forge session. Query parameters: `job` (attach to an existing job), `recording`, `task`; `/` with any of them redirects here |
| `/passport/<sha256>` | Passport evidence view |
| `/challenge` | Binary check of a hidden variant |
| `/app` | Split a payout on the buggy and repaired builds |
| `/results` | E1 and E2 results; the E2 case rows load from the API when opened |
