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
| `/` | Overview: the problem, the four steps, headline E1 and E2 figures (`lib/evidence.ts`, checked against `results/` by `tests/evidence.test.ts`) and released real-world bugs (`generated/realworld.json`) |
| `/forge` | Forge session. Query parameters: `job` (attach to an existing job), `recording`, `task`; `/` with any of them redirects here |
| `/passport/<sha256>` | Passport evidence view |
| `/challenge` | Binary check of a hidden variant |
| `/app` | Split a payout on the buggy and repaired builds |
| `/results` | E1 and E2 results |
