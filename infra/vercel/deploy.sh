#!/bin/sh
# Deploy the web front end to Vercel from the committed tree only.
# Usage: infra/vercel/deploy.sh SCOPE [API_BASE]   (API_BASE default https://proofforge.fly.dev)
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
SCOPE=$1
API=${2:-https://proofforge.fly.dev}
COMMIT=$(git -C "$ROOT" rev-parse HEAD)
STAGE=$(mktemp -d)
trap 'rm -rf "$STAGE"' EXIT
git -C "$ROOT" archive "$COMMIT" web | tar -x -C "$STAGE"
cd "$STAGE/web"
vercel link --yes --project proofforge --scope "$SCOPE" >/dev/null
vercel deploy --prod --yes --scope "$SCOPE" --build-env NEXT_PUBLIC_API_BASE="$API" --env NEXT_PUBLIC_API_BASE="$API"
"$ROOT/infra/github-deployment.sh" production https://proofforge.dev "$COMMIT"
