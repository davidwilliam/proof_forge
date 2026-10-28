#!/bin/sh
# Build and deploy the API to Fly from the committed tree only: untracked and ignored files
# (.env, local notes, runs) never reach the remote builder.
# Usage: infra/fly/deploy.sh [app]   (default app name from fly.toml)
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
APP=${1:-$(sed -n 's/^app = "\(.*\)"/\1/p' "$ROOT/infra/fly/fly.toml")}
STAGE=$(mktemp -d)
trap 'rm -rf "$STAGE"' EXIT
git -C "$ROOT" archive HEAD | tar -x -C "$STAGE"
cp "$STAGE/infra/docker/Dockerfile.api.dockerignore" "$STAGE/.dockerignore"
LEAN="registry.fly.io/$APP:lean-4.35.0"
# The pinned Lean image, built on Fly's amd64 builder from infra/docker/Dockerfile.lean.
fly deploy "$STAGE/infra/docker" -a "$APP" -c "$STAGE/infra/fly/fly.toml" \
  --dockerfile "$STAGE/infra/docker/Dockerfile.lean" --build-only --push --image-label lean-4.35.0
fly deploy "$STAGE" -a "$APP" -c "$STAGE/infra/fly/fly.toml" \
  --build-arg LEAN_IMAGE="$LEAN" --image-label "api-$(git -C "$ROOT" rev-parse --short HEAD)"
