#!/bin/sh
# Record a finished deploy as a GitHub deployment with a success status, so the repository's
# Deployments panel shows which commit each environment runs. Skipped when gh is not available.
# Usage: infra/github-deployment.sh ENVIRONMENT URL COMMIT
set -eu
ENVIRONMENT=$1
URL=$2
COMMIT=$3
command -v gh >/dev/null 2>&1 || { echo "gh not found: deployment not recorded" >&2; exit 0; }
REPO=${GITHUB_REPOSITORY:-davidwilliam/proof_forge}
# required_contexts is empty: the deploy already ran from the committed tree, so GitHub does not
# wait for commit statuses before recording it.
ID=$(printf '{"ref":"%s","environment":"%s","auto_merge":false,"required_contexts":[],"description":"Deployed from %s"}' \
  "$COMMIT" "$ENVIRONMENT" "$COMMIT" | gh api "repos/$REPO/deployments" --input - --jq .id)
gh api "repos/$REPO/deployments/$ID/statuses" -f state=success -f environment_url="$URL" \
  -f log_url="https://github.com/$REPO/commit/$COMMIT" --jq '"recorded deployment " + (.id|tostring)' >&2
