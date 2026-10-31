#!/usr/bin/env bash
# Developer flow with Muse Code and ProofForge: Muse Code receives the Balancer V2 incident
# report, writes the fix, checks it with ProofForge through the MCP server and gets a Passport.
#
# Runs agents/muse_code.py in the proofforge arm (the MCP server, the skill, the workspace
# AGENTS.md and ProofForgeFin) with the developer prompt in balancer-prompt.md, under the same
# caps as the measured runs ($10 at list prices, 4 hours). The Muse Code JSONL transcript is
# written to <out>/events.jsonl, the ProofForge tool calls to <out>/mcp-calls.jsonl, every model
# call to <out>/calls.jsonl, and the final candidate's Passport to <out>/passport.json.
#
# Requires: Muse Code (`muse`), Docker with the image proofforge-lean:4.35.0, and META_API_KEY in
# the environment or in the repository's .env.
#
# Usage: integrations/muse/demo/run.sh [out-dir]   (default results/muse-code-1/demo-balancer)
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
out="${1:-$root/results/muse-code-1/demo-balancer}"
export MUSE_NO_AUTO_UPDATE=1
exec python3 "$root/agents/muse_code.py" \
  --task rw-balancer-upscale --arm proofforge \
  --prompt-file "$here/balancer-prompt.md" \
  --budget-usd 10 --budget-wall 14400 \
  --out "$out"
