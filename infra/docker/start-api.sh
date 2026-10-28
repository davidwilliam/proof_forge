#!/bin/sh
# Entry point of the API image. PF_DATA (a mounted volume on hosts) must belong to the
# forge user; the server itself never runs as root.
set -eu
DATA="${PF_DATA:-/opt/proofforge/runs}"
mkdir -p "$DATA"
chown forge:forge "$DATA"
# Passports record the judge image; on Fly the deployed image reference carries its digest.
export PF_IMAGE_ID="${PF_IMAGE_ID:-${FLY_IMAGE_REF:-unknown}}"
exec setpriv --reuid=forge --regid=forge --init-groups env HOME=/home/forge \
  PATH=/home/forge/.elan/bin:/opt/venv/bin:/usr/local/bin:/usr/bin:/bin \
  /opt/venv/bin/uvicorn server.app:app --host 0.0.0.0 --port "${PORT:-8000}"
