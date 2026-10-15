#!/usr/bin/env bash
set -euo pipefail
# P0-only launcher. FD 9 survives exec and is inherited by descendants.
lock=/workspace/shared/chen-coordination/locks/heavy.lock
exec 9>>"$lock"
flock -n 9 || { echo 'WAITING_FOR_RESOURCE: host heavy slot is held' >&2; exit 75; }
export LEAN_NUM_THREADS=2
exec "$@"
