#!/usr/bin/env bash
# Network-enabled setup for exact git fetches and the explicitly trusted Mathlib cache only.
# No inherited GitHub variables, secret values, user git config, or extra credentials.
# Filesystem and runner UID are shared: this is credential hygiene, not hostile-code confinement.
set -euo pipefail
: "${COLD_ROOT:?}" "${COLD_HOME:?}" "${COLD_TOOLCHAIN:?}" "${LAKE_CACHE_DIR:?}" "${MATHLIB_CACHE_DIR:?}"
test "$(id -u)" != 0
test -x "$COLD_TOOLCHAIN/bin/lean"
test -d "$COLD_HOME/tmp"
exec sudo --non-interactive /usr/bin/unshare --mount --pid --fork --mount-proc -- \
  /usr/bin/setpriv --reuid="$(id -u)" --regid="$(id -g)" --clear-groups \
  --inh-caps=-all --ambient-caps=-all --bounding-set=-all --no-new-privs \
  /usr/bin/env -i \
  PATH="$COLD_TOOLCHAIN/bin:/usr/bin:/bin" HOME="$COLD_HOME" TMPDIR="$COLD_HOME/tmp" \
  LANG=C.UTF-8 LC_ALL=C.UTF-8 GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null \
  GIT_TERMINAL_PROMPT=0 LEAN_NUM_THREADS=2 LAKE_NO_CACHE=1 LAKE_ARTIFACT_CACHE=false \
  MATHLIB_NO_CACHE_ON_UPDATE=1 LAKE_CACHE_DIR="$LAKE_CACHE_DIR" \
  MATHLIB_CACHE_DIR="$MATHLIB_CACHE_DIR" \
  /usr/bin/bash -euo pipefail -c 'cd "$1"; shift; exec "$@"' bash "$COLD_ROOT" "$@"
