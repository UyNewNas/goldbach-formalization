#!/usr/bin/env bash
# Explicit stored-cap permit gates for a working pinned stock Lean CLI.
set -euo pipefail

cd "$(dirname "$0")/../../../../.."
test "$(cat lean-toolchain)" = leanprover/lean4:v4.33.0-rc1

targets=(
  ImbalancedChen.StoredHistoricalBoxPermit
  verification.parts.p1.round2.permit.StoredCapProbe
  verification.parts.p1.round2.permit.StoredCapAudit
)

lake build ImbalancedChen.StoredHistoricalBoxPermit
for module in "${targets[@]}"; do
  p1_source="${module//.//}.lean"
  p1_output=".lake/build/lib/lean/${module//.//}.olean"
  mkdir -p "$(dirname "$p1_output")"
  lake env lean -DwarningAsError=true -o "$p1_output" "$p1_source"
done
for module in "${targets[@]}"; do
  LEAN_NUM_THREADS=1 lake env leanchecker --verbose "$module"
done
