#!/usr/bin/env bash
# Explicit round-two P1 gates for a working pinned stock Lean CLI.
# Shared root imports and whole-root verification remain owned by Part 0.
set -euo pipefail

cd "$(dirname "$0")/../../../.."
test "$(cat lean-toolchain)" = leanprover/lean4:v4.33.0-rc1

production=(
  ImbalancedChen.HistoricalUpperFiveCellGeometry
  ImbalancedChen.ActualHistoricalFifthCellIntegral
)
targets=(
  "${production[@]}"
  verification.parts.p1.round2.HistoricalCellProbe
  verification.parts.p1.round2.Part1HistoricalCellAudit
)

lake build "${production[@]}"

for module in "${targets[@]}"; do
  p1_source="${module//.//}.lean"
  p1_output=".lake/build/lib/lean/${module//.//}.olean"
  mkdir -p "$(dirname "$p1_output")"
  lake env lean -DwarningAsError=true -o "$p1_output" "$p1_source"
done

# Replay each target's own declarations with the unmodified bundled checker.
for module in "${targets[@]}"; do
  LEAN_NUM_THREADS=1 lake env leanchecker --verbose "$module"
done

# The audit above inventories all declarations defined by the two new
# production modules and their probe, including private/generated entries.
