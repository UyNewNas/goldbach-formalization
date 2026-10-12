#!/usr/bin/env bash
# Explicit P1 historical saving gates for the pinned stock CLI.
# Part 0 owns public-root integration and its canonical gates.
set -euo pipefail

cd "$(dirname "$0")/../../../.."
test "$(cat lean-toolchain)" = leanprover/lean4:v4.33.0-rc1

production=(
  ImbalancedChen.HistoricalUpperFiveCellGeometry
  ImbalancedChen.ActualHistoricalFifthCellIntegral
  ImbalancedChen.ActualHistoricalFifthSavingIntegral
  ImbalancedChen.HistoricalFifthCutoffInvariance
)
targets=(
  "${production[@]}"
  verification.parts.p1.round2.HistoricalCellProbe
  verification.parts.p1.round3.Part1HistoricalSavingAudit
)

lake build "${production[@]}"

for module in "${targets[@]}"; do
  p1_source="${module//.//}.lean"
  p1_output=".lake/build/lib/lean/${module//.//}.olean"
  mkdir -p "$(dirname "$p1_output")"
  lake env lean -DwarningAsError=true -o "$p1_output" "$p1_source"
done

for module in "${targets[@]}"; do
  LEAN_NUM_THREADS=1 lake env leanchecker --verbose "$module"
done
