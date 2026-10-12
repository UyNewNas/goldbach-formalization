#!/usr/bin/env bash
# Explicit P1 gates for an environment where the pinned stock Lean CLI starts.
# The shared root gates remain Part 0's separate integration responsibility.
set -euo pipefail

cd "$(dirname "$0")/../../.."
test "$(cat lean-toolchain)" = leanprover/lean4:v4.33.0-rc1

production=(
  ImbalancedChen.HistoricalPrefixCertificate
  ImbalancedChen.OrdinaryLowerFourFrontier
  ImbalancedChen.ActualSelectedPrefixLowerCellSum
  ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral
)
targets=(
  "${production[@]}"
  verification.parts.p1.LevelCheckProbe
  verification.parts.p1.Part1HistoryAudit
)

# Obtain the normal Lake dependency objects without changing pins or options.
lake build "${production[@]}"

# Strictly elaborate every P1 source, including the standalone verification
# modules, in dependency order; emit the exact objects subsequently replayed.
for module in "${targets[@]}"; do
  source="${module//.//}.lean"
  output=".lake/build/lib/lean/${module//.//}.olean"
  mkdir -p "$(dirname "$output")"
  lake env lean -DwarningAsError=true -o "$output" "$source"
done

# The bundled checker replays each named module's own declarations. Naming
# only the audit would not replay the four production modules and the probe.
# Keep the six replays sequential to limit simultaneous import environments.
for module in "${targets[@]}"; do
  LEAN_NUM_THREADS=1 lake env leanchecker --verbose "$module"
done

# Audit output was produced while elaborating Part1HistoryAudit above. It
# enumerates all defining-module declarations, including private/generated
# ones, and rejects any axiom outside the original three-axiom allowlist.
