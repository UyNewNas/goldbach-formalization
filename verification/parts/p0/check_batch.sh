#!/usr/bin/env bash
# Explicit batch verification in a normal checkout with the pinned stock CLI.
# Existing cache objects are reused by Lake; no dependency update is requested.
set -euo pipefail

cd "$(dirname "$0")/../../.."
batch="${1:-buchstab}"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.33.0-rc1
python3 verification/parts/p0/check_pins.py

case "$batch" in
  buchstab)
    production=(ImbalancedChen.CurrentChenBuchstabRefinement)
    replay=(ImbalancedChen.CurrentChenBuchstabRefinement)
    audit=verification.parts.p5.BuchstabAudit
    ;;
  p2)
    production=(
      ImbalancedChen.Certificates.RationalLogCertificate
      ImbalancedChen.Certificates.PairedFibreIntegral
      ImbalancedChen.Certificates.PairedCertificateChecker
      ImbalancedChen.Certificates.PairedV2Data
      ImbalancedChen.Certificates.PairedV2
      ImbalancedChen.Certificates.AboveMuSecondCoarse
    )
    replay=("${production[@]}")
    audit=verification.part2.CertificateAudit
    ;;
  p3-long-slot)
    production=(ImbalancedChen.Part3LongSlotDistribution)
    replay=("${production[@]}")
    audit=verification.parts.p0.LongSlotAudit
    ;;
  paired-buchstab)
    production=(ImbalancedChen.CurrentPairedBuchstabBridge)
    replay=("${production[@]}")
    audit=verification.parts.p0.PairedBuchstabAudit
    ;;
  *)
    printf 'Unknown batch: %s\n' "$batch" >&2
    exit 64
    ;;
esac

# Fail early if this checkout has not received the requested batch.
for module in "${production[@]}" "$audit"; do
  test -f "${module//.//}.lean"
done

receipt_dir="verification/parts/p0/local-results/$(git rev-parse HEAD)/$batch"
mkdir -p "$receipt_dir"
git rev-parse HEAD > "$receipt_dir/source-commit.txt"
git status --porcelain > "$receipt_dir/source-status.txt"
lake env lean --version 2>&1 | tee "$receipt_dir/toolchain.log"

# The common old root is insufficient: every new production module is explicit.
lake build "${production[@]}" 2>&1 | tee "$receipt_dir/lake-build.log"
for module in "${production[@]}" "$audit"; do
  source="${module//.//}.lean"
  object=".lake/build/lib/lean/${module//.//}.olean"
  mkdir -p "$(dirname "$object")"
  lake env lean -DwarningAsError=true -o "$object" "$source" \
    2>&1 | tee "$receipt_dir/$module.compile.log"
done
for module in "${replay[@]}"; do
  lake env leanchecker --verbose "$module" \
    2>&1 | tee "$receipt_dir/$module.replay.log"
done
python3 verification/parts/p0/check_pins.py
printf 'Explicit batch passed: %s at %s\n' "$batch" "$(cat "$receipt_dir/source-commit.txt")"
printf 'This receipt does not replace final full-root build and axiom gates.\n'
