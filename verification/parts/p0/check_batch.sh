#!/usr/bin/env bash
# Explicit batch verification in a normal checkout with the pinned stock CLI.
# Existing cache objects are reused by Lake; no dependency update is requested.
set -euo pipefail

cd "$(dirname "$0")/../../.."
batch="${1:-buchstab}"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.33.0-rc1
python3 verification/parts/p0/check_pins.py
suppliers=()

case "$batch" in
  buchstab)
    production=(ImbalancedChen.CurrentChenBuchstabRefinement)
    replay=(ImbalancedChen.CurrentChenBuchstabRefinement)
    audit=verification.parts.p5.BuchstabAudit
    ;;
  p2-first)
    production=(
      ImbalancedChen.Certificates.RationalLogCertificate
      ImbalancedChen.Certificates.PairedFibreIntegral
      ImbalancedChen.Certificates.PairedCertificateChecker
      ImbalancedChen.Certificates.PairedV2Data
      ImbalancedChen.Certificates.PairedV2
    )
    replay=("${production[@]}")
    audit=verification.parts.p0.CertificatesFirstCellAudit
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
  p2-coarse)
    production=(ImbalancedChen.Certificates.AboveMuSecondCoarse)
    replay=("${production[@]}")
    audit=verification.parts.p0.CoarseAudit
    ;;
  p5-finite)
    production=(ImbalancedChen.CurrentChenMeanLedger ImbalancedChen.CurrentChenLowerScale)
    replay=("${production[@]}")
    audit=verification.parts.p0.ChenFiniteAudit
    ;;
  paired-buchstab)
    production=(ImbalancedChen.CurrentPairedBuchstabBridge)
    suppliers=(
      ImbalancedChen.CurrentChenBuchstabRefinement
      ImbalancedChen.Certificates.RationalLogCertificate
      ImbalancedChen.Certificates.PairedFibreIntegral
      ImbalancedChen.Certificates.PairedCertificateChecker
      ImbalancedChen.Certificates.PairedV2Data
      ImbalancedChen.Certificates.PairedV2
    )
    replay=("${production[@]}")
    audit=verification.parts.p0.PairedBuchstabAudit
    ;;
  *)
    printf 'Unknown batch: %s\n' "$batch" >&2
    exit 64
    ;;
esac

# Fail early if this checkout has not received the requested batch.
sources=(lean-toolchain lakefile.toml lake-manifest.json
  verification/parts/p0/check_batch.sh verification/parts/p0/check_pins.py
  verification/parts/p0/check_sources.py verification/verify_variable_envelope_boxes.py)
if [[ "$batch" = p2-first || "$batch" = p2 ]]; then
  sources+=(verification/part2/import_paired_v2.py
    verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json)
fi
for module in "${production[@]}" "${suppliers[@]}" "$audit"; do
  test -f "${module//.//}.lean"
  sources+=("${module//.//}.lean")
done
# A receipt for a fixed commit must not silently use edited or untracked inputs.
for source in "${sources[@]}"; do
  git ls-files --error-unmatch "$source" > /dev/null
done
git diff --exit-code -- "${sources[@]}"
git diff --cached --exit-code -- "${sources[@]}"

receipt_dir="verification/parts/p0/local-results/$(git rev-parse HEAD)/$batch"
mkdir -p "$receipt_dir"
git rev-parse HEAD > "$receipt_dir/source-commit.txt"
git status --porcelain > "$receipt_dir/source-status.txt"
sha256sum "${sources[@]}" > "$receipt_dir/source-sha256.txt"
python3 verification/parts/p0/check_sources.py "${production[@]}" "${suppliers[@]}" "$audit" \
  | tee "$receipt_dir/source-guard.json"
if [[ "$batch" = p2-first || "$batch" = p2 ]]; then
  python3 verification/part2/import_paired_v2.py \
    verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
    --check-generated ImbalancedChen/Certificates/PairedV2Data.lean \
    --report "$receipt_dir/decode-report.json" \
    | tee "$receipt_dir/decode.log"
fi
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
objects=()
for module in "${replay[@]}" "${suppliers[@]}"; do
  objects+=(".lake/build/lib/lean/${module//.//}.olean")
done
sha256sum "${objects[@]}" > "$receipt_dir/object-sha256.txt"
for module in "${replay[@]}"; do
  lake env leanchecker --verbose "$module" \
    2>&1 | tee "$receipt_dir/$module.replay.log"
  python3 - "$module" "$receipt_dir/$module.replay.log" <<'PY'
from pathlib import Path
import sys
if f"replaying {sys.argv[1]}" not in Path(sys.argv[2]).read_text().splitlines():
    raise SystemExit(f"Missing bundled kernel replay evidence for {sys.argv[1]}")
PY
done
python3 verification/parts/p0/check_pins.py
sha256sum --check --status "$receipt_dir/source-sha256.txt"
sha256sum --check --status "$receipt_dir/object-sha256.txt"
printf 'Explicit batch passed: %s at %s\n' "$batch" "$(cat "$receipt_dir/source-commit.txt")"
printf 'This receipt does not replace final full-root build and axiom gates.\n'
