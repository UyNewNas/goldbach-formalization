#!/usr/bin/env bash
# Run from any directory with the repository's unchanged pinned toolchain.
set -euo pipefail

part2_repo="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$part2_repo"

python3 verification/part2/import_paired_v2.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --check-generated ImbalancedChen/Certificates/PairedV2Data.lean

modules=(
  ImbalancedChen.Certificates.PairedFibreIntegral
  ImbalancedChen.Certificates.RationalLogCertificate
  ImbalancedChen.Certificates.PairedCertificateChecker
  ImbalancedChen.Certificates.PairedV2Data
  ImbalancedChen.Certificates.PairedV2
  ImbalancedChen.Certificates.AboveMuSecondCoarse
)

lake build "${modules[@]}"
for module in "${modules[@]}"; do
  lake env lean -DwarningAsError=true "${module//.//}.lean"
done
for module in "${modules[@]}"; do
  lake env leanchecker --verbose "$module"
done
lake env lean -DwarningAsError=true verification/part2/CertificateAudit.lean
