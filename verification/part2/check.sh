#!/usr/bin/env bash
# Run from any directory with the repository's unchanged pinned toolchain.
set -euo pipefail

part2_repo="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$part2_repo"

python3 verification/part2/import_paired_v2.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --check-generated ImbalancedChen/Certificates/PairedV2Data.lean

python3 verification/part2/generate_paired_prefix.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --count 4 --check-generated ImbalancedChen/Certificates
python3 verification/part2/round2/upstream/verify_upstream_acceptance.py
python3 verification/part2/generate_paired_prefix.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --start 4 --count 60 --check-generated ImbalancedChen/Certificates
# Receive the unchanged historic gate on its own fixed tree, not against
# the expanded 15-module present snapshot.
p2_historic="$(mktemp -d)"
trap 'rm -rf -- "$p2_historic"' EXIT
git clone --quiet --shared "$part2_repo" "$p2_historic"
git -C "$p2_historic" checkout --quiet --detach e6d6d57323cc358cef060fb243ec386c13cb662d
(cd "$p2_historic" && python3 verification/part2/round3/batch4-to64/verify_acceptance.py)
python3 verification/part2/generate_paired_prefix.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --start 64 --count 64 --check-generated ImbalancedChen/Certificates
python3 verification/part2/round4/batch64-to128/verify_preflight.py

modules=(
  ImbalancedChen.Certificates.PairedFibreIntegral
  ImbalancedChen.Certificates.RationalLogCertificate
  ImbalancedChen.Certificates.PairedCertificateChecker
  ImbalancedChen.Certificates.PairedV2Data
  ImbalancedChen.Certificates.PairedV2
  ImbalancedChen.Certificates.AboveMuSecondCoarse
  ImbalancedChen.Certificates.PairedV2Geometry
  ImbalancedChen.Certificates.PairedV2Prefix4Data
  ImbalancedChen.Certificates.PairedV2Prefix4
  ImbalancedChen.Certificates.PairedV2Batch4To64Data
  ImbalancedChen.Certificates.PairedV2Batch4To64
  ImbalancedChen.Certificates.PairedV2Prefix64
  ImbalancedChen.Certificates.PairedV2Batch64To128Data
  ImbalancedChen.Certificates.PairedV2Batch64To128
  ImbalancedChen.Certificates.PairedV2Prefix128
)

for module in "${modules[@]}"; do
  lake build "$module"
done
for module in "${modules[@]}"; do
  lake env lean -DwarningAsError=true "${module//.//}.lean"
done
for module in "${modules[@]}"; do
  lake env leanchecker --verbose "$module"
done
lake env lean -DwarningAsError=true verification/part2/CertificateAudit.lean
