# Follow-up to queued job 572afb7f57df4246b428983dce6188fc.
# Run after its successful replay/audit. This reads the accepted receipts;
# it neither compiles sources nor repeats kernel replay or declaration audits.
# The queued-resume-command.sh file preserves the command actually submitted.
set -euo pipefail
cd /workspace/p2-7-20261125
mapfile -t p27_export_targets < docs/p2/20261125/p27/audit-targets.txt
python3 -B verification/part2/export_winner9_private_evidence.py \
  --output-dir .lake/p2-private/exports/p27-complete-with-adoption-20261125 \
  --split all \
  --transfer-page-bytes 1000000 \
  --driver-file .lake/p27-repro-drivers/driver-v1.py \
  --driver-file .lake/p27-repro-drivers/audit-driver-v2.py \
  --extra-evidence docs/p2/20261125/p27 \
  --extra-evidence .lake/p27-currentchen-adoption/attempt-001 \
  "${p27_export_targets[@]}"
