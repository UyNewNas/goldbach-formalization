#!/usr/bin/env bash
# TEMPLATE ONLY. Submit in a NEW job after the actual successful stage1 result.
# Same envelope: timeout_seconds=900, memory_mb=13107, cpu_threads=1.
# Root must first preserve the exact get_task JSON at the status path below and
# replace all FILL_* arguments with its actual task id and SHA-bound results.
# Any unfilled argument aborts before canonical reads, directory creation, or release.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
cd /workspace/p2-4-compact-proof-20261125
exec python3 -B /workspace/p24-diagnostic-metadata-retention-20261126/scripts-002/stage2_verify_release.py \
  --stage1-receipt-sha256 FILL_ACTUAL_STAGE1_RECEIPT_SHA256 \
  --stage1-task-id FILL_ACTUAL_SUCCEEDED_STAGE1_TASK_ID \
  --stage1-task-status /workspace/p24-diagnostic-metadata-retention-20261126/attempt-002/stage1-task-status.json \
  --stage1-task-status-sha256 FILL_ACTUAL_GET_TASK_JSON_SHA256 \
  --release-reviewed-thirteen
