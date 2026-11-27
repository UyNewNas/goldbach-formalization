#!/bin/sh
set -eu
cd /workspace/scratch/6faf06385519
python -I -B shape_executor_review/readback/shape_readback.py \
  --archive materials/recovery-20261127/shape-completion-v1/shape-evidence.tar.xz \
  --external-success materials/recovery-20261127/shape-completion-v1/EXTERNAL_SUCCESS.json \
  --run-stdout materials/recovery-20261127/shape-completion-v1/RUN_TASK.stdout \
  --recovery materials/recovery-20261127/capture-attempt-v2/RECOVERY_EXPORT.tar.xz \
  --capture-observation materials/recovery-20261127/capture-attempt-v2/EXTERNAL_OBSERVATION.json
